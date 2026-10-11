#!/usr/bin/env python3
"""mdBook preprocessor: semantic highlighting of the Hugin code blocks, computed by the compiler.

mdBook runs it on every build after error-index.py (see book.toml), so the pages of the error index are
highlighted too. Every fenced block whose info string starts with `hugin` becomes pre-rendered HTML,
`<pre><code class="hugin hljs nohighlight">` with a `<span class="hg-…">` per token, which mdBook passes
through and highlight.js skips (`nohighlight`). The spans come from `hugin highlight`, run once for the
whole book: the language server's semantic tokens, and lexical classes for the rest. hugin.css colours
them. The Markdown sources are unchanged, so the reference tests (which read them) are not affected.
See reference/README.md.

Hovers and definitions (issue #132, docs/design/web-ide.md, section 7): the compiler runs as
`hugin highlight --info`, which adds each block's annotation table. A name becomes
`<span data-i="…">` or, where it has a declaration, `<a data-i="…" href="…" tabindex="-1">`: a use links
to its declaration's `id` in the same block (each block is its own program), a name of the bundled
library to the module's page in the reference, with the anchor that this preprocessor adds to the row of
the page's declaration table that lists the name. `data-i` indexes the page's hover texts, deduplicated
over its blocks and written once as JSON (`<script type="application/json" id="hg-hovers">`) after the
page's text; hugin-info.js shows them. A block with names is one tab stop (`tabindex="0"`). The links
work without JavaScript.

The budget (7.4): the bytes that the hovers, links and anchors add to a page, after gzip, are at most
BUDGET. The preprocessor prints the largest and the median page's figure and fails above it.

The compiler is the staged launcher target/universal/stage/bin/hugin (`sbt stage`); HUGIN overrides it
(relative to the repository root, e.g. HUGIN=bin/hugin, which stages on first use). Without it the
build fails: a book with unhighlighted or differently highlighted code would be wrong without notice.

The protocol: `highlight.py supports <renderer>` exits 0 for html only; otherwise stdin is the JSON
array [context, book] and stdout is the processed book.
"""
import gzip
import html
import json
import os
import posixpath
import re
import statistics
import subprocess
import sys
from pathlib import Path

# a fence at the start of a line, its info string and body (the conventions of CodeBlocks.scala)
FENCE = re.compile(r"^```([^\n]*)\n(.*?)^```[ \t]*$", re.M | re.S)

# the gzip bytes that hovers, links and anchors may add to a page (docs/design/web-ide.md, 7.4);
# HUGIN_INFO_BUDGET overrides it (in bytes), to try the check
BUDGET = int(os.environ.get("HUGIN_INFO_BUDGET", 8 * 1024))
LABEL = "Hugin code, arrow keys move between names"


def is_hugin(info):
    words = [w for w in re.split(r"[,\s]+", info.strip()) if w]
    return bool(words) and words[0] == "hugin"


def uses_prelude(info):
    # `elaborate` blocks of docs/errors are checked without the prelude (ExplanationsSuite)
    return "elaborate" not in re.split(r"[,\s]+", info)


def chapters(items):
    for item in items:
        chapter = item.get("Chapter") if isinstance(item, dict) else None
        if chapter is not None:
            yield chapter
            yield from chapters(chapter.get("sub_items", []))


def compiler(root):
    override = os.environ.get("HUGIN")
    staged = root / "target" / "universal" / "stage" / "bin" / "hugin"
    path = root / override if override else staged  # a relative HUGIN is relative to the repository root
    if not (path.is_file() and os.access(path, os.X_OK)):
        sys.exit(
            f"highlight: no Hugin compiler at {path}. The code blocks are highlighted by the compiler:\n"
            "  run `sbt stage` (or `bin/hugin --help`, which stages it) in the repository root, or set\n"
            "  HUGIN to a `hugin` launcher, then build the book again. See reference/README.md."
        )
    return path


def render(runs):
    out = []
    for text, classes, *_ in runs:
        escaped = html.escape(text, quote=False)
        if classes:
            names = " ".join("hg-" + c for c in classes)
            out.append(f'<span class="{names}">{escaped}</span>')
        else:
            out.append(escaped)
    return '<pre><code class="hugin hljs nohighlight">' + "".join(out) + "</code></pre>"


def module_of(path):
    """The library module whose reference page `path` is (`prelude`, `std/graph`), or None."""
    if path == "prelude.md":
        return "prelude"
    m = re.fullmatch(r"(std/[a-z_]+)\.md", path or "")
    return m.group(1) if m and m.group(1) != "std/index" else None


def anchor_id(name):
    # `%input` -> hg-dir-input, `x'` -> hg-x-p: ids that need no escaping in a URL fragment
    return "hg-" + name.replace("%", "dir-").replace("'", "-p")


def first_cell(row):
    """The first cell of a table row `| … | … |` (a `|` inside a code span does not end it), or None."""
    tick = False
    for k, c in enumerate(row[1:], 1):
        if c == "`":
            tick = not tick
        elif c == "|" and not tick:
            return row[1:k]
    return None


def add_anchors(content):
    """Adds an anchor `<span id="hg-<name>"></span>` to the row of each declaration table that lists a
    name first (the first word of a code span in the row's first cell), outside fences. Returns the new
    content and the anchored names."""
    lines, fenced, seen = content.split("\n"), False, set()
    for k, line in enumerate(lines):
        if line.lstrip().startswith(("```", "~~~")):
            fenced = not fenced
        if fenced or not line.startswith("|") or re.match(r"\|\s*:?-", line):
            continue
        cell = first_cell(line)
        if cell is None:
            continue
        new = []
        for span in re.findall(r"`([^`]+)`", cell):
            m = re.match(r"%?[A-Za-z_][\w']*", span.strip())
            if m and m.group(0) not in seen:
                seen.add(m.group(0))
                new.append(m.group(0))
        if new:
            spans = "".join(f'<span id="{anchor_id(n)}"></span>' for n in new)
            lines[k] = "|" + spans + line[1:]
    return "\n".join(lines), seen


class Page:
    """A page's deduplicated hover texts and its numbered blocks."""

    def __init__(self, path, link):
        self.path, self.link = path, link
        self.hovers, self.index, self.blocks = [], {}, 0

    def hover(self, h):
        key = json.dumps(h, ensure_ascii=False)
        if key not in self.index:
            self.index[key] = len(self.hovers)
            self.hovers.append(h)
        return self.index[key]

    def table(self):
        # read with JSON.parse, never inserted as HTML; `<` escaped so that no `</script>` ends it early
        text = json.dumps(self.hovers, ensure_ascii=False, separators=(",", ":")).replace("<", "\\u003c")
        return f'<script type="application/json" id="hg-hovers">{text}</script>'


def ident(name):
    return re.sub(r"[^\w-]", lambda m: f"_{ord(m.group(0)):x}", name, flags=re.A)


def render_info(result, page):
    """A block with its names as spans and links (docs/design/web-ide.md, 7.2)."""
    runs, names, hovers = result["runs"], result["names"], result["hovers"]
    page.blocks += 1
    number = page.blocks
    starts, at = [], 0
    for run in runs:
        starts.append(at)
        at += len(run[0].encode("utf-16-le")) // 2  # the targets are UTF-16 offsets
    named = [(start, run, names[run[2]]) for start, run in zip(starts, runs) if len(run) > 2]
    declarations = {start: run[0] for start, run, n in named if n["decl"]}
    used = {n["target"] for start, _, n in named if isinstance(n.get("target"), int) and n["target"] != start}
    ids, taken = {}, set()
    for start in sorted(used & declarations.keys()):
        base = f"hg{number}-{ident(declarations[start])}"
        ids[start] = base
        k = 1
        while ids[start] in taken:
            k += 1
            ids[start] = f"{base}-{k}"
        taken.add(ids[start])
    out, active = [], False
    for start, run in zip(starts, runs):
        text, classes = run[0], run[1]
        escaped = html.escape(text, quote=False)
        attrs = f' class="{" ".join("hg-" + c for c in classes)}"' if classes else ""
        if len(run) < 3:
            out.append(f"<span{attrs}>{escaped}</span>" if classes else escaped)
            continue
        n = names[run[2]]
        target, href = n.get("target"), None
        if isinstance(target, int) and target != start and target in ids:
            href = "#" + ids[target]
        elif isinstance(target, list):
            href = page.link(*target)
        if n["hover"] is not None:
            attrs += f' data-i="{page.hover(hovers[n["hover"]])}"'
            active = True
        if href:
            out.append(f'<a{attrs} href="{html.escape(href)}" tabindex="-1">{escaped}</a>')
            active = True
        elif start in ids:
            out.append(f'<span{attrs} id="{ids[start]}">{escaped}</span>')
        else:
            out.append(f"<span{attrs}>{escaped}</span>" if attrs else escaped)
    code = '<code class="hugin hljs nohighlight"'
    if active:
        code += f' data-hg="{number}" tabindex="0" aria-label="{LABEL}"'
    return f"<pre>{code}>" + "".join(out) + "</code></pre>"


def gzipped(text):
    return len(gzip.compress(text.encode("utf-8"), compresslevel=6, mtime=0))


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "supports":
        sys.exit(0 if sys.argv[2:] == ["html"] else 1)
    context, book = json.load(sys.stdin)
    root = Path(context["root"]).resolve().parent
    items = book["items"] if "items" in book else book["sections"]  # mdBook 0.5 / 0.4
    # the anchors of the library modules' pages, added before the blocks are found (they are outside fences)
    original, anchors, pages = {}, {}, {}
    for chapter in chapters(items):
        path = chapter.get("path")
        original[id(chapter)] = chapter.get("content") or ""
        module = module_of(path)
        if module and chapter.get("content"):
            chapter["content"], names = add_anchors(chapter["content"])
            pages[module] = path
            anchors.update({(module, n): anchor_id(n) for n in names})
    blocks = []  # (chapter, match) in order
    for chapter in chapters(items):
        for m in FENCE.finditer(chapter.get("content") or ""):
            if is_hugin(m.group(1)):
                blocks.append((chapter, m))
    snippets = [{"code": m.group(2), "prelude": uses_prelude(m.group(1))} for _, m in blocks]
    hugin = compiler(root)
    done = subprocess.run(
        [str(hugin), "highlight", "--info"],
        input=json.dumps(snippets),
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if done.returncode != 0:
        sys.exit(f"highlight: `{hugin} highlight --info` failed ({done.returncode}):\n{done.stderr}")
    results = json.loads(done.stdout)
    if len(results) != len(snippets):
        sys.exit(f"highlight: {len(snippets)} snippets, but {len(results)} results")
    for (chapter, m), result in zip(blocks, results):
        if "".join(run[0] for run in result["runs"]) != m.group(2):
            sys.exit(f"highlight: the runs of a block in {chapter.get('path')} do not cover its text")

    def linker(path):
        def link(module, name):
            if module not in pages:
                return None
            href = posixpath.relpath(pages[module][: -len(".md")] + ".html", posixpath.dirname(path) or ".")
            return href + ("#" + anchors[(module, name)] if (module, name) in anchors else "")

        return link

    by_chapter = {}
    for (chapter, m), result in zip(blocks, results):
        by_chapter.setdefault(id(chapter), []).append((m, result))
    added = {}  # page -> gzip bytes added over the plain highlighting
    for chapter in chapters(items):
        path = chapter.get("path")
        content, base = chapter.get("content") or "", original[id(chapter)]
        if id(chapter) not in by_chapter and content == base:
            continue
        page = Page(path, linker(path))
        found = by_chapter.get(id(chapter), [])
        rendered = [render_info(result, page) for _, result in found]
        # replace from the end, so that the offsets of earlier matches stay valid
        for (m, _), text in reversed(list(zip(found, rendered))):
            content = content[: m.start()] + text + content[m.end() :]
        if page.hovers:
            content += "\n\n" + page.table() + "\n"
        plain = [m for m in FENCE.finditer(base) if is_hugin(m.group(1))]
        for m, (_, result) in reversed(list(zip(plain, found))):
            base = base[: m.start()] + render(result["runs"]) + base[m.end() :]
        chapter["content"] = content
        added[path] = gzipped(content) - gzipped(base)
    report(added)
    json.dump(book, sys.stdout)


def report(added):
    if not added:
        return
    largest = max(added, key=added.get)
    median = statistics.median(added.values())
    print(
        f"highlight: hovers and links add {added[largest] / 1024:.1f} KB gzip to the largest page ({largest}), "
        f"{median / 1024:.1f} KB to the median of {len(added)} pages; budget {BUDGET / 1024:.1f} KB",
        file=sys.stderr,
    )
    over = {p: n for p, n in added.items() if n > BUDGET}
    if over:
        pages = ", ".join(f"{p} ({n / 1024:.1f} KB)" for p, n in sorted(over.items()))
        sys.exit(
            f"highlight: the hovers and links of {pages} exceed the budget of {BUDGET / 1024:.1f} KB gzip per page "
            "(docs/design/web-ide.md, 7.4)"
        )


if __name__ == "__main__":
    main()
