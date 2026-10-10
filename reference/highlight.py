#!/usr/bin/env python3
"""mdBook preprocessor: semantic highlighting of the Hugin code blocks, computed by the compiler.

mdBook runs it on every build after error-index.py (see book.toml), so the pages of the error index are
highlighted too. Every fenced block whose info string starts with `hugin` becomes pre-rendered HTML,
`<pre><code class="hugin hljs nohighlight">` with a `<span class="hg-…">` per token, which mdBook passes
through and highlight.js skips (`nohighlight`). The spans come from `hugin highlight`, run once for the
whole book: the language server's semantic tokens, and lexical classes for the rest. hugin.css colours
them. The Markdown sources are unchanged, so the reference tests (which read them) are not affected.
See reference/README.md.

The compiler is the staged launcher target/universal/stage/bin/hugin (`sbt stage`); HUGIN overrides it
(relative to the repository root, e.g. HUGIN=bin/hugin, which stages on first use). Without it the
build fails: a book with unhighlighted or differently highlighted code would be wrong without notice.

The protocol: `highlight.py supports <renderer>` exits 0 for html only; otherwise stdin is the JSON
array [context, book] and stdout is the processed book.
"""
import html
import json
import os
import re
import subprocess
import sys
from pathlib import Path

# a fence at the start of a line, its info string and body (the conventions of CodeBlocks.scala)
FENCE = re.compile(r"^```([^\n]*)\n(.*?)^```[ \t]*$", re.M | re.S)


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
    for text, classes in runs:
        escaped = html.escape(text, quote=False)
        if classes:
            names = " ".join("hg-" + c for c in classes)
            out.append(f'<span class="{names}">{escaped}</span>')
        else:
            out.append(escaped)
    return '<pre><code class="hugin hljs nohighlight">' + "".join(out) + "</code></pre>"


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "supports":
        sys.exit(0 if sys.argv[2:] == ["html"] else 1)
    context, book = json.load(sys.stdin)
    root = Path(context["root"]).resolve().parent
    items = book["items"] if "items" in book else book["sections"]  # mdBook 0.5 / 0.4
    blocks = []  # (chapter, match) in order
    for chapter in chapters(items):
        for m in FENCE.finditer(chapter.get("content") or ""):
            if is_hugin(m.group(1)):
                blocks.append((chapter, m))
    snippets = [{"code": m.group(2), "prelude": uses_prelude(m.group(1))} for _, m in blocks]
    hugin = compiler(root)
    done = subprocess.run(
        [str(hugin), "highlight"],
        input=json.dumps(snippets),
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if done.returncode != 0:
        sys.exit(f"highlight: `{hugin} highlight` failed ({done.returncode}):\n{done.stderr}")
    results = json.loads(done.stdout)
    if len(results) != len(snippets):
        sys.exit(f"highlight: {len(snippets)} snippets, but {len(results)} results")
    for (chapter, m), runs in zip(blocks, results):
        if "".join(text for text, _ in runs) != m.group(2):
            sys.exit(f"highlight: the runs of a block in {chapter.get('path')} do not cover its text")
    # replace from the end, so that the offsets of earlier matches stay valid
    for (chapter, m), runs in reversed(list(zip(blocks, results))):
        content = chapter["content"]
        chapter["content"] = content[: m.start()] + render(runs) + content[m.end() :]
    json.dump(book, sys.stdout)


if __name__ == "__main__":
    main()
