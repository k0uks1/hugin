#!/usr/bin/env python3
"""mdBook preprocessor: the error index of the reference, made from docs/errors/<code>.md.

mdBook runs it on every build (see book.toml). It adds one page per code, errors/<code>.html, under
the chapter errors/index.md, appends a table of all codes to that chapter, and links plain mentions of
other codes (`E0002 (...)` in "Related") to their pages. Nothing is written to disk, so the index is
always up to date with docs/errors. See reference/README.md.

The protocol: `error-index.py supports <renderer>` exits 0 (every renderer is supported); otherwise
stdin is the JSON array [context, book] and stdout is the processed book.
"""
import json
import re
import sys
from pathlib import Path

INDEX = "errors/index.md"
CODE = re.compile(r"(?<![\w\[])([EW]\d{4})(?![\w\]]|\.md)")
TITLE = re.compile(r"^# ([EW]\d{4}): (.*)$")


def read_codes(errors_dir):
    """(code, title, retired, text) of every docs/errors/<code>.md, sorted by code."""
    codes = []
    for path in sorted(errors_dir.glob("*.md")):
        text = path.read_text(encoding="utf-8")
        first = text.splitlines()[0] if text else ""
        match = TITLE.match(first)
        if not match or match.group(1) != path.stem:
            sys.exit(f"error-index: {path} must start with `# {path.stem}: <title>`")
        retired = "\n**Retired**" in text
        codes.append((path.stem, match.group(2), retired, text))
    if not codes:
        sys.exit(f"error-index: no explanations in {errors_dir}")
    return codes


def link_codes(text, known):
    """Links mentions of known codes outside code blocks, inline code and the title line."""
    out, fenced = [], False
    for i, line in enumerate(text.split("\n")):
        if line.startswith("```"):
            fenced = not fenced
        if fenced or line.startswith("```") or i == 0:
            out.append(line)
            continue
        parts = line.split("`")
        for j in range(0, len(parts), 2):  # even parts are outside inline code
            parts[j] = CODE.sub(lambda m: f"[{m[1]}]({m[1]}.md)" if m[1] in known else m[0], parts[j])
        out.append("`".join(parts))
    return "\n".join(out)


def table(codes):
    rows = [f"| [{c}]({c}.md) | {t}{' (retired)' if r else ''} |" for c, t, r, _ in codes]
    return "\n".join(["", "| Code | Title |", "|---|---|", *rows, ""])


def find_index(items):
    for item in items:
        chapter = item.get("Chapter") if isinstance(item, dict) else None
        if chapter is None:
            continue
        if chapter.get("path") == INDEX:
            return chapter
        found = find_index(chapter.get("sub_items", []))
        if found:
            return found
    return None


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "supports":
        sys.exit(0)
    context, book = json.load(sys.stdin)
    errors_dir = Path(context["root"]).resolve().parent / "docs" / "errors"
    codes = read_codes(errors_dir)
    known = {c for c, _, _, _ in codes}
    items = book["items"] if "items" in book else book["sections"]  # mdBook 0.5 / 0.4
    index = find_index(items)
    if index is None:
        sys.exit(f"error-index: SUMMARY.md has no chapter {INDEX}")
    index["content"] = index["content"].rstrip("\n") + "\n" + table(codes)
    parents = index.get("parent_names", []) + [index["name"]]
    index["sub_items"] = [
        {
            "Chapter": {
                "name": code,
                "content": link_codes(text, known - {code}),
                "number": None,
                "sub_items": [],
                "path": f"errors/{code}.md",
                "source_path": None,
                "parent_names": parents,
            }
        }
        for code, _, _, text in codes
    ]
    json.dump(book, sys.stdout)


if __name__ == "__main__":
    main()
