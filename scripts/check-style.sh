#!/usr/bin/env bash
# Fails if the language reference (reference/src) or the error explanations (docs/errors) contain words
# and phrases that reference/STYLE.md rules out (issue #63): filler, marketing words, hedges where a rule
# is exact, em-dashes, rhetorical questions, and terms that the glossary of reference/src/notation.md
# retires. Code blocks and inline code are not checked. The list holds only phrases that are wrong in
# this text wherever they occur; style that needs judgement is left to review (STYLE.md, section 8).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 -I - "$ROOT" <<'PY'
import re, sys
from pathlib import Path

root = Path(sys.argv[1])

# (pattern, advice); matched case-insensitively against prose with code removed
PHRASES = [
    # openers, closers and filler
    (r"\blet(['’]s| us)\b", "state the rule; the reference does not address the reader as 'us'"),
    (r"\bin this (section|chapter) we\b", "say what the section defines, without 'we'"),
    (r"\b(in summary|to summari[sz]e|in conclusion)\b", "a section does not end with a summary"),
    (r"\b(it'?s|it is) worth (noting|mentioning)\b", "state the fact, or use a Note block"),
    (r"\bnote that\b", "state the fact, or use a Note block"),
    (r"\b(importantly|crucially|needless to say|of course)\b", "drop the filler"),
    (r"\bhere(?: is|'s) an example\b", "say what the example demonstrates"),
    # contrast frames
    (r"\b(it'?s|is|isn'?t) not (just|merely|only) .{0,40}[,;] (it'?s|but)\b", "state what Hugin does"),
    (r"\bnot merely\b", "state what Hugin does"),
    # marketing words
    (r"\b(seamless(ly)?|powerful|robust(ly)?|elegant(ly)?|effortless(ly)?|leverag(e|es|ed|ing)|"
     r"empower(s|ed|ing)?|unlock(s|ed|ing)?|cutting-edge|best-in-class|state-of-the-art|"
     r"game-chang\w*|delv(e|es|ing)|full power)\b", "describe what the construct does"),
    # hedges where a rule is exact
    (r"\b(generally|typically|usually|basically|in most cases)\b",
     "state the rule exactly, and its exceptions"),
    # punctuation
    (r"—", "use a comma, colon or parentheses, or two sentences (no em-dash)"),
    (r"\?\s*$", "no rhetorical questions"),
]

# terms the glossary of notation.md retires; not checked in notation.md (which lists them) and in the
# explanations of retired codes (which describe the language before the redesign)
RETIRED = [
    (r"\b(fact|data)[ -]constructors?\b", "say 'constructor': every constructor builds facts"),
    (r"\bsubfacts?\b", "say 'nested fact'"),
    (r"\bskolem terms?\b", "say 'constructor term'"),
    (r"\binductive types?\b", "say 'inductive family'"),
]


def prose(text):
    """The lines of a Markdown text with fenced code blocks, inline code and link targets blanked."""
    out, fenced = [], False
    for line in text.split("\n"):
        if line.lstrip().startswith("```"):
            fenced = not fenced
            out.append("")
            continue
        if fenced:
            out.append("")
            continue
        line = re.sub(r"`[^`]*`", "C", line)
        line = re.sub(r"\]\([^)]*\)", "]", line)
        line = re.sub(r"<[^>]+>", "", line)
        out.append(line)
    return out


files = sorted((root / "reference" / "src").rglob("*.md")) + sorted((root / "docs" / "errors").glob("*.md"))
problems = 0
for path in files:
    text = path.read_text(encoding="utf-8")
    rules = list(PHRASES)
    if path.name != "notation.md" and "\n**Retired**" not in text:
        rules += RETIRED
    for number, line in enumerate(prose(text), 1):
        for pattern, advice in rules:
            m = re.search(pattern, line, re.IGNORECASE)
            if m:
                problems += 1
                print(f"{path.relative_to(root)}:{number}: '{m.group(0)}': {advice}", file=sys.stderr)
if problems:
    print(f"check-style: {problems} problem(s); see reference/STYLE.md, section 6", file=sys.stderr)
    sys.exit(1)
print(f"check-style: {len(files)} pages follow the word list of reference/STYLE.md")
PY
