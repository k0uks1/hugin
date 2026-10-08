#!/usr/bin/env bash
# Fails if the sources cite sections of docs/REDESIGN.md as a specification. The language reference
# (reference/src) is the specification: cite a chapter as `reference: object/termination` (the chapter's
# path in reference/src/SUMMARY.md). Historical mentions without a section sign (`redesign step B3`,
# `redesign question Q1`) are fine. See CONTRIBUTING.md, "Pull requests".
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# `REDESIGN §4.2`, `docs/REDESIGN.md §5.2`, `REDESIGN, §7`, and the form broken across lines (`REDESIGN` at
# the end of a line, the section on the next)
if hits=$(grep -rnE 'REDESIGN(\.md)?,? ?§|REDESIGN(\.md)?[ (,]*$' "$ROOT/src/main"); then
  echo "error: src/main cites sections of docs/REDESIGN.md; cite the language reference instead" >&2
  echo "       (e.g. \`reference: object/termination\`, a chapter path from reference/src/SUMMARY.md):" >&2
  echo "$hits" | sed "s|$ROOT/||" >&2
  exit 1
fi
# every cited chapter exists
status=0
for ch in $(grep -rohE 'reference: [a-z][a-z/-]*[a-z]' "$ROOT/src" "$ROOT/tests" | sed 's/reference: //' | sort -u); do
  if [[ ! -f "$ROOT/reference/src/$ch.md" ]]; then
    echo "error: \`reference: $ch\` cites a chapter that does not exist (reference/src/$ch.md)" >&2
    status=1
  fi
done
[[ $status == 0 ]] && echo "check-refs: src/main cites no REDESIGN.md sections; every cited chapter exists"
exit $status
