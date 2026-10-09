#!/usr/bin/env bash
# The language reference is the definition of Hugin: a change to the language updates it in the same
# pull request (CONTRIBUTING.md, "Changing the language").
#
# Usage: scripts/check-reference-impact.sh <base-ref> [<head-ref>]
# The pull request description is read from $PR_BODY.
#
# Fails if the diff against <base-ref> touches the code that defines the language (syntax, elaboration,
# object semantics, evaluation, diagnostics codes, the bundled library) but neither `reference/src` nor
# `docs/errors`, unless the description contains a line
#
#   Reference: no change, <reason>
#
# that says why the language is unchanged (a refactoring, a performance change, a fix that makes the
# implementation agree with the reference as written).
set -euo pipefail

base="${1:?usage: check-reference-impact.sh <base-ref>}"
changed="$(git diff --name-only "$base"..."${2:-HEAD}")"

language="$(grep -E '^src/main/scala/hugin/(syntax|core|obj|runtime)/|^src/main/scala/hugin/util/diagnostics/Code\.scala$|^src/main/resources/hugin/stdlib/' <<<"$changed" || true)"
reference="$(grep -E '^reference/src/|^docs/errors/' <<<"$changed" || true)"

if [[ -z "$language" ]]; then
  echo "No language-defining code changed."
  exit 0
fi
if [[ -n "$reference" ]]; then
  echo "Language-defining code and the reference both changed:"
  sed 's/^/  /' <<<"$reference"
  exit 0
fi
if grep -qiE '^[[:space:]]*Reference:[[:space:]]*no change,[[:space:]]*[^[:space:]].{9,}' <<<"${PR_BODY:-}"; then
  echo "Language-defining code changed without a reference change; the description says why:"
  grep -iE '^[[:space:]]*Reference:' <<<"${PR_BODY:-}" | sed 's/^/  /'
  exit 0
fi

cat <<EOF
error: this pull request changes code that defines the language but not the language reference.

Changed language-defining files:
$(sed 's/^/  /' <<<"$language")

A change to the syntax, the typing rules, the semantics, the diagnostics or the bundled library updates
the reference chapter it concerns (reference/src/) or the error explanation (docs/errors/) in the same
pull request. If the language is unchanged (a refactoring, a performance change, a fix that makes the
implementation agree with the reference), say so in the pull request description with a line

  Reference: no change, <reason>
EOF
exit 1
