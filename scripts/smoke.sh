#!/usr/bin/env bash
# Runs every example through the CLI and checks the exit codes. Used by CI after `sbt test`.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HUGIN="$ROOT/bin/hugin"
status=0
for f in "$ROOT"/examples/*.hgn; do
  args=()
  facts="${f%.hgn}.facts"
  [[ -f "$facts" ]] && args+=(--facts "$facts")
  echo "== $(basename "$f")"
  if ! "$HUGIN" run --no-color "$f" "${args[@]}"; then
    echo "FAILED: $f" >&2
    status=1
  fi
done
"$HUGIN" phases > /dev/null
"$HUGIN" explain E0401 > /dev/null
exit $status
