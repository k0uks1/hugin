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
# the language server answers `initialize` and exits with 0 after `shutdown` and `exit`
lsp() { printf 'Content-Length: %d\r\n\r\n%s' "${#1}" "$1"; }
reply=$({ lsp '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}'
          lsp '{"jsonrpc":"2.0","id":2,"method":"shutdown"}'
          lsp '{"jsonrpc":"2.0","method":"exit"}'; } | "$HUGIN" lsp)
if [[ "$reply" != *'"hoverProvider":true'* ]]; then
  echo "FAILED: hugin lsp did not answer initialize" >&2
  status=1
fi
exit $status
