#!/usr/bin/env bash
# Cold end-to-end benchmark (docs/PERFORMANCE.md): every program of the bench set is run with the staged
# launcher in a new JVM, RUNS times (default 5); prints the median wall time per program.
#
#   bench/cold.sh [launcher]        # default: target/universal/stage/bin/hugin (run `sbt stage` first)
#
# The bench set is listed by `hugin.bench.BenchSet` (src/test/scala/hugin/bench/Bench.scala); this script
# keeps its own copy of the list so that it runs without sbt.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
HUGIN="${1:-target/universal/stage/bin/hugin}"
RUNS="${RUNS:-5}"

programs=(
  "check one-line|check bench/small/one.hgn"
  "run a01_transitive_closure|run tests/run/a01_transitive_closure.hgn --facts tests/run/a01_transitive_closure.facts"
  "run a05_stratified|run tests/run/a05_stratified.hgn"
  "run c1_aggregates|run tests/run/c1_aggregates.hgn"
  "run a04_typechecker|run tests/run/a04_typechecker.hgn --facts tests/run/a04_typechecker.facts"
  "run a10_meta_applicative|run tests/run/a10_meta_applicative.hgn"
  "run f_modules|run tests/run/f_modules.hgn"
  "run c1_roundtrip|run tests/run/c1_roundtrip.hgn"
  "run c2_module_wide|run tests/run/c2_module_wide.hgn"
  "run meta_scaled|run bench/meta/meta_scaled.hgn"
  "run nat_literals|run bench/meta/nat_literals.hgn"
  "run tc_chain|run bench/datalog/tc.hgn --facts bench/datalog/tc.facts"
  "run shortest_grid|run bench/datalog/sp.hgn --facts bench/datalog/sp.facts"
  "run strata|run bench/datalog/strata.hgn --facts bench/datalog/strata.facts"
  "check gen_large|check bench/gen/large.hgn"
  "run gen_large|run bench/gen/large.hgn --facts bench/gen/large.facts"
)

median() { sort -n | awk '{a[NR]=$1} END {print (NR % 2) ? a[(NR+1)/2] : int((a[NR/2]+a[NR/2+1])/2)}'; }

for entry in "${programs[@]}"; do
  name="${entry%%|*}"
  read -r -a args <<< "${entry#*|}"
  times=()
  for _ in $(seq "$RUNS"); do
    start=$(date +%s%N)
    "$HUGIN" "${args[@]}" --no-color > /dev/null 2>&1 || true
    end=$(date +%s%N)
    times+=($(( (end - start) / 1000000 )))
  done
  printf '%-32s median %6d ms   (%s)\n' "$name" "$(printf '%s\n' "${times[@]}" | median)" "${times[*]}"
done
