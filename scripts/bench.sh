#!/usr/bin/env bash
# Benchmark leantex against lualatex on the bench corpus.
# Reference point, not a fair fight: lualatex loads formats and fonts per run,
# and does far more. Median of N runs, milliseconds.
set -euo pipefail
cd "$(dirname "$0")/.."
N=${N:-5}
LEANTEX=.lake/build/bin/leantex

./scripts/gen-lorem.sh >/dev/null

run_ms() { # cmd...
  local t0 t1
  t0=$(date +%s%N)
  if ! "$@" >/dev/null 2>&1; then
    echo "benchmark command failed: $*" >&2
    return 1
  fi
  t1=$(date +%s%N)
  echo $(( (t1 - t0) / 1000000 ))
}

median() {
  printf '%s\n' "$@" | sort -n | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}'
}

bench() { # label cmd...
  local label=$1; shift
  local times=()
  for _ in $(seq 1 "$N"); do
    times+=("$(run_ms "$@")")
  done
  printf '%-42s %6s ms (median of %d)\n' "$label" "$(median "${times[@]}")" "$N"
}

for doc in tests/corpus/paragraphs.tex bench/lorem.tex; do
  base=$(basename "$doc")
  bench "leantex  $base" "$LEANTEX" -q build "$doc"
  if command -v lualatex >/dev/null; then
    workdir=$(mktemp -d)
    cp "$doc" "$workdir/"
    bench "lualatex $base" lualatex --interaction=batchmode \
      --output-directory="$workdir" "$workdir/$base"
    rm -r "$workdir"
  fi
done
