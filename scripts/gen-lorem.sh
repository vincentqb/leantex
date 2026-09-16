#!/usr/bin/env bash
# Regenerates bench/lorem.tex: a deterministic, lualatex-compatible document
# of justified prose, large enough to make timing differences visible.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p bench
{
  echo '\documentclass{article}'
  echo '\begin{document}'
  echo
  words=(typesetting algorithm paragraph internationalization demonstration
    hyphenation measurement considerable arrangement optimization
    representation understanding development infrastructure characteristic
    responsibility configuration transformation implementation documentation)
  for p in $(seq 1 150); do
    line=""
    for s in $(seq 1 60); do
      w=${words[$(( (p * 7 + s * 13) % 20 ))]}
      line="$line $w"
    done
    echo "The quick brown fox says:$line again and again."
    echo
  done
  echo '\end{document}'
} > bench/lorem.tex
wc -c bench/lorem.tex
