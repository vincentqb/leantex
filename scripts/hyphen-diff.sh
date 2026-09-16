#!/usr/bin/env bash
# Differential test: leantex hyphenation vs real TeX on a word list.
#
# The oracle is luatex loading THE SAME pattern set the engine embeds
# (hyph-en-us.tex / ushyphmax), with matching hyphenmins. Note that plain
# `lualatex` would be the wrong oracle: TeX Live's language.dat maps the
# `english` language to hyphen.tex (Knuth's frozen set), a strict subset, so
# it legitimately reports fewer break candidates.
#
# \showhyphens lists every admissible break, not one chosen rendering.
#
# usage: ./scripts/hyphen-diff.sh [wordlist]
set -euo pipefail
cd "$(dirname "$0")/.."

command -v luatex >/dev/null || { echo "luatex not found" >&2; exit 2; }
[[ -x .lake/build/bin/leantex ]] || { echo "run: lake build" >&2; exit 2; }

words_file=${1:-}
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT

if [[ -z "$words_file" ]]; then
  words_file="$work/words.txt"
  cat tests/corpus/*.tex PLAN.md AGENTS.md 2>/dev/null \
    | tr -c 'A-Za-z' '\n' | grep -E '^[a-z]{6,}$' | LC_ALL=C sort -u > "$words_file"
fi

{
  echo '\newlanguage\probelang'
  echo '\language=\probelang'
  echo '\lefthyphenmin=2 \righthyphenmin=3'
  echo '\input hyph-en-us'
  while read -r w; do
    echo "\\showhyphens{$w}"
  done < "$words_file"
  echo '\end'
} > "$work/oracle.tex"

(cd "$work" && luatex --interaction=batchmode oracle.tex >/dev/null 2>&1) || true

grep -o '\\tenrm .*' "$work/oracle.log" | sed 's|^\\tenrm ||' | tr -d ' ' \
  > "$work/oracle.txt"

.lake/build/bin/leantex hyphenate --file "$words_file" > "$work/ours.txt"

total=$(wc -l < "$words_file")
oracle_lines=$(wc -l < "$work/oracle.txt")
if [[ "$oracle_lines" -ne "$total" ]]; then
  echo "oracle produced $oracle_lines lines for $total words; cannot compare" >&2
  exit 2
fi

paste -d'\t' "$words_file" "$work/oracle.txt" "$work/ours.txt" > "$work/joined.tsv"
mismatches=$(awk -F'\t' '$2 != $3 {print "  " $1 ": tex " $2 " | leantex " $3}' \
  "$work/joined.tsv")

if [[ -n "$mismatches" ]]; then
  echo "mismatches:"
  echo "$mismatches"
  echo "hyphen-diff: $(echo "$mismatches" | wc -l)/$total words disagree"
  exit 1
fi

echo "hyphen-diff: $total words, leantex matches TeX exactly"
