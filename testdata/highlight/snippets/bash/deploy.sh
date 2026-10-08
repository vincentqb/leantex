#!/usr/bin/env bash
# Rebuild an invented site and publish it.
set -euo pipefail

SITE_DIR="${SITE_DIR:-$HOME/site}"
count=0
readonly stamp=$(date +%Y%m%d)

build() {
  local target="$1"
  echo "building ${target} into $SITE_DIR" >&2
  for page in pages/*.md; do
    if [[ -f "$page" && ! -L "$page" ]]; then
      count=$((count + 1))
      pandoc "$page" -o "${SITE_DIR}/$(basename "${page%.md}").html"
    elif [ -d "$page" ]; then
      continue
    else
      printf 'skipping %s\n' "$page"
    fi
  done
}

case "${1:-all}" in
  all|full) build all ;;
  quick) build quick && echo done ;;
  *) echo "unknown target: $1"; exit 2 ;;
esac

cat <<EOF > "$SITE_DIR/VERSION"
built $stamp with $count pages
EOF

total=$(( 16#ff + 2#101 ))
echo $'tab:\there' 'single $quoted' "mixed \"escapes\" \$5" `whoami`
