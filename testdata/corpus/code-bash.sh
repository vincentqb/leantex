#!/usr/bin/env bash
# Rinse the cache
#
# An invented script for the code-file reader's golden fixture. Its leading
# comment block reads as prose above the code.

set -eu

cache="${TMPDIR:-/tmp}/rinse"  # a trailing comment stays in the code
mkdir -p "$cache"
echo "rinsed $cache"
