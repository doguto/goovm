#!/bin/bash
# Profiles goosecc with perf on one file:
#   tests/profile.sh [-E|-fsyntax-only] file.c [flags...]
# Builds a -g copy of goosecc in $PROF (default /tmp/goosecc-prof).
set -e
HERE="$(cd "$(dirname "$0")/.." && pwd)"
PROF="${PROF:-/tmp/goosecc-prof}"
PERF="${PERF:-/usr/lib/linux-tools-6.8.0-31/perf}"
MODE="$1"; shift
CFLAGS="-O2 -g" "$HERE/build.sh" "$PROF" > /dev/null 2>&1
"$PERF" record -q -o "$PROF/perf.data" -F 20000 -g "$PROF/goosecc" "$MODE" "$@" -o /dev/null > /dev/null 2>&1 || true
"$PERF" report -i "$PROF/perf.data" --no-children --percent-limit 1 --stdio 2>/dev/null | grep -E "^ +[0-9.]+%" | head -40
