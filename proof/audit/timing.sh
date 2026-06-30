#!/usr/bin/env bash
# audit/timing.sh -- parse a `make timing` (TIMED=1) build log.
#
# Usage:
#   timing.sh table    <log> [N]              print the N slowest files (default 10) + total
#   timing.sh baseline <log> <out>             write "<file>.v <seconds>" lines, sorted by path
#   timing.sh compare  <log> <baseline> [mult] print files exceeding <mult>x (default 1.25) their baseline entry
#
# A "timed" line is one Makefile.rocq's TIMED=1 emits per compiled file:
#   <path>.vo (real: S.SS, user: U.UU, sys: Y.YY, mem: M ko)
# The coqdep timing line (.Makefile.rocq.d ...) is not a compiled file and is
# skipped. bash 5 + GNU coreutils/awk only.
set -euo pipefail
export LC_ALL=C

mode="${1:?usage: timing.sh table|baseline|compare LOG ...}"
log="${2:?missing log file}"
[ -f "$log" ] || { echo "timing.sh: no such log: $log" >&2; exit 1; }

# Extract "<path>.v <seconds>" pairs, one per compiled file, in log order.
extract() {
  grep -E '^\S+\.vo \(real: ' "$1" \
    | sed -E 's/^(\S+)\.vo \(real: ([0-9.]+),.*/\1.v \2/'
}

case "$mode" in
  table)
    n="${3:-10}"
    pairs=$(extract "$log")
    if [ -z "$pairs" ]; then
      echo "timing.sh: no timed compile lines in $log (warm tree? re-run after 'make clean')" >&2
      exit 0
    fi
    count=$(printf '%s\n' "$pairs" | wc -l)
    total=$(printf '%s\n' "$pairs" | awk '{sum += $2} END {printf "%.2f", sum + 0}')
    printf '%s\n' "$pairs" | sort -k2,2 -rn | head -n "$n" \
      | awk '{printf "%8.2f  %s\n", $2, $1}'
    printf 'total: %.2fs over %d file(s)\n' "$total" "$count"
    ;;
  baseline)
    out="${3:?missing output path}"
    extract "$log" | sort -k1,1 > "$out"
    ;;
  compare)
    baseline="${3:?missing baseline file}"
    mult="${4:-1.25}"
    [ -f "$baseline" ] || { echo "timing.sh: no such baseline: $baseline" >&2; exit 1; }
    extract "$log" | awk -v mult="$mult" '
      NR == FNR { base[$1] = $2; next }
      ($1 in base) && (base[$1] > 0) && ($2 > base[$1] * mult) {
        printf "%-55s now=%7.2fs  baseline=%7.2fs  (%.2fx)\n", $1, $2, base[$1], $2 / base[$1]
      }
    ' "$baseline" -
    ;;
  *)
    echo "timing.sh: unknown mode '$mode' (expected table|baseline|compare)" >&2
    exit 1
    ;;
esac
