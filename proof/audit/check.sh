#!/usr/bin/env bash
# audit/check.sh -- the mechanical audit gate for the secp256k1 Rocq/VST proof
# tree.  Read-only: it never compiles anything and never writes .vo files.
#
# Usage: check.sh [gate...]      (default: all)
#   gate in {0 0b 1 2 3 4 5} or "all"
#
# Env:
#   PROOF_DIR         override the resolved proof root (for testing against
#                     a scratch fixture tree); default is this script's
#                     grandparent directory.
#                     on once the F0 goal-selector cleanup lands).
#
# Gates:
#   0  FRESH      every _RocqProject .v has a fresh .vo, no orphan .vo under
#                 the layer dirs, every layer .v is tracked in _RocqProject.
#   0b AST        clight/extraction.v matches the pinned audit/extraction.sha256.
#   1  GAPS       no Admitted./admit./give_up. in the proof layers.
#   2  AXIOMS-SRC Axiom/Parameter/Hypothesis/Conjecture declarations confined
#                 to the two files on the trust base.
#   3  PIN        audit/statement.v (if present) has a fresh .vo; SKIP if
#                 the file does not exist yet.
#   4  CONE       audit/assumptions.log's Print-Assumptions closure stays
#                 inside audit/AXIOM_WHITELIST (the former check-axioms.sh).
#   5  STYLE      banned tactics, do-N-forward, inline Opaque/Transparent +
#                 bracket-match-goal anti-patterns, ASCII-only, SPDX headers,
#                 the verif/ gprog import, doc path references, and the
#                 tactics/ layering rule -- 9 lettered sub-checks (5a, 5b,
#                 5c, 5c2, 5d, 5e, 5f, 5g, 5h).
#
# Each gate prints exactly one summary line:
#   GATE <n> <NAME>: OK -- ...
#   GATE <n> <NAME>: FAIL -- ...
# followed by up to ~20 indented offending lines (then "...").  Gates keep
# running after a failure; the script exits non-zero iff any selected gate
# failed (gate 3's SKIP does not count as a failure).
set -uo pipefail

# ---------------------------------------------------------------------------
# Resolve the proof root from this script's own path, so it runs correctly
# regardless of the caller's cwd.  PROOF_DIR is overridable for testing
# against a scratch fixture tree.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
PROOF_DIR="${PROOF_DIR:-$(dirname "$SCRIPT_DIR")}"
cd "$PROOF_DIR" || { echo "check.sh: cannot cd to PROOF_DIR=$PROOF_DIR" >&2; exit 2; }

LAYER_DIRS="vst theory model contract tactics verif"
MAX_LINES=20

# ---------------------------------------------------------------------------
# Helpers

# Print up to MAX_LINES lines from stdin, indented, then an elision marker.
print_capped() {
  local n=0
  local line
  while IFS= read -r line; do
    n=$((n + 1))
    if [ "$n" -le "$MAX_LINES" ]; then
      printf '    %s\n' "$line"
    fi
  done
  if [ "$n" -gt "$MAX_LINES" ]; then
    printf '    ... (%d more)\n' "$((n - MAX_LINES))"
  fi
}

# ---------------------------------------------------------------------------
# GATE 0 -- FRESH

gate_0_fresh() {
  local name="GATE 0 FRESH"
  local -a problems=()
  local v vo f listed

  # (i) every .v listed in _RocqProject has a .vo whose mtime >= the .v's.
  while IFS= read -r v; do
    [ -n "$v" ] || continue
    vo="${v%.v}.vo"
    if [ ! -e "$vo" ]; then
      problems+=("(i)   $v -- no .vo (never compiled)")
    elif [ "$v" -nt "$vo" ]; then
      problems+=("(i)   $v -- newer than $vo (stale build)")
    fi
  done < <(grep -E '^\S+\.v$' _RocqProject)

  # (ii) no .vo under the layer dirs/audit/clight lacks a sibling .v.
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    v="${f%.vo}.v"
    [ -e "$v" ] || problems+=("(ii)  $f -- orphan .vo, no sibling .v")
  done < <(find $LAYER_DIRS audit clight -name '*.vo' 2>/dev/null | sort)

  # (iii) every .v under the layer dirs + clight is listed in _RocqProject,
  # or is one of the standalone exceptions.
  listed=$(grep -E '^\S+\.v$' _RocqProject | sort -u)
  while IFS= read -r v; do
    [ -n "$v" ] || continue
    case "$v" in
      audit/assumptions.v | audit/statement.v | secp256k1_fv.v) continue ;;
    esac
    if ! grep -qxF "$v" <<<"$listed"; then
      problems+=("(iii) $v -- not listed in _RocqProject")
    fi
  done < <(find $LAYER_DIRS clight -name '*.v' 2>/dev/null | sort)

  if [ "${#problems[@]}" -eq 0 ]; then
    echo "$name: OK -- all tracked .v compiled+fresh, no orphan .vo, no untracked .v"
    return 0
  fi
  echo "$name: FAIL -- ${#problems[@]} freshness/tracking problem(s):"
  printf '%s\n' "${problems[@]}" | print_capped
  return 1
}

# ---------------------------------------------------------------------------
# GATE 0b -- AST pin

gate_0b_ast() {
  local name="GATE 0b AST"
  local ast="clight/extraction.v"
  local pin="audit/extraction.sha256"

  if [ ! -e "$ast" ]; then
    echo "$name: FAIL -- $ast is missing (run: make extract)"
    return 1
  fi
  if [ ! -e "$pin" ]; then
    echo "$name: FAIL -- $pin is missing (no AST pin recorded yet)"
    return 1
  fi

  local out
  if out=$(sha256sum -c "$pin" 2>&1); then
    echo "$name: OK -- $ast matches the pinned hash in $pin"
    return 0
  fi
  echo "$name: FAIL -- the extraction AST changed since it was pinned;" \
    "re-review clight/extraction.v before updating $pin:"
  printf '%s\n' "$out" | print_capped
  return 1
}

# ---------------------------------------------------------------------------
# GATE 1 -- proof GAPS

gate_1_gaps() {
  local name="GATE 1 GAPS"
  local hits

  hits=$(grep -rnE '\b(Admitted|admit|give_up)\.' $LAYER_DIRS 2>/dev/null)

  if [ -z "$hits" ]; then
    echo "$name: OK -- no proof gaps"
    return 0
  fi
  echo "$name: FAIL -- proof gap(s):"
  printf '%s\n' "$hits" | print_capped
  return 1
}

# ---------------------------------------------------------------------------
# GATE 2 -- AXIOMS-SRC

gate_2_axioms_src() {
  local name="GATE 2 AXIOMS-SRC"
  local -a allowed=(
    "theory/modinv/divsteps/bound724.v"
    "theory/modinv/divsteps/bound590.v"
  )
  local hits line f ok a
  local -a bad=()

  hits=$(grep -rnE '^\s*(Axiom|Axioms|Parameter|Parameters|Hypothesis|Hypotheses|Conjecture)\b' $LAYER_DIRS 2>/dev/null)
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    f="${line%%:*}"
    ok=0
    for a in "${allowed[@]}"; do
      [ "$f" = "$a" ] && ok=1 && break
    done
    [ "$ok" -eq 0 ] && bad+=("$line")
  done <<<"$hits"

  if [ "${#bad[@]}" -eq 0 ]; then
    echo "$name: OK -- Axiom/Parameter/Hypothesis/Conjecture confined to the 2 declared files"
    return 0
  fi
  echo "$name: FAIL -- assumption declared outside {${allowed[*]}}:"
  printf '%s\n' "${bad[@]}" | print_capped
  return 1
}

# ---------------------------------------------------------------------------
# GATE 3 -- PIN (headline theorem pin; SKIP until audit/statement.v exists)

gate_3_pin() {
  local name="GATE 3 PIN"
  local stmt="audit/statement.v"
  local vo="audit/statement.vo"

  if [ ! -e "$stmt" ]; then
    echo "$name: SKIP -- audit/statement.v not present yet"
    return 0
  fi
  if [ ! -e "$vo" ]; then
    echo "$name: FAIL -- $vo missing (run: make audit)"
    return 1
  fi
  if [ "$stmt" -nt "$vo" ]; then
    echo "$name: FAIL -- $stmt is newer than $vo (stale compile)"
    return 1
  fi
  echo "$name: OK -- $vo present and newer than $stmt"
  return 0
}

# ---------------------------------------------------------------------------
# GATE 4 -- CONE (assumption cone vs whitelist; the former check-axioms.sh)

gate_4_cone() {
  local name="GATE 4 CONE"
  local log="audit/assumptions.log"
  local wl="audit/AXIOM_WHITELIST"

  if [ ! -e "$log" ]; then
    echo "$name: FAIL -- $log not present (run: make axioms, or make audit)"
    return 1
  fi
  if [ ! -e "$wl" ]; then
    echo "$name: FAIL -- $wl not present"
    return 1
  fi

  # A failed trust-base compile must fail the gate (else "no axioms" reads as pass).
  if grep -qE '^(Error|Toplevel input|Syntax error|Anomaly)' "$log"; then
    echo "$name: FAIL -- trust-base compile reported an error:"
    grep -nE '^(Error|Toplevel input|Syntax error|Anomaly)' "$log" | print_capped
    return 1
  fi

  # Distinct axiom names: Print Assumptions prints each as a column-0
  # "qualified.name : type" entry (type may wrap onto indented continuation lines).
  local found allow unexpected n
  found=$(grep -E '^[^[:space:]]+ :' "$log" | sed -E 's/ :.*$//' | sort -u)
  # Allowed names: first token of each non-comment, non-blank whitelist line.
  allow=$(sed -E 's/#.*$//' "$wl" | awk 'NF{print $1}' | sort -u)

  if [ -z "$found" ]; then
    echo "$name: FAIL -- no assumptions parsed from $log (unexpected)."
    return 1
  fi

  unexpected=$(comm -23 <(printf '%s\n' "$found") <(printf '%s\n' "$allow"))

  if [ -n "$unexpected" ]; then
    echo "$name: FAIL -- assumption(s) not in $wl:"
    printf '%s\n' "$unexpected" | print_capped
    echo "    If intended, add to $wl (with justification); otherwise an axiom crept in."
    return 1
  fi

  n=$(printf '%s\n' "$found" | grep -c .)
  echo "$name: OK -- $n distinct assumption(s), all whitelisted."
  print_trust_surface_table "$found" "$wl"
  return 0
}

# For each whitelisted name that actually appears in the log: its group
# ("foundational" / "project", from which "# ---" section of the whitelist
# it sits under) and the first line of the comment block directly above it.
print_trust_surface_table() {
  local found="$1"
  local wl="$2"
  local map
  map=$(awk '
    /^# ---/ {
      line = $0
      sub(/^# *--- */, "", line)
      split(line, w, / *[ (]/)
      group = tolower(w[1])
      prevcomment = 0
      next
    }
    /^#/ {
      txt = $0
      sub(/^# ?/, "", txt)
      if (!prevcomment) block = txt
      prevcomment = 1
      next
    }
    /^[ \t]*$/ { prevcomment = 0; next }
    {
      print $1 "\t" group "\t" block
      prevcomment = 0
    }
  ' "$wl")

  echo
  echo "Trust surface:"
  {
    printf 'name\tgroup\tjustification\n'
    while IFS= read -r name; do
      [ -n "$name" ] || continue
      grep -F -m1 "$(printf '%s\t' "$name")" <<<"$map"
    done <<<"$found"
  } | column -t -s $'\t' | sed 's/^/    /'
}

# ---------------------------------------------------------------------------
# GATE 5 -- STYLE (9 lettered sub-checks: 5a, 5b, 5c, 5c2, 5d, 5e, 5f, 5g, 5h)

check_5a_banned_tactics() {
  local pattern='\b(progressC|convert_C_to_math|solve_bounds|solve_bounds_body|unfold_C|clear_mod|fastforward|forward_verify_check)\b'
  local hits
  hits=$(grep -rnE "$pattern" verif contract tactics 2>/dev/null)
  if [ -z "$hits" ]; then
    echo "  5a banned-tactics: OK -- no banned Ltac name in verif/ contract/ tactics/"
    return 0
  fi
  echo "  5a banned-tactics: FAIL -- banned Ltac name(s) in verif/ contract/ tactics/:"
  printf '%s\n' "$hits" | print_capped
  return 1
}

check_5b_do_n_forward() {
  local hits
  hits=$(grep -rnE '\bdo [0-9]+ \(?(forward|forward_call|progressC)\b' verif 2>/dev/null)
  if [ -z "$hits" ]; then
    echo "  5b do-N-forward: OK -- no repeated-forward idiom in verif/"
    return 0
  fi
  echo "  5b do-N-forward: FAIL -- repeated-forward idiom(s) in verif/:"
  printf '%s\n' "$hits" | print_capped
  return 1
}

check_5c_anti_patterns() {
  local hits
  hits=$(
    {
      grep -rnE '^\s*(Opaque|Transparent)\b' verif 2>/dev/null
      grep -rnE 'match goal with\s*\[\s*H' verif 2>/dev/null
    } | sort -u
  )
  if [ -z "$hits" ]; then
    echo "  5c anti-patterns: OK -- no inline Opaque-Transparent / bracket-match-goal in verif/"
    return 0
  fi
  local n
  n=$(printf '%s\n' "$hits" | grep -c .)
  echo "  5c anti-patterns: FAIL -- $n inline Opaque-Transparent/match-goal hit(s) in verif/:"
  printf '%s\n' "$hits" | print_capped
  return 1
}

# Numbered goal-selectors (`2:{`) and `all:` bullet chains are banned in
# verif/ (STYLE.md, "Banned in verif/"); every site was rewritten in phase F0.
check_5c2_goal_selectors() {
  local hits
  hits=$(
    {
      grep -rnE '^\s*[0-9]+:\s*\{' verif 2>/dev/null
      grep -rnE '^\s*all:' verif 2>/dev/null
    } | sort -u
  )
  if [ -z "$hits" ]; then
    echo "  5c2 goal-selectors: OK -- no numbered goal-selector / all: chain in verif/"
    return 0
  fi

  local n files_n counts
  n=$(printf '%s\n' "$hits" | grep -c .)
  counts=$(printf '%s\n' "$hits" | cut -d: -f1 | sort | uniq -c | awk '{print $2 ": " $1}')
  files_n=$(printf '%s\n' "$counts" | grep -c .)

  echo "  5c2 goal-selectors: FAIL -- $n site(s) in $files_n file(s):"
  printf '%s\n' "$counts" | print_capped
  return 1
}

check_5d_ascii() {
  local -a hits=()
  local f lines ln
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    lines=$(LC_ALL=C grep -noP '[^\x00-\x7F]' "$f" 2>/dev/null | cut -d: -f1 | sort -un)
    if [ -n "$lines" ]; then
      while IFS= read -r ln; do hits+=("$f:$ln"); done <<<"$lines"
    fi
  done < <(find . -path ./.git -prune -o -type f \( -name '*.v' -o -name '*.md' -o -name '*.sh' \) -print | sed 's|^\./||')

  if [ "${#hits[@]}" -eq 0 ]; then
    echo "  5d ascii: OK -- no non-ASCII bytes in any .v/.md/.sh file"
    return 0
  fi
  echo "  5d ascii: FAIL -- non-ASCII byte(s) found:"
  printf '%s\n' "${hits[@]}" | print_capped
  return 1
}

check_5e_spdx() {
  local -a bad=()
  local f c
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    [ "$f" = "clight/extraction.v" ] && continue
    c=$(grep -c 'SPDX-License-Identifier: MIT' "$f")
    [ "$c" -eq 1 ] || bad+=("$f (found $c SPDX line(s))")
  done < <(find $LAYER_DIRS audit -name '*.v' 2>/dev/null | sort)

  if [ "${#bad[@]}" -eq 0 ]; then
    echo "  5e spdx: OK -- every .v has exactly one SPDX line"
    return 0
  fi
  echo "  5e spdx: FAIL -- missing/duplicate SPDX line:"
  printf '%s\n' "${bad[@]}" | print_capped
  return 1
}

check_5f_gprog_import() {
  local -a bad=()
  local f c
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    c=$(grep -cE '^Require Import secp256k1\.contract\.gprog\.' "$f")
    [ "$c" -eq 1 ] || bad+=("$f (found $c gprog import(s))")
  done < <(find verif -name '*.v' 2>/dev/null | sort)

  if [ "${#bad[@]}" -eq 0 ]; then
    echo "  5f gprog-import: OK -- every verif/ file has exactly one contract.gprog import"
    return 0
  fi
  echo "  5f gprog-import: FAIL -- wrong contract.gprog import count:"
  printf '%s\n' "${bad[@]}" | print_capped
  return 1
}

check_5g_doc_paths() {
  local -a sources=()
  local f loc path
  local -a bad=()

  while IFS= read -r f; do
    [ -n "$f" ] && sources+=("$f")
  done < <(find $LAYER_DIRS audit clight -name '*.v' 2>/dev/null)
  for f in STYLE.md README.md; do
    [ -e "$f" ] && sources+=("$f")
  done

  if [ "${#sources[@]}" -eq 0 ]; then
    echo "  5g doc-paths: OK -- no source files to scan"
    return 0
  fi

  local refs
  refs=$(
    {
      grep -noE '`(vst|theory|model|contract|tactics|verif|audit|clight)/[A-Za-z0-9_./-]*\.v`' "${sources[@]}" 2>/dev/null \
        | sed -E 's/^([^:]+:[0-9]+):`([A-Za-z0-9_./-]+\.v)`$/\1\t\2/'
      grep -noE '\[(vst|theory|model|contract|tactics|verif|audit|clight)/[A-Za-z0-9_./-]*\.v\]' "${sources[@]}" 2>/dev/null \
        | sed -E 's/^([^:]+:[0-9]+):\[([A-Za-z0-9_./-]+\.v)\]$/\1\t\2/'
    }
  )

  while IFS=$'\t' read -r loc path; do
    [ -n "$path" ] || continue
    case "$path" in
      *..* | *'*'* | *'<'* | *'%'*) continue ;;
      audit/statement.v | secp256k1_fv.v) continue ;;  # planned files, documented before they exist
    esac
    [ -e "$path" ] || bad+=("$loc -> $path")
  done <<<"$refs"

  if [ "${#bad[@]}" -eq 0 ]; then
    echo "  5g doc-paths: OK -- every referenced <dir>/.../<name>.v path exists"
    return 0
  fi
  echo "  5g doc-paths: FAIL -- referenced path does not exist:"
  printf '%s\n' "${bad[@]}" | print_capped
  return 1
}

check_5h_tactics_gprog() {
  local hits
  hits=$(grep -rn 'contract\.gprog' tactics/ 2>/dev/null)
  if [ -z "$hits" ]; then
    echo "  5h tactics-gprog: OK -- no contract.gprog import in tactics/"
    return 0
  fi
  echo "  5h tactics-gprog: FAIL -- tactics/ file imports a proving context:"
  printf '%s\n' "$hits" | print_capped
  return 1
}

gate_5_style() {
  local name="GATE 5 STYLE"
  local rc=0
  local out_a out_b out_c out_c2 out_d out_e out_f out_g out_h

  out_a=$(check_5a_banned_tactics); [ $? -ne 0 ] && rc=1
  out_b=$(check_5b_do_n_forward); [ $? -ne 0 ] && rc=1
  out_c=$(check_5c_anti_patterns); [ $? -ne 0 ] && rc=1
  out_c2=$(check_5c2_goal_selectors); [ $? -ne 0 ] && rc=1
  out_d=$(check_5d_ascii); [ $? -ne 0 ] && rc=1
  out_e=$(check_5e_spdx); [ $? -ne 0 ] && rc=1
  out_f=$(check_5f_gprog_import); [ $? -ne 0 ] && rc=1
  out_g=$(check_5g_doc_paths); [ $? -ne 0 ] && rc=1
  out_h=$(check_5h_tactics_gprog); [ $? -ne 0 ] && rc=1

  if [ "$rc" -eq 0 ]; then
    echo "$name: OK -- all 9 style sub-checks passed "
  else
    echo "$name: FAIL -- one or more style sub-checks failed (see below)"
  fi
  printf '%s\n' "$out_a" "$out_b" "$out_c" "$out_c2" "$out_d" "$out_e" "$out_f" "$out_g" "$out_h"
  return $rc
}

# ---------------------------------------------------------------------------
# Dispatch

usage() {
  echo "usage: $(basename "$0") [gate...]   gate in {0 0b 1 2 3 4 5} or 'all' (default: all)" >&2
}

main() {
  local -a all_gates=(0 0b 1 2 3 4 5)
  local -a requested=("$@")
  local -a selected=()
  local r

  if [ "$#" -eq 0 ]; then
    requested=(all)
  fi
  for r in "${requested[@]}"; do
    if [ "$r" = "all" ]; then
      selected+=("${all_gates[@]}")
    else
      selected+=("$r")
    fi
  done

  local overall=0
  local g
  for g in "${selected[@]}"; do
    case "$g" in
      0) gate_0_fresh || overall=1 ;;
      0b) gate_0b_ast || overall=1 ;;
      1) gate_1_gaps || overall=1 ;;
      2) gate_2_axioms_src || overall=1 ;;
      3) gate_3_pin || overall=1 ;;
      4) gate_4_cone || overall=1 ;;
      5) gate_5_style || overall=1 ;;
      *)
        echo "check.sh: unknown gate '$g'" >&2
        usage
        overall=1
        ;;
    esac
  done
  exit "$overall"
}

main "$@"
