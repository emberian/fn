#!/bin/bash
# One fresh process at a time. Run from repository root.
set -eu
base=fn2/experiments/squares/mutants
run () {
  local mutant=$1 name=$2 tape=${3:-}
  local free_kib
  free_kib=$(df -Pk . | awk 'NR==2 {print $4}')
  if [ "$free_kib" -lt 62914560 ]; then
    echo 'BLOCKED: less than 60 GiB free; no files deleted.'
    exit 3
  fi
  if [ -n "$tape" ]; then
    env FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 \
      FN2_E1_MUTANT="$mutant" FN2_E1_SEED=20261028 \
      FN2_E1_REPLAY="$tape" FN2_E1_OUTPUT="$base/$name.sexp" \
      timeout -k 5 900 tools/acl2 < "$base/qualify.lsp" > "$base/$name.log" 2>&1 &
  else
    env FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 \
      FN2_E1_MUTANT="$mutant" FN2_E1_SEED=20261028 \
      FN2_E1_OUTPUT="$base/$name.sexp" \
      timeout -k 5 900 tools/acl2 < "$base/qualify.lsp" > "$base/$name.log" 2>&1 &
  fi
  local run_pid=$!
  echo "$run_pid" > "$base/$name.pid"
  wait "$run_pid"
  rg '^E1 QUALIFICATION' "$base/$name.log"
}
for mutant in M2 M3 M4 M5; do
  run "$mutant" "replay-$mutant-20261028" "$base/qualification-$mutant-20261028.sexp"
  run ORIGINAL "original-prefix-$mutant-20261028" "$base/qualification-$mutant-20261028.sexp"
done
run M1 qualification-M1-20261028
run M6 qualification-M6-retry-20261028
