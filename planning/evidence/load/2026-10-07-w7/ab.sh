#!/bin/bash
# usage: ab.sh WORKDIR OUT MODE RUNS "R list" LABEL=PATH [LABEL=PATH ...]   (run on persvati; one cell per lock hold)
# Order: for each run index, for each arm, for each R: A B A B ...  Templates are loaded first, outside the lock.
W=$1; OUT=$2; MODE=$3; RUNS=$4; RS=$5; shift 5
SRC=/tank/fn/scratch/load-w7/src/tools/load/w7_extent.py
for spec in "$@"; do taskset -c 12-23 python3.12 $SRC template --image "$spec" --workdir "$W" || exit 1; done
for run in $(seq 0 $((RUNS-1))); do
  for R in $RS; do
    for spec in "$@"; do
      flock /tank/fn/scratch/timing-12-23.lock taskset -c 12-23 python3.12 $SRC run --image "$spec" --readers $R --runs 1 --first-run $run --workdir "$W" --out "$OUT" --mode "$MODE"
    done
  done
done
