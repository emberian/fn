#!/bin/sh
# spike-storage: timed opens of the store at W with image I; logs to L (jsonl-ish lines)
W=$1; I=$2; L=$3; shift 3
. /tank/fn/scratch/bounds-p3/env.sh
export ACL2_CUSTOMIZATION=NONE
for step in "$@"; do
  case $step in
    status) args="--fn operator $W/fn.toml status";;
    checkpoint) args="--fn operator $W/fn.toml store checkpoint";;
    *) args="--fn operator $W/fn.toml $step";;
  esac
  s=$(date +%s.%N)
  out=$(/usr/bin/time -f "MAXRSS_KIB %M" $I $args 2>&1)
  rc=$?
  e=$(date +%s.%N)
  echo "{\"step\": \"$step\", \"rc\": $rc, \"wall_s\": $(echo "$e - $s" | bc), \"rss\": \"$(echo "$out" | grep MAXRSS | cut -d' ' -f2)\", \"lines\": \"$(echo "$out" | grep -E '^open=|^checkpoint |^reclaim|^chain|^transactions=|^compact|^released|error' | tr '\n' '|' | tr '"' "'")\"}" >> $L
done
du -sk $W/store >> $L
