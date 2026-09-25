#!/bin/sh
# Drive tin 2.6.2 against an fn node through tools/nntp_wire_log.py (reader-surface lane; from the reader spike, D28).
#   tin_drive.sh TIN WIRE_PORT HOME_DIR OUT_DIR STEP...
# TIN_FLAGS (default "-r -A") are tin's flags; -A forces AUTHINFO.
# Each STEP is "keys|seconds|name": tmux send-keys KEYS, wait, save the pane
# as OUT_DIR/NN-name.txt.  The session is named spiketin and owned by this run.
set -eu
tin=$1 port=$2 home=$3 out=$4; shift 4
mkdir -p "$out"
tmux kill-session -t spiketin 2>/dev/null || true
tmux new-session -d -s spiketin -x 120 -y 40 \
  "env HOME=$home TERM=xterm EDITOR=$home/editor.sh VISUAL=$home/editor.sh $tin ${TIN_FLAGS:--r -A} -p $port -g 127.0.0.1 2>$home/tin.stderr; sleep 3600"
sleep 8
n=0
tmux capture-pane -p -t spiketin > "$out/00-start.txt"
for step in "$@"; do
  n=$((n + 1))
  keys=${step%%|*}; rest=${step#*|}; wait=${rest%%|*}; name=${rest#*|}
  if [ "$keys" = "ENTER" ]; then tmux send-keys -t spiketin Enter
  elif [ "${keys#TEXT:}" != "$keys" ]; then tmux send-keys -t spiketin -l "${keys#TEXT:}"
  else tmux send-keys -t spiketin "$keys"; fi
  sleep "$wait"
  tmux capture-pane -p -t spiketin > "$out/$(printf %02d $n)-$name.txt"
done
