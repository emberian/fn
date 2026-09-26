#!/bin/sh
# round.sh LABEL: one round over every candidate mount, on hbox, under
# systemd-run --user --scope -p MemoryMax=2G. Box state printed beside each figure.
set -u
B=/tank/fn/scratch/node-disk
L=$1
for M in /tank/fn/scratch/node-disk /var/tmp /othersys/home/hbox /dev/shm; do
  for spec in "4096 fsync" "4096 fdatasync" "65536 fsync"; do
    set -- $spec
    echo "== $L mount=$M $(uptime | sed 's/.*load average/load/')"
    echo "units: $(systemctl --user list-units --state=running --no-legend | grep -E 'qual|img|native' | awk '{print $1}' | tr '\n' ' ')"
    systemd-run --user --scope --quiet -p MemoryMax=2G "$B/fsync_probe" "$M" "$1" 100 "$2"
  done
done
echo "== $L end $(date -u +%FT%TZ)"
