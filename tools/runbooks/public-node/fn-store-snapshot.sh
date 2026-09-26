#!/bin/sh
# Hourly snapshot of rpool/fn-public; keeps the newest 48 hourly and the
# newest 14 of those taken at 00 UTC. A ZFS snapshot is atomic, so it is the
# store as a power cut at that instant would leave it: restoring one is fn's
# recovery at open (the byte-level crash model), not a hot copy. It is valid
# only for the release that wrote it (D34: a reinstall moves data by
# `store export/import`, never by a snapshot of another format).
set -eu
DS=rpool/fn-public
now=$(date -u +%Y%m%dT%H%MZ)
zfs snapshot "$DS@auto-$now"
zfs list -H -t snapshot -o name -s creation "$DS" | grep "@auto-" | grep -v "T00..Z$" | head -n -48 | xargs -r -n1 zfs destroy
zfs list -H -t snapshot -o name -s creation "$DS" | grep "@auto-.*T00..Z$" | head -n -14 | xargs -r -n1 zfs destroy
