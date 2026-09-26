#!/bin/sh
# fn-store-rpool.service's ExecStart: import rpool WITHOUT mounting anything
# (altroot /othersys, no cache file: the pool is the old OS install and its
# datasets name /, /var/lib, /home; -N and the altroot keep them off the live
# system), load ONLY rpool/fn-public's key from its key file, and mount that
# one legacy dataset at /srv/fn-public. Idempotent: a pool ember has already
# imported and unlocked by hand is left as it is.
set -eu
DS=rpool/fn-public
MNT=/srv/fn-public
zpool list -H rpool >/dev/null 2>&1 || zpool import -N -R /othersys -o cachefile=none rpool
[ "$(zfs get -H -o value keystatus "$DS")" = available ] || zfs load-key "$DS"
mountpoint -q "$MNT" || mount -t zfs -o noatime,nodev,nosuid "$DS" "$MNT"
findmnt -no SOURCE,FSTYPE,OPTIONS "$MNT"
