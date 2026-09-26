#!/bin/sh
# One-time storage setup for the public node on hbox (lane public-node,
# 2026-09-26; PKT-579's rpool branch). Run by ember as root ON HBOX:
#
#   sudo sh store-rpool-setup.sh            # prints every command, changes nothing
#   sudo sh store-rpool-setup.sh --apply    # runs them
#
# What it makes:
#   rpool/fn-public   its own encryption root (raw 32-octet key in
#                     /etc/zfs/keys/fn-public.key on the NVMe root, 0400 root),
#                     mountpoint=legacy, mounted at /srv/fn-public by
#                     fn-store-rpool.service at every boot. The rest of rpool
#                     stays exactly as it is (hand-unlocked, altroot /othersys).
#   fn-store-snapshot.timer   hourly snapshots, 48 hourly + 14 daily kept.
#
# Why its own key: rpool's own key lives in /run/keystore (a LUKS zvol opened
# by hand with a passphrase), so nothing under rpool's key can mount at boot
# unattended. A child encryption root with a key file mounts unattended; the
# cost is that the key sits on the unencrypted NVMe root. BACK THE KEY UP
# (e.g. 1Password): losing it loses the store.
#
# Properties are the ones node-disk measured 0.79 ms / 0.89 ms (p50/p95, 4 KiB
# append+fsync) under, plus atime=off: sync=standard (NEVER disabled: fn's
# durable acceptance is an fsync), logbias=latency, lz4, 128K records.
# refquota bounds the live store, quota the store plus its snapshots; rpool had
# 96.4G available at 2026-09-26T22Z (zfs list), 86 percent full.
set -eu
APPLY=0
[ "${1:-}" = "--apply" ] && APPLY=1
HERE=$(cd "$(dirname "$0")" && pwd)
DS=rpool/fn-public
MNT=/srv/fn-public
KEY=/etc/zfs/keys/fn-public.key
OWNER=hbox:hbox
run() { echo "+ $*"; [ "$APPLY" = 1 ] && sh -c "$*"; return 0; }

[ "$(id -u)" = 0 ] || { echo "run as root (sudo)"; exit 2; }
zpool list -H rpool >/dev/null 2>&1 || { echo "rpool is not imported: unlock and import it by hand first"; exit 2; }
avail=$(zfs get -Hp -o value available rpool)
echo "rpool available: $avail octets"
[ "$avail" -ge 53687091200 ] || { echo "rpool has under 50 GB free: use the NVMe fallback (a plain directory $MNT)"; exit 3; }
if zfs list -H "$DS" >/dev/null 2>&1; then echo "$DS exists; not recreating"; else
  run "install -d -m 0700 /etc/zfs/keys"
  run "[ -e $KEY ] || (umask 077; dd if=/dev/urandom of=$KEY bs=32 count=1 status=none)"
  run "chmod 0400 $KEY"
  run "zfs create -o encryption=aes-256-gcm -o keyformat=raw -o keylocation=file://$KEY -o mountpoint=legacy -o compression=lz4 -o atime=off -o xattr=sa -o sync=standard -o logbias=latency -o refquota=56G -o quota=72G -o reservation=8G $DS"
fi
# The empty mountpoint is made immutable so nothing can write into the NVMe
# root underneath when the dataset is not mounted.
run "install -d -m 0755 $MNT"
run "mountpoint -q $MNT || chattr +i $MNT"
run "install -m 0755 $HERE/fn-store-rpool-mount.sh /usr/local/sbin/fn-store-rpool-mount"
run "install -m 0755 $HERE/fn-store-snapshot.sh /usr/local/sbin/fn-store-snapshot"
run "install -m 0644 $HERE/fn-store-rpool.service $HERE/fn-store-snapshot.service $HERE/fn-store-snapshot.timer /etc/systemd/system/"
run "systemctl daemon-reload"
run "systemctl enable --now fn-store-rpool.service"
run "chown $OWNER $MNT && chmod 0750 $MNT"
run "systemctl enable --now fn-store-snapshot.timer"
run "findmnt -no SOURCE,FSTYPE,OPTIONS $MNT"
run "zfs get -H -o property,value encryptionroot,keystatus,keylocation,refquota,quota,reservation,sync,atime $DS"
echo "Back up $KEY now (32 raw octets; base64 it into your password manager)."
