#!/bin/sh
# tools/runtime_image/bare_measure.sh SBCL ACL2_CORE
# Resident size of a bare SBCL and of the bare ACL2 core, each idle 5 s after
# start with a 1024 MB dynamic space, and the dynamic space each core needs
# (the runtime's "N KiB required").  Prints key=value lines.
set -u
SBCL=$1 CORE=$2
rss() { awk '/^VmRSS/ {print $2}' /proc/$1/status; }
sh -c "sleep 30 | exec $SBCL --dynamic-space-size 1024MB --noinform --no-userinit" >/dev/null 2>&1 &
p=$!; sleep 6; c=$(pgrep -P $p sbcl || echo $p); echo "bare_sbcl_rss_kib=$(rss $c)"; kill $p $c 2>/dev/null
sh -c "sleep 30 | exec $SBCL --dynamic-space-size 1024MB --core $CORE --noinform --no-userinit --eval '(acl2::sbcl-restart)'" >/dev/null 2>&1 &
p=$!; sleep 8; c=$(pgrep -P $p sbcl || echo $p); echo "bare_acl2_rss_kib=$(rss $c)"; kill $p $c 2>/dev/null
echo "bare_sbcl_core_required: $($SBCL --dynamic-space-size 8MB --non-interactive --no-userinit 2>&1 </dev/null | grep -o '[0-9]*KiB required')"
echo "bare_acl2_core_required: $($SBCL --dynamic-space-size 8MB --core $CORE --non-interactive 2>&1 </dev/null | grep -o '[0-9]*KiB required')"
wait 2>/dev/null
