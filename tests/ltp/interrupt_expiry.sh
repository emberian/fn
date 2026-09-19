#!/bin/bash
# Interruption and expiry cases for the fn ION BP-over-LTP laboratory.
#
# The link is cut by dropping the receiving node's LTP/UDP datagrams with one
# named iptables rule, which is deleted by number at the end.  The ruleset is
# never flushed: this host is shared.  ION's own `killm` is never used.
set -u
. "$(dirname "$0")/env.sh"
RUN=${1:?usage: interrupt_expiry.sh RUNDIR}
NODE1=$ION_ROOT/cfg/node1
NODE2=$ION_ROOT/cfg/node2
RECV_PORT=42113
mkdir -p "$RUN/stage-interrupt" "$RUN/stage-expiry"

block()   { sudo -n iptables -I INPUT 1 -i lo -p udp --dport $RECV_PORT -j DROP; }
unblock() { sudo -n iptables -D INPUT -i lo -p udp --dport $RECV_PORT -j DROP; }
staged()  { ls -1 "$1" 2>/dev/null | grep -v '^\.' | head -1; }

# ---- case 1: cut the LTP link mid-transfer, then restore it ----------------
head -c 60000 /dev/urandom > "$RUN/interrupt.bin"
( cd "$NODE2" && exec fn_ltp_stage ipn:2.1 "$RUN/stage-interrupt" 300 1 ) \
    > "$RUN/stage-interrupt.log" 2>&1 &
STAGER1=$!
sleep 2
block
BLOCK_RC=$?
( cd "$NODE1" && bpsendfile ipn:1.1 ipn:2.1 "$RUN/interrupt.bin" 0 600 ) \
    > "$RUN/interrupt-send.log" 2>&1
sleep 20
DURING=$(staged "$RUN/stage-interrupt")
unblock
RESUMED=""
for _ in $(seq 1 60); do
  RESUMED=$(staged "$RUN/stage-interrupt")
  [ -n "$RESUMED" ] && break
  sleep 3
done
INTACT=false
if [ -n "$RESUMED" ] && cmp -s "$RUN/stage-interrupt/$RESUMED" "$RUN/interrupt.bin"; then
  INTACT=true
fi
wait $STAGER1 2>/dev/null

# ---- case 2: cut the link and let the bundle's lifetime expire -------------
head -c 4096 /dev/urandom > "$RUN/expiry.bin"
( cd "$NODE2" && exec fn_ltp_stage ipn:2.1 "$RUN/stage-expiry" 120 1 ) \
    > "$RUN/stage-expiry.log" 2>&1 &
STAGER2=$!
sleep 2
block
( cd "$NODE1" && bpsendfile ipn:1.1 ipn:2.1 "$RUN/expiry.bin" 0 20 ) \
    > "$RUN/expiry-send.log" 2>&1
sleep 60
unblock
sleep 45
EXPIRED_ARRIVAL=$(staged "$RUN/stage-expiry")
wait $STAGER2 2>/dev/null

cat > "$RUN/interrupt-expiry.json" <<JSON
{
  "schema": 1,
  "link_cut": "iptables INPUT -i lo -p udp --dport $RECV_PORT -j DROP, inserted and deleted by rule, never a ruleset flush",
  "interruption": {
    "adu_octets": 60000,
    "ltp_segment_octets": 1200,
    "bundle_lifetime_seconds": 600,
    "staged_while_link_was_cut": "${DURING:-none}",
    "staged_after_link_restored": "${RESUMED:-none}",
    "bytes_identical_to_source": $INTACT
  },
  "expiry": {
    "adu_octets": 4096,
    "bundle_lifetime_seconds": 20,
    "seconds_link_cut": 60,
    "seconds_waited_after_restore": 45,
    "staged_after_restore": "${EXPIRED_ARRIVAL:-none}"
  }
}
JSON
cat "$RUN/interrupt-expiry.json"
