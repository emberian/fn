#!/bin/ksh
# A node's first minutes on OpenBSD under a stock login class's datasize,
# from an installed release (cut_release.sh gate 13; lane openbsd-datasize).
#
#   ksh tools/openbsd_smoke.sh FN DATASIZE_KIB DIR PORT
#
# FN is the installed bin/fn; DATASIZE_KIB the soft limit to run under
# (4194304: the stock `daemon' class a node's rc.d service runs in; 1572864:
# the `default' class); DIR a scratch directory (it is emptied; any file
# system); PORT a free loopback port.  In order, each under
# that limit: --version; a loopback fn.toml (no login: the development
# defaults a loopback listener keeps); `init' with no profile (fn sizes the
# store for the limit); `run' to LISTENING; a POST (240) and its ARTICLE
# (220); kill -9 of the owner; `recover'; `run' again, the first article
# still served (220) and a second POST (240); `status'; a clean stop.  The
# last line is `openbsd_smoke: OK ...' (exit 0) or `openbsd_smoke: RED
# STEP: ...' (exit 1).  The NNTP client is the guest's python3 (a build VM
# has it; a friend's node need not).  It changes nothing outside DIR.
set -u
[ $# -eq 4 ] || { echo 'usage: openbsd_smoke.sh FN DATASIZE_KIB DIR PORT' >&2; exit 2; }
FN=$1 DS=$2 D=$3 PORT=$4
OWNER=
red() {
  echo "openbsd_smoke: RED $1: $2"
  [ -n "$OWNER" ] && kill -9 "$OWNER" 2>/dev/null
  exit 1
}
ulimit -d "$DS" || red ulimit "cannot set datasize $DS KiB"
rm -rf "$D" && mkdir -p "$D" || red dir "cannot make $D"
echo "== datasize $(ulimit -d) KiB, physmem $(sysctl -n hw.physmem)"

v=$("$FN" --version 2>&1) || red version "$v"
echo "version: $v"

printf '[store]\npath = "%s/store"\n[listener]\nhost = "127.0.0.1"\nport = %s\n[posting]\nenabled = true\n[control]\npath = "%s/c.sock"\n' \
  "$D" "$PORT" "$D" > "$D/fn.toml"
o=$("$FN" operator "$D/fn.toml" init fn.test 2>&1) || red init "$o"
echo "$o" | grep '^init: '
echo "$o" | grep -q 'within-budget=yes' || red init "not within the budget: $o"

# nntp WORDS: python3 speaks NNTP on the loopback port; prints one reply
# line per step.  post N posts article N; read N fetches it.
nntp() {
  python3 - "$PORT" "$@" <<'PY'
import socket, sys
port, verb, n = int(sys.argv[1]), sys.argv[2], sys.argv[3]
s = socket.create_connection(("127.0.0.1", port), timeout=60)
f = s.makefile("rwb")
def line(cmd=None):
    if cmd:
        f.write(cmd.encode() + b"\r\n"); f.flush()
    return f.readline().decode("latin-1").strip()
line()
mid = "<openbsd-smoke-%s@smoke.invalid>" % n
if verb == "post":
    r = line("POST")
    if r.startswith("340"):
        f.write(("From: smoke@smoke.invalid\r\nNewsgroups: fn.test\r\nSubject: smoke %s\r\n"
                 "Message-ID: %s\r\n\r\nbody %s\r\n.\r\n" % (n, mid, n)).encode()); f.flush()
        r = line()
else:
    r = line("ARTICLE " + mid)
print(r)
PY
}

start() {
  "$FN" operator "$D/fn.toml" run > "$D/run$1.out" 2> "$D/run$1.err" &
  OWNER=$!
  i=0
  while [ $i -lt 300 ]; do
    grep -q '^LISTENING ' "$D/run$1.out" 2>/dev/null && { echo "run $1: LISTENING"; return 0; }
    kill -0 "$OWNER" 2>/dev/null || { wait "$OWNER"; red "run$1" "exit $? before LISTENING: $(tail -3 "$D/run$1.err" | tr '\n' ' ')"; }
    sleep 1; i=$((i + 1))
  done
  red "run$1" "no LISTENING in 300 s"
}

start 1
r=$(nntp post 1) ; echo "post 1: $r"; case $r in 240*) ;; *) red post1 "$r" ;; esac
r=$(nntp read 1) ; echo "read 1: $r"; case $r in 220*) ;; *) red read1 "$r" ;; esac

kill -9 "$OWNER"; wait "$OWNER" 2>/dev/null; OWNER=
echo "kill -9: done"
o=$("$FN" operator "$D/fn.toml" recover 2>&1) || red recover "$o"
echo "recover: $(echo "$o" | tail -1)"

start 2
r=$(nntp read 1) ; echo "read 1 after kill -9: $r"; case $r in 220*) ;; *) red reread1 "$r" ;; esac
r=$(nntp post 2) ; echo "post 2: $r"; case $r in 240*) ;; *) red post2 "$r" ;; esac
o=$("$FN" operator "$D/fn.toml" status 2>&1) || red status "$o"
h=$(echo "$o" | grep '^heap=') || red status "no heap line: $o"
echo "status: $h"

kill "$OWNER"
i=0
while kill -0 "$OWNER" 2>/dev/null && [ $i -lt 60 ]; do sleep 1; i=$((i + 1)); done
kill -0 "$OWNER" 2>/dev/null && red stop "the owner did not stop in 60 s after SIGTERM"
OWNER=
echo "openbsd_smoke: OK datasize=$DS KiB $h"
