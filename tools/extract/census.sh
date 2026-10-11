#!/bin/sh
# tools/extract/census.sh RUNDIR [BASELINE] -- the executed-set census of one hbox image
# run (tools/hbox_native.sh's RUNDIR, whose tree/build/fn-host-developer is the train's
# developer image), as a detached step: it starts itself under swarm-build with nohup and
# timeout, writes RUNDIR/census.pid and RUNDIR/census.log, and returns.  The inner run:
#   1. fn-core: tools/extract/core.sh unless tree/build/core/fn-core exists (check.sh built it);
#      the gate arm's transcripts: tools/extract/transcripts.py unless check.sh wrote them;
#   2. executed_set.py run (gate, served, load), books, sizes, census into RUNDIR/census/;
#   3. the shrink line (executed_set.py line), against BASELINE (a census.json) when given,
#      into RUNDIR/census/line.txt and the log.
# The log's last line is `== census done status N'; N is 0 only when every step succeeded.
# Workload children may fail (their statuses are in RUNDIR/census/arms.json); the census
# counts what they ran.  Environment: FN_CENSUS_TIMEOUT (seconds, default 14400).
set -u
[ $# -ge 1 ] || { echo "usage: census.sh RUNDIR [BASELINE]" >&2; exit 2; }
R=$(cd "$1" && pwd) || { echo "census: no run directory $1" >&2; exit 2; }
B=${2:-}
[ -x "$R/tree/build/fn-host-developer" ] || { echo "census: $R/tree/build/fn-host-developer is not built" >&2; exit 2; }
if [ -z "${FN_CENSUS_INNER:-}" ]; then
    FN_CENSUS_INNER=1 nohup setsid swarm-build timeout "${FN_CENSUS_TIMEOUT:-14400}" \
        sh "$R/tree/tools/extract/census.sh" "$R" $B > "$R/census.log" 2>&1 < /dev/null &
    echo $! > "$R/census.pid"
    echo "census: started (pid $(cat "$R/census.pid")); log $R/census.log"
    exit 0
fi
T=$R/tree
O=$R/census
X=$T/tools/extract
mkdir -p "$O/pathbin"
export FN_OPENSSL_PREFIX=${FN_OPENSSL_PREFIX:-/tank/fn/toolchains/openssl-3.5.8}
export FN_TEST_DURABLE_TMP=${FN_TEST_DURABLE_TMP:-/var/tmp}
if [ -x "$R/bin/openssl-test" ]; then
    export FN_TEST_OPENSSL_BIN=$R/bin/openssl-test
    ln -sf "$R/bin/openssl-test" "$O/pathbin/openssl"     # tests that call `openssl' for ML-DSA keys
    export PATH=$O/pathbin:$PATH
fi
cd "$T" || exit 1
st=0
step() { name=$1; shift; echo "== $name $(date -u +%T)"; "$@"; rc=$?; echo "   $name exit $rc"; [ $rc = 0 ] || st=$rc; return $rc; }
[ -x build/core/fn-core ] || step core sh "$X/core.sh" . || { echo "== census done status $st"; exit $st; }
[ -n "$(ls build/extract/check/transcripts/*.chunks 2>/dev/null)" ] || \
    step transcripts python3 "$X/transcripts.py" build/extract/check/transcripts || { echo "== census done status $st"; exit $st; }
step run python3 "$X/executed_set.py" run . build/fn-host-developer build/core/fn-core "$O"
step books python3 "$X/executed_set.py" books build/fn-host-developer "$O" --tree .
step sizes python3 "$X/executed_set.py" sizes build/core/fn-core "$O"
step census sh -c "python3 '$X/executed_set.py' census '$O' build/core --books '$O/books.tsv' --sizes '$O/sizes.tsv' --tree . --json '$O/census.json' > '$O/census.md'"
if [ -n "$B" ]; then
    step line sh -c "python3 '$X/executed_set.py' line '$O/census.json' --baseline '$B' > '$O/line.txt'"
else
    step line sh -c "python3 '$X/executed_set.py' line '$O/census.json' > '$O/line.txt'"
fi
cat "$O/line.txt" 2>/dev/null
echo "== census done status $st"
exit $st
