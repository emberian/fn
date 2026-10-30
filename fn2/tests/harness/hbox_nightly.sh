#!/bin/sh
# The hbox nightly surface run (RELEASE-PLAN §2.5): the whole suite at the hbox cadence against one image
# set, then the report table. Launch detached under swarm-build, with this script's PID file:
#
#   cd TREE && SWARM_MEM_MAX=64G setsid nohup swarm-build sh fn2/tests/harness/hbox_nightly.sh OUT \
#       > OUT.log 2>&1 < /dev/null &
#
# TREE is an extracted tree of the commit under test (`git archive`); OUT a fresh directory (refused if it
# exists). The script writes OUT/nightly.pid (its own PID; run_surface writes OUT/out/surface.pid), stops
# only through those files, and removes its own on exit. Stop it with `kill $(cat OUT/nightly.pid)`: the
# TERM is passed to run_surface's PID file, never to a pattern. The last log line is `DONE`.
#
# Environment (defaults are hbox's fn1 evidence set, recorded in fn2/docs/h-harness.md):
#   FN2_NIGHTLY_IMAGE    keyed image directory (fn-host*, *.core, lib, TREE_SHA)
#   FN2_NIGHTLY_TARGET   fn1 | fn2 (default fn1)
#   FN2_NIGHTLY_FAMILIES comma list for --family (default: every family)
#   FN2_NIGHTLY_HOURS    wall cap (default 8)
#   FN2_NIGHTLY_OPT_INS  space list of NAME=VALUE native opt-ins (default FN_RUN_SLOW=1 FN_RUN_RELOCATION_E2E=1)
#   FN2_NIGHTLY_KNOWN    JSON list classifying known rows for the report (default fn2/tests/surface/known-fn1.json)
#   FN2_NIGHTLY_MIN_GIB  free GiB the output filesystem must keep (default 60)
#   FN2_NIGHTLY_MIN_MEM_GIB least memory ceiling (physical, cgroup memory.max) the run needs (default 32)
set -u
OUT=${1:?usage: hbox_nightly.sh OUT}
T=$(pwd)
IMG=${FN2_NIGHTLY_IMAGE:-/tank/fn/images/keyed/c14e9e8e29ef4e34765271d69885970751f516ba317e583774b9bb9d261a40c4}
SSL=${FN2_NIGHTLY_OPENSSL:-/tank/fn/toolchains/openssl-3.5.8}
PY=${FN2_NIGHTLY_PYTHON:-/usr/bin/python3}
VENV=${FN2_NIGHTLY_VENV:-/tank/fn/scratch/fn2-h-harness/venv/lib/python3.12/site-packages}
[ -f "$T/fn2/tests/surface/run_surface.py" ] || { echo "nightly: run from an extracted tree (no fn2/tests here)"; exit 2; }
[ -f "$IMG/TREE_SHA" ] || { echo "nightly: no image set at $IMG"; exit 2; }
[ -e "$OUT" ] && { echo "nightly: $OUT exists; choose a fresh directory"; exit 2; }
mkdir -p "$OUT/bin" "$OUT/tmp" "$T/build" || exit 2
OUT=$(cd "$OUT" && pwd)
free=$(df -Pk "$OUT" | awk 'NR == 2 {print int($4 / 1048576)}')
if [ "$free" -lt "${FN2_NIGHTLY_MIN_GIB:-60}" ]; then
  echo "nightly: BLOCKED: $free GiB free on the output filesystem (under ${FN2_NIGHTLY_MIN_GIB:-60}); nothing run"
  echo DONE
  exit 3
fi
# fn1 sizes each node's connection capacity from the least memory ceiling it observes (physical
# memory, the cgroup's memory.max up the hierarchy; books/admission-memory.lisp): under a 16 GiB
# ceiling a node holds 22 connections, not 31, and control_across_peers, which holds 31 on each node,
# meets the spec's 400 (H6). Refuse a ceiling under FN2_NIGHTLY_MIN_MEM_GIB (default 32).
ceiling=$(awk '/MemTotal/ {print int($2 / 1048576)}' /proc/meminfo)
cg=$(sed -n 's/^0:://p' /proc/self/cgroup)
while [ -n "$cg" ] && [ "$cg" != / ]; do
  if [ -f "/sys/fs/cgroup$cg/memory.max" ]; then
    m=$(cat "/sys/fs/cgroup$cg/memory.max")
    [ "$m" != max ] && [ $((m / 1073741824)) -lt "$ceiling" ] && ceiling=$((m / 1073741824))
  fi
  cg=$(dirname "$cg")
done
echo "nightly: memory ceiling $ceiling GiB (least of physical and cgroup memory.max)"
if [ "$ceiling" -lt "${FN2_NIGHTLY_MIN_MEM_GIB:-32}" ]; then
  echo "nightly: BLOCKED: memory ceiling $ceiling GiB under ${FN2_NIGHTLY_MIN_MEM_GIB:-32}; launch with SWARM_MEM_MAX=64G; nothing run"
  echo DONE
  exit 3
fi
echo $$ > "$OUT/nightly.pid"
stop() {
  [ -f "$OUT/out/surface.pid" ] && kill "$(cat "$OUT/out/surface.pid")" 2>/dev/null
}
trap 'stop; rm -f "$OUT/nightly.pid"; echo "nightly: stopped"; echo DONE; exit 130' TERM INT
# Every image file of the set (launchers, cores, *.world-deps: H5c's image_differential failed for
# want of fn-host.world-deps when this was a fixed list) and its lib.
for f in "$IMG"/fn-host* "$IMG"/lib; do
  [ -e "$f" ] && ln -sfn "$f" "$T/build/$(basename "$f")"
done
printf '%s\n' '#!/bin/sh' "LD_LIBRARY_PATH=$SSL/lib exec $SSL/bin/openssl \"\$@\"" > "$OUT/bin/openssl-test"
chmod 0755 "$OUT/bin/openssl-test"
export FN_TEST_OPENSSL_BIN="$OUT/bin/openssl-test" FN_OPENSSL_PREFIX="$SSL" FN_TEST_DURABLE_TMP="$OUT/tmp"
export FN_FIXTURES_DIR=${FN_FIXTURES_DIR:-/tank/fn/scratch/fixtures}
# The production image for every family; the developer image (its [web] face, carry and bp-obligation)
# for the web and bp S forms and every native that names it, with its own identity under its prefix.
export FN_NATIVE_HOST="$T/build/fn-host" FN_NATIVE_DEVELOPER_HOST="$T/build/fn-host-developer"
export PYTHONPATH="$VENV" PYTHONDONTWRITEBYTECODE=1
SOURCE=$(cat "$IMG/TREE_SHA")
eval "$($PY tools/native_env.py identity --image "$T/build/fn-host" --source "$SOURCE" --export)"
eval "$($PY tools/native_env.py identity --image "$T/build/fn-host-developer" --source "$SOURCE" \
  --prefix FN_NATIVE_DEVELOPER_ --export)"
export FN2_SURFACE_IDENTITY="$T/build/fn-host" FN2_SURFACE_SOURCE="$SOURCE"
# The E fixture drivers (fn2/tests/surface/fixtures.py; the bp golden row runs the DTN image's bp verbs).
export FN_NATIVE_DTN_HOST="$T/build/fn-host-dtn"
for F in NNTP CONSUMER BP TLS_AUTH WEB; do export "FN2_SURFACE_FIXTURE_$F=fn2.tests.surface.fixtures:fixture"; done
# The F, H and R drivers (H7): fuzz for the eight families besides nntp, history for peering and bp, the
# tools/load perf cells for every published row.
for F in CONSUMER OPERATOR WEB PEERING BP TLS_AUTH CONFIG_LIMITS STORE_OPS; do
  export "FN2_SURFACE_FUZZ_$F=fn2.tests.surface.fuzz:fuzz"
done
for F in PEERING BP; do export "FN2_SURFACE_HISTORY_$F=fn2.tests.surface.history_drivers:history"; done
for F in NNTP CONSUMER OPERATOR WEB PEERING BP TLS_AUTH CONFIG_LIMITS STORE_OPS; do
  export "FN2_SURFACE_PERF_$F=fn2.tests.surface.perf:perf"
done
for opt in ${FN2_NIGHTLY_OPT_INS-FN_RUN_SLOW=1 FN_RUN_RELOCATION_E2E=1}; do export "$opt"; done
FAMILY=${FN2_NIGHTLY_FAMILIES:+--family $FN2_NIGHTLY_FAMILIES}
[ -n "$FAMILY" ] || FAMILY=--all
echo "nightly: tree $T image $IMG (TREE_SHA $SOURCE) target ${FN2_NIGHTLY_TARGET:-fn1} $FAMILY opt-ins ${FN2_NIGHTLY_OPT_INS-FN_RUN_SLOW=1 FN_RUN_RELOCATION_E2E=1}"
uptime
started=$(date +%s)
timeout --foreground --signal=TERM $(( ${FN2_NIGHTLY_HOURS:-8} * 3600 ))s \
  $PY -m fn2.tests.surface.run_surface --target "${FN2_NIGHTLY_TARGET:-fn1}" --box hbox $FAMILY --out "$OUT/out" &
child=$!
wait $child
code=$?
echo "surface exit $code after $(( $(date +%s) - started )) s"
KNOWN=${FN2_NIGHTLY_KNOWN:-$T/fn2/tests/surface/known-fn1.json}
[ -f "$KNOWN" ] || KNOWN=
if [ -f "$OUT/out/surface.json" ]; then
  $PY -m fn2.tests.surface.nightly "$OUT/out" ${KNOWN:+--known "$KNOWN"} \
    --title "Nightly $(date -u +%Y-%m-%d) at $(git -C "$T" rev-parse --short HEAD 2>/dev/null || basename "$T")" > "$OUT/nightly.md"
  echo "report: $OUT/nightly.md"
fi
uptime
rm -f "$OUT/nightly.pid"
echo DONE
