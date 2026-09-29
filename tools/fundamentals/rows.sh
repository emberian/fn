#!/bin/sh
# The box half of tools/fundamentals.py: F1 to F8 on ONE image tree, with the
# fundamentals scoreboard's methods (planning/evidence/fundamentals-2026-09-27/
# README.md; its harness/run_all.sh is this driver's origin).  Run on hbox:
#
#   rows.sh TREE OUT [STEPS]
#
# TREE is a tools/hbox_native.sh tree whose build/ holds fn-host (production),
# fn-host-developer, fn-host-dtn and fn-host-dtn-developer (--images
# developer,production,dtn,dtn-developer); the step `heap' adds
# fn-host-developer-heap (build_heap_image.sh) when it is not there.  OUT
# receives one output per row, driver.log (the box's load, ARC and three
# largest processes before every row, each row's exit) and images.sha256.
#
# Pinning, as the scoreboard: the rows run one after another pinned to
# ROW_CORES (default 20-23) in their own systemd scopes with a MemoryMax;
# the F4 mixed hour runs at the same time on F4_CORES (16-19) and the stall
# case after it there; swarm-build uses 0-15.  The native modules (F5's
# capacity check, F7) run unpinned under a 24G scope, as hbox_native.sh runs
# them.  Stores live on /dev/shm except F3's (its disks are the row).
#
# Environment: ROW_CORES, F4_CORES, F4_SECONDS (3600), F6_FIXTURES (the
# registered fixture directory, /tank/fn/scratch/fixtures), F2_BEFORE (an
# older developer image for F2's before/after; none by default),
# EDGE_SSH (an ssh destination with python3 and this tree's F3 harness for
# the edge disk's POST/s; none by default), OPENSSL_TEST (an OpenSSL 3.5
# binary for the ML-DSA-65 test keys; default hbox's 3.5.8 toolchain).
# STEPS default: "heap f4 f5 f5n f8 f1 f6c f3 f2 f7 wait f4s" (f6c: F6 from the
# scale curve, TREE/tools/scale_curve.py over the curve fixture; f6: the old
# chain-20000 and t40k-2k-cp5 opens).
set -u
T=$1; O=$2; STEPS=${3:-"heap f4 f5 f5n f8 f1 f6c f3 f2 f7 wait f4s"}
H=$(cd "$(dirname "$0")" && pwd)
ROW_CORES=${ROW_CORES:-20-23}; F4_CORES=${F4_CORES:-16-19}; F4_SECONDS=${F4_SECONDS:-3600}
FX=${F6_FIXTURES:-/tank/fn/scratch/fixtures}
# This invocation's own scratch: a second rows.sh on the same OUT never removes it.
W=/dev/shm/fundamentals-$(basename "$(dirname "$O")")-$$
DEV=$T/build/fn-host-developer; PROD=$T/build/fn-host; PROF=$T/build/fn-host-developer-heap
mkdir -p "$O" "$W" "$O/bin" "$O/logs"
if [ -z "${OPENSSL_TEST:-}" ]; then
  printf '%s\n' '#!/bin/sh' 'LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib exec /tank/fn/toolchains/openssl-3.5.8/bin/openssl "$@"' > "$O/bin/openssl-test"
  chmod 0755 "$O/bin/openssl-test"; OPENSSL_TEST=$O/bin/openssl-test
fi
# The environment hbox_native.sh gives its modules (a module that runs ACL2,
# as the BP bridge does, needs FN_ACL2 and the certificate cache).
export FN_ACL2=${FN_ACL2:-/tank/fn/toolchains/w28/acl2-literal-4g} FN_CERT_CACHE=${FN_CERT_CACHE:-/tank/fn/certcache} FN_CERT_ORIGIN_KIND=run
export FN_TEST_OPENSSL_BIN=$OPENSSL_TEST
unset FN_OPENSSL_PREFIX
box() { echo "$(date -u +%FT%TZ) $1 load: $(cut -d' ' -f1-3 /proc/loadavg); arc=$(awk '/^size/{print $3}' /proc/spl/kstat/zfs/arcstats 2>/dev/null); top: $(ps -eo rss,comm --sort=-rss | sed -n 2,4p | tr '\n' ';')" >> "$O/driver.log"; }
scope() { mem=$1; cores=$2; shift 2; systemd-run --user --scope -q -p MemoryMax=$mem -p MemorySwapMax=0 taskset -c "$cores" "$@"; }
done_() { echo "$(date -u +%FT%TZ) $1 rc=$2" >> "$O/driver.log"; }
# A native module as hbox_native.sh runs it: tools/native_env.py's variables
# for the four images, then EXTRA (NAME=VALUE ...), under a 24G scope.
module() {
  label=$1 mod=$2; shift 2
  assignments=$(python3 tools/native_env.py plan --images developer,production,dtn,dtn-developer "$mod" 2>/dev/null \
    | awk -v m="$mod" '$1 == m { $1 = ""; print }' | sed "s#\\\$T#$T#g")
  box "$label"
  # shellcheck disable=SC2086
  env FN_TEST_OPENSSL_BIN="$OPENSSL_TEST" FN_TEST_OPENSSL="$OPENSSL_TEST" $assignments "$@" \
    systemd-run --user --scope --quiet -p MemoryMax=24G -p MemorySwapMax=0 -- \
    python3 tools/test_budget.py --one "$mod" > "$O/logs/$label.log" 2>&1
  rc=$?
  echo "$(python3 tools/test_budget.py --verdict "$O/logs/$label.log" 2>&1)" > "$O/logs/$label.verdict"
  done_ "$label" $rc
}
cd "$T" || exit 2
F4PID=
for step in $STEPS; do
case $step in
heap)
  if [ ! -x "$PROF" ]; then
    box heap-image; sh "$H/build_heap_image.sh" "$T" > "$O/logs/heap-image.log" 2>&1; done_ heap-image $?
  fi
  (cd build && sha256sum fn-host.core fn-host-developer.core fn-host-dtn.core fn-host-dtn-developer.core fn-host-developer-heap.core 2>/dev/null) > "$O/images.sha256" ;;
f4)
  rm -rf "$W/f4"; mkdir -p "$W/f4"
  date -u +%FT%TZ > "$O/f4-start.txt"; box f4-start
  ( FN_MIXED_AGENTS=0 FN_MIXED_CONTROL=1 FN_MIXED_TREE=$T FN_MIXED_IMAGE=$DEV FN_MIXED_OPENSSL=$OPENSSL_TEST \
      systemd-run --user --scope -q -p MemoryMax=40G -p MemorySwapMax=0 -- taskset -c "$F4_CORES" \
      python3 "$H/mixed.py" "$W/f4" "$F4_SECONDS" > "$O/f4-mixed.out" 2>&1
    rc=$?; cp "$W/f4/mixed.json" "$O/f4-mixed.json" 2>/dev/null; done_ f4 $rc; rm -rf "$W/f4" ) &
  F4PID=$! ;;
wait)
  [ -z "$F4PID" ] || wait "$F4PID"; F4PID= ;;
f4s)
  # The stall case (F4-R "regardless of the disk's state"): tests.test_native_slow_disk
  # pinned where the hour ran, its measurement line kept.
  box f4s
  env FN_NATIVE_DEVELOPER_HOST="$DEV" systemd-run --user --scope -q -p MemoryMax=24G -p MemorySwapMax=0 -- \
    taskset -c "$F4_CORES" python3 -m unittest -v tests.test_native_slow_disk > "$O/f4-stall.log" 2>&1
  done_ f4s $? ;;
f5) for i in 1 2; do
      box "f5-$i"; rm -rf "$W/mux"
      scope 24G "$ROW_CORES" python3 tools/mux_measure.py "$DEV" "$W/mux" --idle 1000 --active 200 --overs 10 --posts 50 > "$O/f5-mux-$i.json" 2> "$O/f5-mux-$i.err"
      done_ "f5-$i" $?; rm -rf "$W/mux"
    done ;;
f5n) module f5-native-mux tests.test_native_mux ;;
f8) box f8; scope 8G "$ROW_CORES" python3 "$H/floor.py" "$T" "$PROD" "$W/f8" --posts 1000 --octets 2048 > "$O/f8-floor-prod.json" 2> "$O/f8-floor-prod.err"
    done_ f8 $?; rm -rf "$W/f8" ;;
f1) for spec in a1000x2048:"--posts 1000 --octets 2048" a1000x8000:"--posts 1000 --octets 8000" a2000x2048:"--posts 2000 --octets 2048"; do
      n=${spec%%:*}; args=${spec#*:}
      box "f1-$n"
      # shellcheck disable=SC2086
      scope 8G "$ROW_CORES" python3 "$H/slope.py" "$T" "$PROF" "$W/f1-$n" $args > "$O/f1-slope-$n.json" 2> "$O/f1-slope-$n.err"
      done_ "f1-$n" $?; rm -rf "$W/f1-$n"
    done ;;
f6) for fx in chain-20000 t40k-2k-cp5; do
      for mode in asis reckpt; do
        box "f6-$fx-$mode"; rm -rf "$W/f6"
        scope 40G "$ROW_CORES" python3 "$H/reopen_ckpt.py" "$T" "$PROF" "$FX/$fx" "$W/f6" "$O/f6-$fx-$mode.json" "$mode" > "$O/f6-$fx-$mode.out" 2> "$O/f6-$fx-$mode.err"
        done_ "f6-$fx-$mode" $?; rm -rf "$W/f6"
      done
    done ;;
f6c) box f6c; rm -rf "$O/f6-curve"
    python3 "$T/tools/scale_curve.py" run --image "$PROD" --tree "$T" --probes open_replay,checkpoint,open_checkpoint \
      --jobs 1 --cores 4 --first-core "${ROW_CORES%%-*}" --work /dev/shm --out "$O/f6-curve" > "$O/f6-curve.out" 2>&1
    done_ f6c $? ;;
f3) for fs in nvme tank; do
      if [ $fs = nvme ]; then D=/var/tmp/fundamentals-$(basename "$(dirname "$O")")/gc-$fs; S=30; else D=/tank/fn/scratch/fundamentals/$(basename "$(dirname "$O")")/gc-$fs; S=60; fi
      rm -rf "$D"; mkdir -p "$(dirname "$D")"
      box "f3-$fs"
      FN_TREE=$T scope 110G "$ROW_CORES" python3 "$H/gc_measure.py" --image "$DEV" --dir "$D" --json "$O/f3-gc-$fs.json" --label $fs --seconds $S --connections 1,8,32 --fsync-posts 64 > "$O/f3-gc-$fs.log" 2>&1
      done_ "f3-$fs" $?; rm -rf "$D"
    done
    if [ -n "${EDGE_SSH:-}" ]; then
      box f3-edge
      ssh -n -o BatchMode=yes "$EDGE_SSH" "cd fn-fundamentals && python3 tools/fundamentals/gc_measure.py --image \$PWD/build/fn-host-developer --dir \$HOME/fn-fundamentals-gc --json /dev/stdout --label edge --seconds 60 --connections 1,8 --fsync-posts 64" > "$O/f3-gc-edge.json" 2> "$O/f3-gc-edge.log"
      done_ f3-edge $?
    fi ;;
f2) box f2-load; rm -rf "$W/f2"; mkdir -p "$W/f2"
    scope 40G "$ROW_CORES" python3 "$H/sr_measure.py" --image "$DEV" --fixture fresh --work "$W/f2/l" --articles 10000 --keep-store "$W/f2/fx" --json "$O/f2-load.json" > "$O/f2-load.out" 2>&1
    done_ f2-load $?
    for i in 1 2; do
      for side in before after; do
        if [ $side = before ]; then I=${F2_BEFORE:-}; [ -n "$I" ] || continue; else I=$DEV; fi
        box "f2-$side-$i"
        scope 40G "$ROW_CORES" python3 "$H/sr_measure.py" --image "$I" --fixture "$W/f2/fx" --work "$W/f2/$side-$i" --articles 10000 --client bulk --json "$O/f2-$side-$i.json" > "$O/f2-$side-$i.out" 2>&1
        done_ "f2-$side-$i" $?; rm -rf "$W/f2/$side-$i"
      done
    done
    # The lookups per served command (FN_NATIVE_COUNT_LOOKUPS): a fresh 1,000-post
    # store, then the kept 10,000-article store; the before image at 10,000.
    box f2-lookups-1000
    scope 40G "$ROW_CORES" python3 "$H/f2_lookups.py" --image "$DEV" --work "$W/f2/k1000" --articles 1000 --json "$O/f2-lookups-1000.json" > "$O/f2-lookups-1000.out" 2>&1
    done_ f2-lookups-1000 $?; rm -rf "$W/f2/k1000"
    for side in after before; do
      if [ $side = before ]; then I=${F2_BEFORE:-}; [ -n "$I" ] || continue; J=$O/f2-lookups-before-10000; else I=$DEV; J=$O/f2-lookups-10000; fi
      box "f2-lookups-$side-10000"
      scope 40G "$ROW_CORES" python3 "$H/f2_lookups.py" --image "$I" --work "$W/f2/k10000-$side" --store-from "$W/f2/fx/store" --articles 10000 --json "$J.json" > "$J.out" 2>&1
      done_ "f2-lookups-$side-10000" $?; rm -rf "$W/f2/k10000-$side"
    done
    rm -rf "$W/f2" ;;
f7) for img in dtn dtn-developer; do
      module "f7-bp-$img" tests.test_bp_fragment_node_native FN_NATIVE_DEVELOPER_HOST="$T/build/fn-host-$img"
    done ;;
*) echo "rows.sh: unknown step $step" >&2 ;;
esac
done
[ -z "$F4PID" ] || wait "$F4PID"
box end; echo "$(date -u +%FT%TZ) ROWS-DONE" >> "$O/driver.log"
rm -rf "$W"
