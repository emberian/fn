#!/bin/sh
# Run a release cut's mechanical gates in order; stop at the first red.
#
#   tools/cut_release.sh [--dry-run] [--rev REV] [--out DIR] [--from N]
#       [--runtime-from DIR] [--openbsd-host SSH --openbsd-root DIR]
#
# The checklist is planning/release-vVERSION.md (VERSION is the one line of
# the file VERSION at REV, 6.7.N); this script is its mechanical half, and
# each gate below is one of its numbered gates.  Run it from a clean
# checkout whose HEAD is REV (the coordinator's cut worktree), never the
# shared ~/dev/fn.  It writes OUT (default build/cut/vVERSION-REV12/):
# one log per gate and `verdict.txt', whose last line is
#
#   VERDICT GREEN vVERSION REV          every gate green
#   VERDICT RED at NN NAME              the first red gate; nothing after it ran
#   VERDICT DRY-RUN ...                 --dry-run (below)
#
# It creates no tag: the last gate prints the `git tag' command for the
# coordinator.  It never touches /tank/fn/node and deploys nothing.
#
# --dry-run runs the read-only local gates for real (version, tree,
# fundamentals, changelog, closure, docs, runpath: seconds, no box) and, for
# every other gate, writes the commands it would run (hbox_native.sh's own
# --dry-run for the native gate, which plans every module's environment
# without shipping anything); it does not stop at a red, so one dry run lists
# every red precondition, and the verdict names the first.
#
#   gate  what                                            where
#   01    version: VERSION is 6.7.N, tag vVERSION free    local
#         or at REV, N above every earlier v6.7.* tag
#   02    tree: HEAD is REV, no tracked change            local
#   03    fundamentals: every row of the checklist's      local
#         fundamentals table MET with evidence at REV
#   04    changelog: CHANGELOG.md is what                 local
#         tools/changelog.py writes at REV
#   05    closure: every book green at its digest         local
#         (green_check --strict, and --profile default)
#   06    make check (registries, current view,           local
#         proof cost, the throughput comparison)
#   07    docs_check --check                              local
#   08    runpath_check (static)                          local
#   09    the four images and every native module         hbox (hbox_native.sh)
#   10    the throughput gate, quiet (not --under-load)   hbox
#   11    the hostile campaign, every family              hbox
#   12    the Linux tarball: built from `git archive      hbox (+ debian:12)
#         REV' with the glibc-floor runtime, runpath
#         --tarball, installed fresh, test_release_tarball,
#         `fn --version' on Debian 12
#   13    the OpenBSD tarball: the same in the build VM   --openbsd-host
#   14    the power-loss cut list on the release image    hbox (sudo -n)
#   15    the friends session from the Linux tarball      hbox
#   16    the tag: print the command                      local
#
# Box paths: everything under /tank/fn/scratch/cut-VERSION/ (S); the native
# gate's tree is S/native-REV12/tree (T), whose build/ holds the four
# images the later gates use.  --from N resumes at gate N (the earlier
# gates' verdict lines are kept from OUT/verdict.txt).
set -u

usage() {
  echo 'usage: cut_release.sh [--dry-run] [--rev REV] [--out DIR] [--from N] [--runtime-from DIR] [--openbsd-host SSH --openbsd-root DIR]' >&2
  exit 2
}
DRY=no REV_ARG=HEAD OUT="" FROM=1
RUNTIME=/tank/fn/scratch/glibc-floor/runtime-2.6.8
OB_HOST="" OB_ROOT=""
HOST=${FN_HBOX:-hbox}
BOX_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
BOX_CACHE=/tank/fn/certcache
while [ "$#" -gt 0 ]; do
  case $1 in
    --dry-run) DRY=yes; shift ;;
    --rev) [ "$#" -ge 2 ] || usage; REV_ARG=$2; shift 2 ;;
    --out) [ "$#" -ge 2 ] || usage; OUT=$2; shift 2 ;;
    --from) [ "$#" -ge 2 ] || usage; FROM=$2; shift 2 ;;
    --runtime-from) [ "$#" -ge 2 ] || usage; RUNTIME=$2; shift 2 ;;
    --openbsd-host) [ "$#" -ge 2 ] || usage; OB_HOST=$2; shift 2 ;;
    --openbsd-root) [ "$#" -ge 2 ] || usage; OB_ROOT=$2; shift 2 ;;
    *) usage ;;
  esac
done
case $FROM in ''|*[!0-9]*) usage ;; esac

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT" || exit 2
REV=$(git rev-parse --verify -q "$REV_ARG^{commit}") || { echo "cut_release: no commit $REV_ARG" >&2; exit 2; }
SHORT=$(printf %s "$REV" | cut -c1-12)
VERSION=$(git show "$REV:VERSION" 2>/dev/null | sed -n 1p)
[ -n "$VERSION" ] || VERSION=none
OUT=${OUT:-$ROOT/build/cut/v$VERSION-$SHORT}
case $OUT in /*) ;; *) OUT=$ROOT/$OUT ;; esac
mkdir -p "$OUT"
V=$OUT/verdict.txt
S=/tank/fn/scratch/cut-$VERSION
T=$S/native-$SHORT/tree
CHECKLIST=planning/release-v$VERSION.md
PY=${PYTHON:-python3}

stamp() { date -u +%Y-%m-%dT%H:%M:%SZ; }
if [ "$FROM" -le 1 ] || [ ! -f "$V" ]; then
  {
    echo "cut v$VERSION at $REV"
    echo "mode $( [ "$DRY" = yes ] && echo dry-run || echo real ) started $(stamp) by tools/cut_release.sh"
  } > "$V"
else
  # Resume: keep the verdict lines of the gates before FROM.
  awk -v from="$FROM" '/^[0-9][0-9] / { if ($1 + 0 >= from) exit } { print }' "$V" > "$V.new" && mv "$V.new" "$V"
  echo "resumed at gate $FROM $(stamp)" >> "$V"
fi

FIRST_RED=
# box CMD: one shell command on hbox (never in a dry run).
box() { ssh -n -o BatchMode=yes "$HOST" "$1"; }
# box_script NAME TEXT: TEXT becomes S/NAME.sh on hbox (no quoting through
# ssh's command line); the caller runs `sh S/NAME.sh'.
box_script() { printf '%s\n' "$2" | ssh -o BatchMode=yes "$HOST" "mkdir -p $S && cat > $S/$1.sh"; }
would() { echo "would: $*"; }

# gate NN NAME FUNCTION: run it, log it, record it; stop on red unless dry.
gate() {
  nn=$1 name=$2 fn=$3
  [ "$nn" -ge "$FROM" ] || return 0
  log=$OUT/$nn-$name.log
  echo "== $nn $name"
  started=$(stamp)
  ( $fn ) > "$log" 2>&1
  rc=$?
  last=$(grep -v '^$' "$log" | tail -1 | cut -c1-200)
  case $rc in
    0) word=GREEN ;;
    10) word=DRY ;;
    *) word=RED ;;
  esac
  line="$nn $name $word ($started..$(stamp)): $last"
  echo "$line" >> "$V"
  echo "   $word: $last"
  if [ "$word" = RED ]; then
    [ -n "$FIRST_RED" ] || FIRST_RED="$nn $name"
    if [ "$DRY" = no ]; then
      echo "VERDICT RED at $nn $name (log $log)" >> "$V"
      echo "cut_release: RED at $nn $name; log $log; verdict $V" >&2
      exit 1
    fi
  fi
}

# ---------------------------------------------------------------- the gates

g_version() {
  case $VERSION in
    6.7.0) n=0 ;;
    6.7.[1-9]*) n=${VERSION#6.7.}; case $n in *[!0-9]*) echo "VERSION at $REV is '$VERSION', not 6.7.N"; return 1 ;; esac ;;
    *) echo "VERSION at $REV is '$VERSION', not 6.7.N"; return 1 ;;
  esac
  tagged=$(git rev-parse -q --verify "refs/tags/v$VERSION^{commit}" || true)
  if [ -n "$tagged" ] && [ "$tagged" != "$REV" ]; then
    echo "tag v$VERSION exists at $tagged, not $REV: bump VERSION"; return 1
  fi
  for t in $(git tag -l 'v6.7.*'); do
    [ "$t" = "v$VERSION" ] && continue
    m=${t#v6.7.}
    case $m in ''|*[!0-9]*) continue ;; esac
    if [ "$m" -ge "$n" ]; then echo "tag $t is not below v$VERSION: bump VERSION"; return 1; fi
  done
  [ -n "$(git show "$REV:$CHECKLIST" 2>/dev/null | head -1)" ] || { echo "no $CHECKLIST at $REV"; return 1; }
  echo "version $VERSION; tag v$VERSION $( [ -n "$tagged" ] && echo "at REV" || echo free ); checklist $CHECKLIST"
}

g_tree() {
  head=$(git rev-parse HEAD)
  dirty=$(git status --porcelain --untracked-files=no | head -5)
  [ -z "$dirty" ] || { echo "tracked changes:"; echo "$dirty"; }
  [ "$head" = "$REV" ] || echo "HEAD is $head, not REV $REV"
  if [ "$head" != "$REV" ] || [ -n "$dirty" ]; then
    echo "the cut runs in a clean checkout at REV (git worktree add --detach build/cut-tree $SHORT)"; return 1
  fi
  echo "clean checkout at $REV"
}

g_fundamentals() {
  # The table between the markers: | ID | fundamental | bar | STATUS | evidence |
  git show "$REV:$CHECKLIST" > "$OUT/checklist.md" 2>/dev/null || { echo "no $CHECKLIST at $REV"; return 1; }
  rows=$(awk '/<!-- fundamentals -->/{on=1; next} /<!-- end fundamentals -->/{on=0} on && /^\| *F[0-9]+ *\|/' "$OUT/checklist.md")
  [ -n "$rows" ] || { echo "no fundamentals table in $CHECKLIST"; return 1; }
  open=0 total=0
  echo "$rows" | {
    while IFS="|" read -r _ id what _bar status evidence _; do
      id=$(echo "$id" | tr -d ' ') status=$(echo "$status" | tr -d ' *')
      evidence=$(echo "$evidence" | sed 's/^ *//; s/ *$//; s/`//g')
      total=$((total + 1))
      if [ "$status" != MET ]; then
        open=$((open + 1)); echo "$id $status: $(echo "$what" | sed 's/^ *//; s/ *$//')"
      elif ! git cat-file -e "$REV:$evidence" 2>/dev/null; then
        open=$((open + 1)); echo "$id MET but its evidence '$evidence' is not in REV"
      fi
    done
    if [ "$open" -gt 0 ]; then echo "$open of $total fundamentals not met (blocking)"; exit 1; fi
    echo "all $total fundamentals met, each with its evidence at REV"
  }
}

g_changelog() {
  "$PY" tools/changelog.py --rev "$REV" > "$OUT/CHANGELOG.expected" || { echo "tools/changelog.py failed"; return 1; }
  git show "$REV:CHANGELOG.md" > "$OUT/CHANGELOG.committed" 2>/dev/null || { echo "no CHANGELOG.md at REV"; return 1; }
  if cmp -s "$OUT/CHANGELOG.expected" "$OUT/CHANGELOG.committed"; then
    echo "CHANGELOG.md is current at REV"
  else
    diff "$OUT/CHANGELOG.committed" "$OUT/CHANGELOG.expected" | head -20
    echo "CHANGELOG.md is stale at REV: python3 tools/changelog.py --write, commit, cut again"; return 1
  fi
}

g_closure() {
  "$PY" tools/green_check.py --strict --summary || { echo "a book is not green at its digest (green_check --strict)"; return 1; }
  "$PY" tools/green_check.py --profile default --strict || { echo "the default profile's closure is not green"; return 1; }
  echo "every book green at its digest; the default profile's closure green"
}

g_check() {
  if [ "$DRY" = yes ]; then would make check; return 10; fi
  make check || { echo "make check failed"; return 1; }
  echo "make check green"
}

g_docs() {
  "$PY" tools/docs_check.py --check || { echo "docs_check --check failed"; return 1; }
  echo "docs_check --check green"
}

g_runpath() {
  "$PY" tools/runpath_check.py --quiet || { echo "runpath_check (static) failed"; return 1; }
  echo "runpath_check (static) green"
}

# Every image-gated module: tests/test_*native*.py and tests/test_bp_*.py,
# less the `exclude' lines of planning/release-native-gate.txt; its `env'
# lines are the opt-ins the gate passes (NAME=VALUE, tab-separated).
NATIVE_GATE=planning/release-native-gate.txt
modules() {
  for f in $(git ls-tree --name-only "$REV" tests/ | grep -E '^tests/test_(.*native.*|bp_.*)\.py$'); do
    m=tests.$(basename "$f" .py)
    if git show "$REV:$NATIVE_GATE" 2>/dev/null | awk -F'\t' -v m="$m" '$1 == "exclude" && $2 == m { f = 1 } END { exit !f }'; then continue; fi
    printf '%s\n' "$m"
  done
}
gate_envs() {
  git show "$REV:$NATIVE_GATE" 2>/dev/null | awk -F'\t' '$1 == "env" { printf "--env %s ", $2 }'
}

g_native() {
  mods=$(modules | tr '\n' ' ')
  # shellcheck disable=SC2046
  set -- --name "cut-$VERSION" --label "$SHORT" --images developer,production,dtn,dtn-developer \
    --deadline 43200 $(gate_envs) "$REV"
  echo "modules ($(echo $mods | wc -w | tr -d ' ')): $mods"
  if [ "$DRY" = yes ]; then
    # shellcheck disable=SC2086
    sh tools/hbox_native.sh --dry-run "$@" $mods > "$OUT/native-dry-run.txt" 2>&1
    rc=$?
    tail -3 "$OUT/native-dry-run.txt"
    [ "$rc" -eq 0 ] || { echo "hbox_native.sh --dry-run refused (exit $rc; $OUT/native-dry-run.txt)"; return 1; }
    would sh tools/hbox_native.sh "$@" "<$(echo $mods | wc -w | tr -d ' ') modules>"
    return 10
  fi
  # shellcheck disable=SC2086
  sh tools/hbox_native.sh "$@" $mods
  rc=$?
  box "cat $S/native-$SHORT/run.log" > "$OUT/native-run.log" 2>&1
  grep '^== modules' "$OUT/native-run.log" || true
  [ "$rc" -eq 0 ] || { echo "hbox_native status $rc: a module FAILED or SKIPPED ($HOST:$S/native-$SHORT)"; return 1; }
  echo "four images built at REV; every module OK ($HOST:$S/native-$SHORT)"
}

g_throughput() {
  set -- run --image "$T/build/fn-host-developer" --revision "$REV" --label "cut-$VERSION" --wait-quiet 1800
  if [ "$DRY" = yes ]; then would "$PY" tools/throughput_gate.py "$@"; would "$PY" tools/throughput_gate.py check; return 10; fi
  "$PY" tools/throughput_gate.py "$@" || { echo "the throughput run failed (a box never quiet refuses: exit 3)"; return 1; }
  "$PY" tools/throughput_gate.py check || { echo "the throughput gate regressed against planning/throughput-baseline.json"; return 1; }
  echo "throughput gate quiet and within the baseline (planning/evidence/throughput/$SHORT-cut-$VERSION*.json)"
}

g_hostile() {
  cmd="cd $T && python3 tools/hostile_campaign.py --image $T/build/fn-host-developer --evidence $S/hostile --report $S/hostile/report.json --mem 8G"
  if [ "$DRY" = yes ]; then would "ssh $HOST '$cmd'"; return 10; fi
  box "mkdir -p $S/hostile && $cmd" > "$OUT/hostile.out" 2>&1
  rc=$?
  tail -5 "$OUT/hostile.out"
  [ "$rc" -eq 0 ] || { echo "the hostile campaign found a defect or failed (exit $rc; $HOST:$S/hostile/report.json)"; return 1; }
  echo "hostile campaign: every family, no defect"
}

g_tarball_linux() {
  tb=fn-$VERSION-linux-x86_64.tar.gz
  script="set -eu
[ ! -e $S/release ] || { echo 'exists: $S/release'; exit 4; }
[ -x $RUNTIME/sbcl ] || { echo 'no glibc-floor runtime $RUNTIME'; exit 4; }
mkdir -p $S/release-work $S/fresh
cd $T
FN_CERT_CACHE=$BOX_CACHE FN_ACL2=$BOX_ACL2 sh packaging/release-tarball.sh --runtime-from $RUNTIME linux-x86_64 $REV $S/release $S/source.tar
python3 tools/runpath_check.py --tarball $S/release/$tb
cd $S/fresh && cp $S/release/$tb $S/release/SHA256SUMS . && sha256sum -c --ignore-missing SHA256SUMS
tar xzf $tb && sh fn/install.sh --prefix $S/fresh/opt/fn --node $S/fresh/node --no-service
cd $T && FN_RELEASE_TARBALL=$S/release/$tb python3 -m unittest -v tests.test_release_tarball 2> $S/release-test.log; tail -1 $S/release-test.log
[ \"\$(tail -1 $S/release-test.log)\" = OK ] || { echo 'test_release_tarball: not OK with no skips'; exit 1; }
docker run --rm -v $S/release:/r:ro debian:12 sh -c 'apt-get update -qq >/dev/null && apt-get install -y -qq libssl3 >/dev/null && cd /tmp && tar xzf /r/$tb && fn/bin/fn --version' > $S/debian12-version.txt
[ \"\$(cat $S/debian12-version.txt)\" = 'fn $VERSION ($SHORT)' ] || { echo \"Debian 12: \$(cat $S/debian12-version.txt)\"; exit 1; }
grep -F $tb $S/release/SHA256SUMS"
  if [ "$DRY" = yes ]; then
    would "git archive --format=tar $REV | ssh $HOST 'cat > $S/source.tar'"
    echo "$script" | sed 's/^/would (hbox): /'
    return 10
  fi
  git archive --format=tar "$REV" | ssh -o BatchMode=yes "$HOST" "mkdir -p $S && cat > $S/source.tar" || { echo "shipping the archive failed"; return 1; }
  box_script tarball-linux "$script" || { echo "shipping the gate script failed"; return 1; }
  box "sh $S/tarball-linux.sh" || { echo "the Linux tarball gate failed"; return 1; }
  echo "$tb built, runpath clean, installed fresh, test_release_tarball OK, Debian 12 prints fn $VERSION ($SHORT)"
}

g_tarball_openbsd() {
  tb=fn-$VERSION-openbsd-amd64.tar.gz
  if [ -z "$OB_HOST" ] || [ -z "$OB_ROOT" ]; then
    echo "no --openbsd-host/--openbsd-root: the OpenBSD tarball is not built (the build VM of planning/evidence/release-openbsd-2026-09-26.md section 2)"
    return 1
  fi
  R=$OB_ROOT/cut-$VERSION
  script="set -eu
[ ! -e $R/release ] || { echo 'exists: $R/release'; exit 4; }
mkdir -p $R/src $R/fresh && tar -xf $R/source.tar -C $R/src && cd $R/src
: \${FN_CERT_CACHE:?} \${FN_ACL2:?}
sh packaging/release-tarball.sh openbsd-amd64 $REV $R/release $R/source.tar
python3 tools/runpath_check.py --tarball $R/release/$tb
cd $R/fresh && cp $R/release/$tb $R/release/SHA256SUMS . && sha256 -C SHA256SUMS $tb
tar xzf $tb && sh fn/install.sh --prefix $R/fresh/usr/local/fn --node $R/fresh/var/fn --no-service
cd $R/src && FN_RELEASE_TARBALL=$R/release/$tb python3 -m unittest -v tests.test_release_tarball 2> $R/release-test.log; tail -1 $R/release-test.log
[ \"\$(tail -1 $R/release-test.log)\" = OK ] || { echo 'test_release_tarball: not OK with no skips'; exit 1; }
sha256 $R/release/$tb"
  if [ "$DRY" = yes ]; then
    would "git archive --format=tar $REV | ssh $OB_HOST 'cat > $R/source.tar'"
    echo "$script" | sed 's/^/would (openbsd): /'
    return 10
  fi
  git archive --format=tar "$REV" | ssh -o BatchMode=yes "$OB_HOST" "mkdir -p $R && cat > $R/source.tar" || { echo "shipping the archive failed"; return 1; }
  printf '%s\n' "$script" | ssh -o BatchMode=yes "$OB_HOST" "cat > $R/gate.sh" || { echo "shipping the gate script failed"; return 1; }
  ssh -n -o BatchMode=yes "$OB_HOST" "sh $R/gate.sh" || { echo "the OpenBSD tarball gate failed"; return 1; }
  echo "$tb built in the VM, runpath clean, installed fresh, test_release_tarball OK"
}

g_power_loss() {
  img=$S/fresh/opt/fn/libexec/fn/fn-host
  W=$S/power-loss
  C="python3 $T/tools/power_loss.py"
  script="set -eu
[ -x $img ] || { echo 'no installed release image $img (gate 12)'; exit 4; }
sudo -n true || { echo 'power-loss needs sudo -n on $HOST for the block layer'; exit 4; }
$C rig-up $W --data-mib 1024 --log-mib 16384
$C workload $W --image $img --posts 600 --conn 10 --open-suffix 64 --octets 700,2048,3800 --refuse-every 25 --seed 30
$C rig-down $W
$C index $W
$C cuts $W --image $img --plan init=8,post=150,checkpoint=60,compact=60,reclaim=50,control=8 --recover-crash 0.2 --seed 930 --label cut
$C summary $W/cuts-*.jsonl | tee $W/summary.md"
  if [ "$DRY" = yes ]; then echo "$script" | sed 's/^/would (hbox, in a systemd-run --user unit): /'; return 10; fi
  box_script power-loss "$script" || { echo "shipping the gate script failed"; return 1; }
  box "systemd-run --user --scope -q -p MemoryMax=24G sh $S/power-loss.sh" > "$OUT/power-loss.out" 2>&1
  rc=$?
  tail -3 "$OUT/power-loss.out"
  [ "$rc" -eq 0 ] || { echo "the power-loss campaign did not complete (exit $rc)"; return 1; }
  # | all | all | cuts | violations | controls_caught | ... | harness_error |
  grep '^| all | all |' "$OUT/power-loss.out" | awk -F'|' '{
    v = $5 + 0; c = $6 + 0; h = $(NF - 1) + 0
    printf "cuts %d, violations %d, controls caught %d, harness errors %d\n", $4, v, c, h
    exit !(v == 0 && c > 0 && h == 0) }' || { echo "power-loss: a violation, an uncaught control or a harness error"; return 1; }
}

g_friends() {
  cmd="cd $T && FN_NATIVE_HOST=$T/build/fn-host-developer FN_FRIEND_FN=$S/fresh/opt/fn/bin/fn systemd-run --user --scope -q -p MemoryMax=24G python3 -m unittest -v tests.test_native_friends_feed"
  if [ "$DRY" = yes ]; then would "ssh $HOST '$cmd'"; return 10; fi
  box "$cmd" > "$OUT/friends.out" 2>&1
  rc=$?
  tail -3 "$OUT/friends.out"
  [ "$rc" -eq 0 ] && [ "$(grep -v '^$' "$OUT/friends.out" | tail -1)" = OK ] || {
    echo "the friends session from the tarball is not OK with no skips (exit $rc)"; return 1; }
  echo "friends session: the friend's node on the release tarball's bin/fn, OK"
}

g_tag() {
  echo "for the coordinator, at the cut: git tag -a v$VERSION -m 'fn $VERSION' $REV && git push origin v$VERSION"
  [ "$DRY" = yes ] && return 10
  return 0
}

gate 01 version g_version
gate 02 tree g_tree
gate 03 fundamentals g_fundamentals
gate 04 changelog g_changelog
gate 05 closure g_closure
gate 06 check g_check
gate 07 docs g_docs
gate 08 runpath g_runpath
gate 09 native g_native
gate 10 throughput g_throughput
gate 11 hostile g_hostile
gate 12 tarball-linux g_tarball_linux
gate 13 tarball-openbsd g_tarball_openbsd
gate 14 power-loss g_power_loss
gate 15 friends g_friends
gate 16 tag g_tag

if [ "$DRY" = yes ]; then
  echo "VERDICT DRY-RUN v$VERSION $REV: first red ${FIRST_RED:-none} ($(stamp))" >> "$V"
else
  echo "VERDICT GREEN v$VERSION $REV ($(stamp))" >> "$V"
fi
tail -1 "$V"
echo "verdict: $V"
