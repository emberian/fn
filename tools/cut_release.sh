#!/bin/sh
# Run a release cut's mechanical gates in order; stop at the first red.
#
#   tools/cut_release.sh [--dry-run] [--rev REV] [--out DIR] [--from N]
#       [--to N] [--runtime-from DIR] [--openbsd-vm NAME]
#
# The checklist is planning/release-vVERSION.md (VERSION is the one line of
# the file VERSION at REV, an entry of planning/release-sequence.json, D37);
# this script is its mechanical half, and
# each gate below is one of its numbered gates.  Run it from a clean
# checkout whose HEAD is REV (the coordinator's cut worktree), never the
# shared ~/dev/fn.  It writes OUT (default build/cut/vVERSION-REV12/):
# one log per gate and `verdict.txt', whose last line is
#
#   VERDICT GREEN vVERSION REV          every gate green
#   VERDICT RED at NN NAME              the first red gate; nothing after it ran
#   VERDICT DRY-RUN ...                 --dry-run (below)
#   VERDICT PARTIAL ...                 --to N below 17: gates FROM..N green
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
#   01    version: VERSION is the next entry of the       local
#         release sequence after the newest v* tag (by
#         sequence position, never by number; the first
#         entry, 6.6.0, when there is none), its tag free
#         or at REV (tools/release_sequence.py cut-check)
#   02    tree: HEAD is REV, no tracked change            local
#   03    fundamentals: every row of the checklist's      local
#         fundamentals table MET with evidence at REV
#   04    changelog: CHANGELOG.md is what                 local
#         tools/changelog.py writes at REV, and what it
#         writes survives its own commit byte for byte
#   05    closure: every book green at its digest         local
#         (green_check --strict, and --profile default)
#   06    make check (registries, current view,           local
#         proof cost, the throughput comparison)
#   07    docs_check --check                              local
#   08    runpath_check (static)                          local
#   09    the six images and every native module          hbox (hbox_native.sh)
#   10    the throughput gate, quiet (not --under-load)   hbox
#   11    the hostile campaign, every family              hbox
#   12    the Linux tarball: built from `git archive      hbox (+ debian:12)
#         REV' with the glibc-floor runtime, runpath
#         --tarball, installed fresh, test_release_tarball,
#         `fn --version' on Debian 12
#   13    the OpenBSD tarball: the same in the build VM,  hbox (the VM)
#         and the installed `fn --version' 
#   14    the power-loss cut list on the release image    hbox (sudo -n)
#   15    the friends session from the Linux tarball      hbox
#   16    extract-check: `make extract-check' (the        local
#         N-version differential) when REV has the
#         target; SKIPPED until then
#   17    the tag: print the command                      local
#
# Box paths: everything under /tank/fn/scratch/cut-VERSION-REV12/ (S); the native
# gate's tree is S/native-REV12/tree (T), whose build/ holds the six
# images the later gates use (fn-host, fn-host-developer, fn-host-dtn,
# fn-host-dtn-developer, and tests.test_native_image_differential's pair:
# fn-host-reference, fn-host-developer-stripped).  --from N resumes at gate
# N (the earlier gates' verdict lines are kept from OUT/verdict.txt); --to N
# stops after gate N (VERDICT PARTIAL: one gate, or a prefix, run for real).
#
# The OpenBSD build VM (gate 13).  A configuration of
# tools/power_loss_openbsd.py on hbox: OB_BASE/NAME/cfg.json and its raw
# disks, NAME `cutbld' by default (--openbsd-vm), OB_BASE
# /tank/fn/scratch/power-loss-openbsd: the cut's own VM, so a lane using a
# sibling VM never blocks a cut.  Its root disk is a raw copy of
# OB_BASE/vm/root-base.qcow2, the release-openbsd install (OpenBSD 7.9
# amd64, syspatch 002-021; pkg sbcl 2.6.3, libsodium 1.0.22, python 3.13,
# bash, gmake; ACL2 8.7 and its certified system books under
# /usr/local/fn-work).  The gate writes its own literal ACL2 launcher there
# (4 GiB heap, --tls-limit 65536 as hbox's image builds since batch AV).
# Its second disk is the build space, FFS2 on sd1a, mounted
# wxallowed at /bw.  qemu runs in the fn-openbsd-qemu:local container with
# /dev/kvm; root logs in with OB_BASE/vm/id_ed25519 on 127.0.0.1:PORT
# (cfg.json's `ssh').  Provisioned once on hbox (2026-09-27, lane
# release-machinery), as openbsd-release-fixes provisioned its orfbld
# (planning/evidence/openbsd-release-fixes-2026-09-27.md section 1):
#   python3 tools/power_loss_openbsd.py prepare cutbld --cache writeback \
#     --ssh 2293 --nntp 11693 --smp 8 --mem 7168 --store-size 48G \
#     --format raw --ffs 2
# then, in the guest, root's login class lifted past the 4 GiB heap (the
# `daemon' class caps datasize at 4096M; SBCL's 4096 MB dynamic space plus
# the runtime does not fit: "mmap: Cannot allocate memory"):
#   sed -i '/^daemon:/,/^$/s/:datasize=4096M:/:datasize=infinity:/' /etc/login.conf
# (a build VM only; a node keeps its class).
# The gate boots it (`power_loss_openbsd.py start', refused if it is
# already running: someone else's), certifies REV's default closure in the
# guest into a cache of the cut's own, builds the tarball with
# packaging/release-tarball.sh, runs runpath --tarball, installs it fresh,
# runs tests.test_release_tarball, checks the installed `fn --version' under
# root's own login limits, copies the tarball and the logs to S/openbsd/out
# and shuts the VM down (`stop', on every exit).
set -u

usage() {
  echo 'usage: cut_release.sh [--dry-run] [--rev REV] [--out DIR] [--from N] [--to N] [--runtime-from DIR] [--openbsd-vm NAME]' >&2
  exit 2
}
DRY=no REV_ARG=HEAD OUT="" FROM=1 TO=17
RUNTIME=/tank/fn/scratch/glibc-floor/runtime-2.6.8
OB_VM=cutbld OB_BASE=/tank/fn/scratch/power-loss-openbsd
HOST=${FN_HBOX:-hbox}
BOX_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
BOX_CACHE=/tank/fn/certcache
while [ "$#" -gt 0 ]; do
  case $1 in
    --dry-run) DRY=yes; shift ;;
    --rev) [ "$#" -ge 2 ] || usage; REV_ARG=$2; shift 2 ;;
    --out) [ "$#" -ge 2 ] || usage; OUT=$2; shift 2 ;;
    --from) [ "$#" -ge 2 ] || usage; FROM=$2; shift 2 ;;
    --to) [ "$#" -ge 2 ] || usage; TO=$2; shift 2 ;;
    --runtime-from) [ "$#" -ge 2 ] || usage; RUNTIME=$2; shift 2 ;;
    --openbsd-vm) [ "$#" -ge 2 ] || usage; OB_VM=$2; shift 2 ;;
    *) usage ;;
  esac
done
case $FROM$TO in ''|*[!0-9]*) usage ;; esac
case $OB_VM in ''|*[!A-Za-z0-9_-]*) usage ;; esac

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
S=/tank/fn/scratch/cut-$VERSION-$SHORT
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
SKIPS=
# box CMD: one shell command on hbox (never in a dry run).
box() { ssh -n -o BatchMode=yes "$HOST" "$1"; }
# box_script NAME TEXT: TEXT becomes S/NAME.sh on hbox (no quoting through
# ssh's command line); the caller runs `sh S/NAME.sh'.
box_script() { printf '%s\n' "$2" | ssh -o BatchMode=yes "$HOST" "mkdir -p $S && cat > $S/$1.sh"; }
would() { echo "would: $*"; }

# gate NN NAME FUNCTION: run it, log it, record it; stop on red unless dry.
gate() {
  nn=$1 name=$2 fn=$3
  [ "$nn" -ge "$FROM" ] && [ "$nn" -le "$TO" ] || return 0
  log=$OUT/$nn-$name.log
  echo "== $nn $name"
  started=$(stamp)
  ( $fn ) > "$log" 2>&1
  rc=$?
  last=$(grep -v '^$' "$log" | tail -1 | cut -c1-200)
  case $rc in
    0) word=GREEN ;;
    10) word=DRY ;;
    11) word=SKIPPED ;;
    *) word=RED ;;
  esac
  line="$nn $name $word ($started..$(stamp)): $last"
  echo "$line" >> "$V"
  echo "   $word: $last"
  [ "$word" != SKIPPED ] || SKIPS="$SKIPS $nn"
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
  # Release order is D37's sequence (planning/release-sequence.json), never a
  # numeric comparison: tools/release_sequence.py decides it.
  tagged=$(git rev-parse -q --verify "refs/tags/v$VERSION^{commit}" || true)
  if [ -n "$tagged" ] && [ "$tagged" != "$REV" ]; then
    echo "tag v$VERSION exists at $tagged, not $REV: VERSION must be the next entry of the sequence"; return 1
  fi
  # shellcheck disable=SC2046
  "$PY" tools/release_sequence.py cut-check "$VERSION" $(git tag -l 'v*') || return 1
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
  # What changelog.py writes at REV must be the committed file, and must
  # survive its own commit: the file is committed as a direct commit after
  # the last lane merge, so REV + that file regenerates byte for byte.  The
  # scratch commit below (git commit-tree onto REV, no ref moved, nothing
  # checked out) is that check, made whether or not REV's file is current.
  "$PY" tools/changelog.py --rev "$REV" > "$OUT/CHANGELOG.expected" || { echo "tools/changelog.py failed"; return 1; }
  "$PY" tools/changelog.py --rev "$REV" | cmp -s - "$OUT/CHANGELOG.expected" || { echo "tools/changelog.py is not deterministic at REV"; return 1; }
  blob=$(git hash-object -w "$OUT/CHANGELOG.expected") &&
  tree=$(git ls-tree "$REV" | awk -v b="$blob" -F'\t' '$2 != "CHANGELOG.md" { print } END { printf "100644 blob %s\tCHANGELOG.md\n", b }' | git mktree) &&
  scratch=$(echo "changelog stability check" | git commit-tree "$tree" -p "$REV") || { echo "the scratch commit failed"; return 1; }
  "$PY" tools/changelog.py --rev "$scratch" > "$OUT/CHANGELOG.after-commit" || { echo "tools/changelog.py failed at the scratch commit"; return 1; }
  if ! cmp -s "$OUT/CHANGELOG.expected" "$OUT/CHANGELOG.after-commit"; then
    diff "$OUT/CHANGELOG.expected" "$OUT/CHANGELOG.after-commit" | head -10
    echo "CHANGELOG.md is not byte-stable across its own commit ($scratch): tools/changelog.py's range"; return 1
  fi
  echo "regenerated at REV: byte-stable across its own commit (scratch $(printf %s "$scratch" | cut -c1-12))"
  git show "$REV:CHANGELOG.md" > "$OUT/CHANGELOG.committed" 2>/dev/null || { echo "no CHANGELOG.md at REV"; return 1; }
  if cmp -s "$OUT/CHANGELOG.expected" "$OUT/CHANGELOG.committed"; then
    echo "CHANGELOG.md is current at REV"
  else
    diff "$OUT/CHANGELOG.committed" "$OUT/CHANGELOG.expected" | head -20
    echo "CHANGELOG.md is stale at REV: python3 tools/changelog.py --write && git commit CHANGELOG.md; that commit is the cut's REV"; return 1
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
  set -- --name "cut-$VERSION-$SHORT" --label "$SHORT" --images developer,production,dtn,dtn-developer,reference,developer-stripped \
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
  echo "six images built at REV; every module OK ($HOST:$S/native-$SHORT)"
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
    box "test -x $RUNTIME/sbcl" || { echo "no glibc-floor runtime $HOST:$RUNTIME (--runtime-from)"; return 1; }
    box "docker image inspect debian:12 >/dev/null 2>&1" || echo "note: debian:12 is not pulled on $HOST (the gate pulls it)"
    echo "preconditions on $HOST: the glibc-floor runtime $RUNTIME"
    return 10
  fi
  git archive --format=tar "$REV" | ssh -o BatchMode=yes "$HOST" "mkdir -p $S && cat > $S/source.tar" || { echo "shipping the archive failed"; return 1; }
  box_script tarball-linux "$script" || { echo "shipping the gate script failed"; return 1; }
  box "sh $S/tarball-linux.sh" || { echo "the Linux tarball gate failed"; return 1; }
  echo "$tb built, runpath clean, installed fresh, test_release_tarball OK, Debian 12 prints fn $VERSION ($SHORT)"
}

g_tarball_openbsd() {
  tb=fn-$VERSION-openbsd-amd64.tar.gz
  B=$OB_BASE R=$S/openbsd W=/bw/cut-$VERSION
  cfg=$B/$OB_VM/cfg.json
  # The guest half (OpenBSD ksh, as root): certify REV's default closure into
  # a cache of its own, build the tarball from the archive, check it, install
  # it fresh.  The release-openbsd / openbsd-release-fixes recipe
  # (planning/evidence/openbsd-release-fixes-2026-09-27.md section 1).
  guest="set -e
mount | grep -q ' /bw '
ulimit -d \$(ulimit -H -d)
[ \$(ulimit -d) = unlimited ] || [ \$(ulimit -d) -ge 6291456 ] || { echo \"datasize \$(ulimit -d) KiB: under the 4 GiB heap plus runtime; lift root's login class (tools/cut_release.sh header)\"; exit 1; }
L=/usr/local/fn-work/acl2-lit-4g-tls64k
printf '%s\\n' '#!/bin/sh' 'export SBCL_HOME=/usr/local/lib/sbcl/' 'exec /usr/local/bin/sbcl --tls-limit 65536 --dynamic-space-size 4096 --control-stack-size 64 --disable-ldb --core /usr/local/fn-work/acl2-8.7/saved_acl2.core --end-runtime-options --no-userinit --eval \"(acl2::sbcl-restart)\" \"\$@\"' > \$L
chmod 0755 \$L
export FN_ACL2=\$L ACL2_SYSTEM_BOOKS=/usr/local/fn-work/acl2-8.7/books
export FN_ACL2_SLOTS=7 FN_ACL2_TIMEOUT_SECONDS=3000 FN_CERT_CACHE=$W/certcache
rm -rf $W/cert $W/certified $W/src $W/certcache $W/release $W/fresh; mkdir -p $W/cert $W/certcache $W/release $W/fresh
cd $W/cert && tar -xf $W/source.tar
echo \"== certify \$(date -u +%FT%TZ)\"
python3 tools/certify_books.py --jobs 7 --closure \$(python3 tools/proof_artifacts.py roots --profile default) > $W/certify.log 2>&1 || { grep -v '^ACL2 did not produce' $W/certify.log | tail -5; grep -o 'Books that failed: [^,]*, [^,]*, [^,]*' $W/certify.log; exit 1; }
# A live certifying tree is not an origin another target may use while it
# exists (certs.usable_origin): moved aside, and the release runs from an
# extraction at another path.
cd $W && mv cert certified && mkdir src && cd src && tar -xf $W/source.tar
echo \"== release \$(date -u +%FT%TZ)\"
FN_FREEZE_SODIUM=/usr/local/lib/libsodium.so.11.1 FN_FREEZE_DYNAMIC_SPACE_MB=1024 sh packaging/release-tarball.sh openbsd-amd64 $REV $W/release $W/source.tar > $W/release.log 2>&1 || { tail -15 $W/release.log; exit 1; }
tail -4 $W/release.log
python3 tools/runpath_check.py --tarball $W/release/$tb
cd $W/fresh && cp $W/release/$tb $W/release/SHA256SUMS . && sha256 -C SHA256SUMS $tb
tar xzf $tb && sh fn/install.sh --prefix $W/fresh/usr/local/fn --node $W/fresh/var/fn --no-service > $W/install.log 2>&1 || { tail -5 $W/install.log; exit 1; }
# The test installs under TMPDIR: an OpenBSD image maps its core RWX, so
# that is a wxallowed file system (/bw), as /usr/local is on a node.  Its one
# skip here is the Linux-only glibc-floor case; any other skip is red.
mkdir -p $W/tmp && cd $W/src && TMPDIR=$W/tmp FN_RELEASE_TARBALL=$W/release/$tb python3 -m unittest -v tests.test_release_tarball 2> $W/release-test.log; tail -1 $W/release-test.log
case \"\$(tail -1 $W/release-test.log)\" in 'OK'|'OK (skipped=1)') ;; *) grep -E '^(FAIL|ERROR)' $W/release-test.log | head; echo 'test_release_tarball: not OK'; exit 1 ;; esac
[ \$(grep -c ' skipped ' $W/release-test.log) -eq \$(grep -c ' skipped .the glibc floor is the Linux release' $W/release-test.log) ] || { grep ' skipped ' $W/release-test.log; echo 'test_release_tarball: a skip other than the glibc floor'; exit 1; }
echo \"== done \$(date -u +%FT%TZ)\""
  # The box half (hbox): the VM up, the archive in, the guest half, the
  # smoke under root's own login limits, the evidence out, the VM down.
  script="set -u
B=$B VM=$OB_VM R=$R
[ -f $cfg ] || { echo 'no OpenBSD build VM $OB_VM ($cfg): see the header of tools/cut_release.sh'; exit 4; }
[ -f $S/source.tar ] || { echo 'no archive $S/source.tar'; exit 4; }
rm -rf $R; mkdir -p $R/src $R/out && tar -xf $S/source.tar -C $R/src tools || exit 4
PORT=\$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))[\"ssh\"])' $cfg)
vm() { ssh -p \$PORT -i $B/vm/id_ed25519 -o BatchMode=yes -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR -o ServerAliveInterval=30 root@127.0.0.1 \"\$@\"; }
python3 $R/src/tools/power_loss_openbsd.py --base $B start $OB_VM || exit 4
trap 'python3 $R/src/tools/power_loss_openbsd.py --base $B stop $OB_VM' EXIT
vm 'mount | grep -q \" /bw \" || { rm -rf /bw; mkdir -p /bw && mount -o wxallowed /dev/sd1a /bw; }; mount | grep -q \" /bw \" && rm -rf $W && mkdir -p $W' || { echo 'the build space /bw (sd1a) did not mount'; exit 4; }
vm 'cat > $W/source.tar' < $S/source.tar || exit 4
vm 'cat > $W/gate.sh' < $S/openbsd-guest.sh || exit 4
vm 'ksh $W/gate.sh'; rc=\$?
for f in certify.log release.log install.log release-test.log; do vm \"cat $W/\$f\" > $R/out/\$f 2>/dev/null; done
vm 'cat $W/release/SHA256SUMS' > $R/out/SHA256SUMS 2>/dev/null
vm 'cat $W/release/$tb' > $R/out/$tb 2>/dev/null
[ \$rc -eq 0 ] || { echo \"the guest half failed (exit \$rc; logs in $R/out)\"; exit 1; }
v=\$(vm '$W/fresh/usr/local/fn/bin/fn --version' 2>&1)
echo \"fn --version (root's login limits: \$(vm 'ulimit -d')): \$v\"
[ \"\$v\" = 'fn $VERSION ($SHORT)' ] || { echo \"the installed fn --version is not 'fn $VERSION ($SHORT)'\"; exit 1; }
# A node keeps OpenBSD's stock daemon class (datasize 4096M), which the
# build VM lifted: the same smoke under it.
v=\$(vm 'ulimit -d 4194304; $W/fresh/usr/local/fn/bin/fn --version' 2>&1)
echo \"fn --version (the stock daemon class, datasize 4194304 KiB): \$v\"
[ \"\$v\" = 'fn $VERSION ($SHORT)' ] || { echo \"under the stock 4 GiB datasize fn --version is not 'fn $VERSION ($SHORT)'\"; exit 1; }
cd $R/out && sha256sum $tb && grep -F $tb SHA256SUMS"
  if [ "$DRY" = yes ]; then
    would "git archive --format=tar $REV | ssh $HOST 'cat > $S/source.tar'"
    echo "$script" | sed 's/^/would (hbox): /'
    printf '%s\n' "$guest" | sed 's/^/would (openbsd guest): /'
    box "test -f $cfg && test -f $B/vm/id_ed25519" \
      || { echo "no OpenBSD build VM $OB_VM on $HOST ($cfg, $B/vm/id_ed25519): provision it as the header of tools/cut_release.sh says"; return 1; }
    running=$(box "docker inspect -f '{{.State.Running}}' pl-obsd-$OB_VM 2>/dev/null")
    [ "$running" != true ] || { echo "the build VM $OB_VM is running now (pl-obsd-$OB_VM: someone's; the gate refuses to take it)"; return 1; }
    echo "preconditions on $HOST: the build VM $OB_VM provisioned and stopped"
    return 10
  fi
  git archive --format=tar "$REV" | ssh -o BatchMode=yes "$HOST" "mkdir -p $S && cat > $S/source.tar" || { echo "shipping the archive failed"; return 1; }
  box_script openbsd-guest "$guest" || { echo "shipping the guest script failed"; return 1; }
  box_script tarball-openbsd "$script" || { echo "shipping the gate script failed"; return 1; }
  box "sh $S/tarball-openbsd.sh" || { echo "the OpenBSD tarball gate failed ($HOST:$R/out)"; return 1; }
  echo "$tb built in the VM $OB_VM, runpath clean, installed fresh, test_release_tarball OK, fn --version fn $VERSION ($SHORT) ($HOST:$R/out)"
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
  if [ "$DRY" = yes ]; then
    echo "$script" | sed 's/^/would (hbox, in a systemd-run --user unit): /'
    box "sudo -n true" 2>/dev/null || { echo "power-loss needs sudo -n on $HOST (the block layer): not available"; return 1; }
    echo "preconditions on $HOST: sudo -n for the block layer"
    return 10
  fi
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

# The N-version differential (lane extract-2): `make extract-check' when REV's
# Makefile has the target; until then the gate says SKIPPED, never green.
g_extract() {
  if ! git show "$REV:Makefile" 2>/dev/null | grep -q '^extract-check:'; then
    echo "no make target extract-check at REV (lane extract-2): skipped"; return 11
  fi
  if [ "$DRY" = yes ]; then would make extract-check; return 10; fi
  make extract-check || { echo "make extract-check failed"; return 1; }
  echo "make extract-check green"
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
gate 16 extract g_extract
gate 17 tag g_tag

if [ "$DRY" = yes ]; then
  echo "VERDICT DRY-RUN v$VERSION $REV: first red ${FIRST_RED:-none} ($(stamp))" >> "$V"
elif [ "$TO" -lt 17 ]; then
  echo "VERDICT PARTIAL v$VERSION $REV: gates $FROM to $TO green; not a cut ($(stamp))" >> "$V"
else
  echo "VERDICT GREEN v$VERSION $REV${SKIPS:+ (skipped:$SKIPS)} ($(stamp))" >> "$V"
fi
tail -1 "$V"
echo "verdict: $V"
