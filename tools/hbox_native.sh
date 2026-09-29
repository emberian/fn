#!/bin/sh
# Build a native image on a build box and run named test modules against it.
#
# The box is --box BOX (hbox, persvati or auto; default $FN_HBOX, else auto).
# Each box's row (item 67, obstructions-7): its scratch BASE (hbox
# /tank/fn/scratch, persvati ~/fn-gates), its certificate cache and build
# wrapper (tools/farm.py HOSTS: hbox /tank/fn/certcache under swarm-build,
# persvati ~/fn-certcache with none), its test OpenSSL (hbox the 3.5.8 test
# tool below, persvati the system openssl 3.5) and whether it holds the
# published image sets (hbox only, /tank/fn/images).  auto picks by load per
# core (tools/boxes.sh --pick), except that --image-set and --reuse-image
# take hbox, where the sets and the earlier runs live; name --box to
# override.  The record (build/hbox-native/LABEL.run here) names the box.
# Before 2026-09-29 the cache and wrapper were hbox's whatever FN_HBOX said,
# so a persvati run could not work (compress-8).
#
#   tools/hbox_native.sh [options] REV MODULE...
#
# REV is a commit (shipped with `git archive`, so the tree is exactly that
# revision) or `.` (this working tree, uncommitted edits included, rsynced with
# farm.py's excludes).  MODULE is a unittest name: tests.test_native_owner or
# tests.test_native_owner.SomeTests.
#
# On the box, under BASE/NAME/native-LABEL/ (NAME is the lane: the
# basename of this worktree, or --name), it
#   1. installs the default profile's closure from /tank/fn/certcache and
#      certifies the rest under swarm-build (a lane's changed books);
#   2. acquires and validates the image's artifact set (tools/proof_artifacts.py;
#      the dtn profile too when a DTN image is asked);
#   3. builds the requested images under swarm-build
#      (--images from developer,production,dtn,dtn-developer,reference,
#      developer-stripped,prof; default
#      developer).  dtn and dtn-developer are host/native/build-dtn.lisp's
#      images (build/fn-host-dtn, build/fn-host-dtn-developer), built exactly
#      as tools/runbooks/hbox-image-build.sh builds them.  `prof` is the
#      PROFILING developer image (tools/profile/build_native_profile.sh,
#      build/fn-host-prof; sb-sprof when FN_PROF_OUT is set), a measurement
#      tool and never a release or test subject.  It needs this run's own
#      full certify and acquire (steps 1-2): copying another native tree and
#      building only the image failed because that tree's certified set
#      lacked books the profiling entry's world loads (served-columns,
#      native-n1: outcome-class, replay, node).  Build it here, in the run
#      that certifies, not by hand in a copied tree;
#   4. runs each MODULE (a --mem of 48G or more waits on one box-wide flock,
#      /tank/fn/scratch/.hbox-native-bigmem.lock, so two such scopes never
#      overlap) under systemd-run --user --scope -p MemoryMax (24G by
#      default, --mem; a served-read measurement through
#      tools/fundamentals/sr_measure.py or served_ab.sh needs 40G: at 24G the
#      owner refuses its connections, connections-exceed-memory), against
#      hbox's system libssl (OpenSSL 3.3.1; no
#      FN_OPENSSL_PREFIX: HST-016), with every --env NAME=VALUE exported.
#      OpenSSL 3.5.8 stays a TEST TOOL only (ML-DSA-65 keys and signatures
#      made independently of the node): $FN_TEST_OPENSSL_BIN, a wrapper
#      that gives that binary its own libraries and nothing else.  When dtn-developer is built and dtn is
#      not, FN_NATIVE_BP_HOST defaults to the dtn-developer image (the BP
#      tests default to build/fn-host-dtn, which that run does not build).
#      Each module's process also gets every variable tools/native_env.py
#      finds it reading: the image variables for the images built
#      (FN_NATIVE_HOST is only ever the production image), the opt-in flags
#      FN_RUN_HYBRID_E2E and FN_RUN_CONSUMER_EXCHANGE, FN_TEST_OPENSSL.  A
#      module reading an image variable whose image is not built is refused
#      by name before anything ships (exit 2), and again on the box before
#      the first test when the image is not in the tree (--no-build).  Each
#      module runs through tools/test_budget.py --one, and its line in
#      run.log is OK (N ran, K skipped), FAILED, or SKIPPED (N of N) with
#      every skip's reason; a SKIPPED module makes the status 4;
#      When the tree holds the production image (or the one --env
#      FN_NATIVE_HOST names), tools/native_env.py identity exports its four
#      identity variables (launcher, core and runtime SHA-256, and the source:
#      the commit, or HEAD+dirty for `.`) for every module;
#   5. writes every log to logs/ and SHA256SUMS (images and logs), then
#      `status` holding the first failing step's exit code, 0 if none.
#      run.log carries the box's load (`uptime`) at the start and the end
#      and the load average before each module, so a timing taken on a
#      loaded box can be judged (feed-queue: 20.9 s against 2.7 s for one
#      case at load 19-37).
#
# It prints the scratch path, then waits for `status` (tools/wait_for.sh) and
# prints the summary; start it with run_in_background.  --detach returns after
# the start instead.  The box run survives a dropped ssh (nohup).
#
# Options: --box hbox|persvati|auto (above), --name NAME, --label LABEL, --images LIST, --mem SIZE,
# --image-acl2 PATH (the ACL2 wrapper the IMAGES are built with; certification
# keeps the toolchain's.  Default /tank/fn/toolchains/w28/acl2-literal-4g-tls64k,
# the w28 launcher at --tls-limit 65536 (coordinator decision 2026-09-27): the
# served image's load exhausted SBCL's thread-local storage at 16384 on
# 2026-09-27 (batch AV's native-av-bb1a and recover-memory-2); give the
# toolchain's own path to build at 16384),
# --jobs N (modules run N at a time against the one image set, default 1:
# each is its own process, its own MemoryMax scope and its own ports; a
# group of 20 modules at 4 jobs on hbox takes about a quarter of the serial
# time), --certify-jobs N|auto (certify, default auto: tools/chain_schedule.py), --no-build (reuse the images already in that
# scratch tree; the re-ship keeps the tree's .cert/.port/.fasl files, which it
# used to delete, leaving REPL sessions there refusing include-book),
# --image-set SHA (no certify and no build: link the prebuilt images the batch
# published for dev commit SHA from hbox:/tank/fn/images/SHA, verified by its
# SHA256SUMS; layout and publishing in tools/image_set.py; --images names
# which of its production, developer, dtn, dtn-developer to link; the
# images' identity source is SHA, the tree is REV), --reuse-image RUN (no
# certify and no build: link the images an earlier run built, RUN =
# NAME/native-LABEL or a /tank/fn/scratch path, from RUN/tree/build; their
# identity source is the one RUN's log names; `tools/image_set.py link-run`),
# --env NAME=VALUE (repeatable; paths may use $T, the tree),
# --deadline S (default 5400), --dry-run (print the box script; the refusal
# and the per-module environment show there), --allow-skips (run a module
# whose opt-in gate -- FN_RUN_*_E2E, FN_INN_SRC ... -- is unset; without it
# such a module is refused at launch, naming the variable, not skipped after
# the build).  Options may come before or
# after REV and the modules.
#
# A box reserved for a measurement (tools/boxes.sh reserve) is waited for before
# anything ships (the holder's own worktree passes).
#
# Replaces the hand-rolled rsync + image.sh + OpenSSL exports 145 lanes wrote
# (friction review 2026-09-26 section 5).  Never touches /tank/fn/node.
set -eu
# Copy-then-run (lane tooling-leftovers, 2026-09-27): sh reads a script as it
# runs it, and a run waits here for an hour or more, so a merge or an edit
# of this file in the worktree mid-run changed the commands the running
# instance read next.  The first thing it does is copy itself and
# tools/wait_for.sh into a private directory and exec the copy; nothing
# after this block reads the worktree's copy of either.
if [ -z "${FN_HBOX_NATIVE_COPY:-}" ]; then
    FN_HBOX_NATIVE_HERE=$(cd "$(dirname "$0")/.." && pwd)
    FN_HBOX_NATIVE_COPY=$(mktemp -d "${TMPDIR:-/tmp}/hbox_native.XXXXXX") || exit 3
    cp "$FN_HBOX_NATIVE_HERE/tools/hbox_native.sh" "$FN_HBOX_NATIVE_HERE/tools/wait_for.sh" \
        "$FN_HBOX_NATIVE_HERE/tools/boxes.sh" "$FN_HBOX_NATIVE_HERE/tools/image_set.py" \
        "$FN_HBOX_NATIVE_HERE/tools/native_box.sh" \
        "$FN_HBOX_NATIVE_COPY/" || exit 3
    export FN_HBOX_NATIVE_COPY FN_HBOX_NATIVE_HERE
    exec sh "$FN_HBOX_NATIVE_COPY/hbox_native.sh" "$@"
fi
trap 'rm -rf "$FN_HBOX_NATIVE_COPY"' EXIT
HERE=$FN_HBOX_NATIVE_HERE
BOX=${FN_HBOX:-auto}
NAME=$(basename "$HERE")
LABEL=
IMAGES=developer
MEM=24G
IMAGE_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k
JOBS=auto
MODULE_JOBS=1
BUILD=1
DETACH=0
DRY=0
ALLOW_SKIPS=
DEADLINE=5400
ENVS=
IMAGES_GIVEN=0
POSITIONAL=
IMAGE_SET=
REUSE=
usage() { sed -n '2,/^set -eu/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//' >&2; exit 2; }
while [ $# -gt 0 ]; do
    case $1 in
        --name) NAME=$2; shift 2 ;;
        --label) LABEL=$2; shift 2 ;;
        --images) IMAGES=$2; IMAGES_GIVEN=1; shift 2 ;;
        --mem) MEM=$2; shift 2 ;;
        --jobs)
            case $2 in ''|*[!0-9]*|0) echo "hbox_native: --jobs takes a positive integer" >&2; exit 2 ;; esac
            MODULE_JOBS=$2; shift 2 ;;
        --certify-jobs) JOBS=$2; shift 2 ;;
        --no-build) BUILD=0; shift ;;
        --image-set)
            case $2 in *[!0-9a-f]*|'') echo "hbox_native: --image-set takes a commit sha" >&2; exit 2 ;; esac
            IMAGE_SET=$2; BUILD=0; shift 2 ;;
        --box)
            case $2 in hbox|persvati|auto) BOX=$2 ;; *) echo "hbox_native: --box takes hbox, persvati or auto" >&2; exit 2 ;; esac
            shift 2 ;;
        --reuse-image)
            case $2 in /*) REUSE=$2 ;; */native-*) REUSE=__BASE__/$2 ;;
                native-*) REUSE=__NAME__/$2 ;;
                *) echo "hbox_native: --reuse-image takes NAME/native-LABEL or the box's absolute run path" >&2; exit 2 ;;
            esac
            case $REUSE in *..*|*[!A-Za-z0-9._/-]*) echo "hbox_native: bad --reuse-image $2" >&2; exit 2 ;; esac
            BUILD=0; shift 2 ;;
        --detach) DETACH=1; shift ;;
        --dry-run) DRY=1; shift ;;
        # A module gated by an unset opt-in (FN_RUN_*_E2E ...) is refused at
        # launch unless this is given (tools/native_env.py plan; item 45).
        --allow-skips) ALLOW_SKIPS=--allow-skips; shift ;;
        --deadline) DEADLINE=$2; shift 2 ;;
        # The ACL2 wrapper the IMAGE builds run under (certification keeps
        # the toolchain's, whose identity the cache keys on).  The world is
        # past SBCL's --tls-limit 16384 since batch AV ("Thread local
        # storage exhausted"; recover-memory-2's packet); the default is the
        # tls64k wrapper above.
        --image-acl2)
            case $2 in /*) ;; *) echo "hbox_native: --image-acl2 takes an absolute path" >&2; exit 2 ;; esac
            case $2 in *[!A-Za-z0-9_./-]*) echo "hbox_native: bad --image-acl2 path" >&2; exit 2 ;; esac
            IMAGE_ACL2=$2; shift 2 ;;
        --env)
            case $2 in
                ?*=*) ;;
                *) echo "hbox_native: --env takes NAME=VALUE" >&2; exit 2 ;;
            esac
            # Spelled out: a locale's [A-Z] range can match lower case.
            case ${2%%=*} in [0-9]*|*[!ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_]*) echo "hbox_native: bad --env name ${2%%=*}" >&2; exit 2 ;; esac
            case ${2#*=} in *[!A-Za-z0-9_./:\$-]*) echo "hbox_native: --env value may hold only A-Za-z0-9_./:-\$" >&2; exit 2 ;; esac
            ENVS="$ENVS $2"; shift 2 ;;
        -h|--help) usage ;;
        -*) echo "hbox_native: unknown option $1" >&2; usage ;;
        # An option may follow REV or a module (PKT-490 (3)): positionals are
        # collected and every option still applies.  REV and module names
        # hold no blank (each is validated below), so the list re-splits.
        *) POSITIONAL="$POSITIONAL $1"; shift ;;
    esac
done
# shellcheck disable=SC2086
set -- $POSITIONAL
[ $# -ge 2 ] || usage
REV=$1; shift
for module in "$@"; do
    case $module in
        tests.[A-Za-z_]*) ;;
        *) echo "hbox_native: $module is not a unittest module name (tests.test_...)" >&2; exit 2 ;;
    esac
    case $module in *[!A-Za-z0-9_.]*) echo "hbox_native: bad module name $module" >&2; exit 2 ;; esac
done
case $NAME in ''|*[!A-Za-z0-9._-]*) echo "hbox_native: bad --name $NAME" >&2; exit 2 ;; esac
# Without --images, the list is what the modules read, over developer
# (tools/native_env.py images): a module reading FN_NATIVE_HOST gets the
# production image built instead of a refusal (three lanes lost a launch each,
# 2026-09-29).  An explicit --images is taken as given, and a module reading
# an image it leaves out is refused by name below.
if [ "$IMAGES_GIVEN" = 0 ]; then
    DERIVE_ENV=
    for assignment in $ENVS; do DERIVE_ENV="$DERIVE_ENV --env $assignment"; done
    # shellcheck disable=SC2086
    IMAGES=$(python3 "$HERE/tools/native_env.py" images --images "$IMAGES" $DERIVE_ENV "$@") || exit 2
fi
DTN=0
DTN_PRODUCTION=0
DTN_DEVELOPER=0
for image in $(echo "$IMAGES" | tr ',' ' '); do
    case $image in
        developer|production|reference|developer-stripped|prof) ;;
        dtn) DTN=1; DTN_PRODUCTION=1 ;;
        dtn-developer) DTN=1; DTN_DEVELOPER=1 ;;
        *) echo "hbox_native: --images takes developer,production,dtn,dtn-developer,reference,developer-stripped,prof" >&2; exit 2 ;;
    esac
done
if [ -n "$IMAGE_SET" ] && [ -n "$REUSE" ]; then
    echo "hbox_native: --image-set and --reuse-image both name the images; give one" >&2; exit 2
fi
if [ -n "$IMAGE_SET" ] || [ -n "$REUSE" ]; then
    for image in $(echo "$IMAGES" | tr ',' ' '); do
        case $image in production|developer|dtn|dtn-developer) ;;
            *) echo "hbox_native: an image set holds production, developer, dtn and dtn-developer, not $image" >&2; exit 2 ;;
        esac
    done
fi
if [ -n "$IMAGE_SET" ]; then
    IMAGE_SET=$(git -C "$HERE" rev-parse --verify --quiet "$IMAGE_SET^{commit}" || echo "$IMAGE_SET")
    case $IMAGE_SET in *[!0-9a-f]*) exit 2 ;; esac
    [ ${#IMAGE_SET} -eq 40 ] || { echo "hbox_native: --image-set $IMAGE_SET: not a commit here; give the full sha" >&2; exit 2; }
fi
if [ $DTN_DEVELOPER -eq 1 ] && [ $DTN_PRODUCTION -eq 0 ]; then
    case " $ENVS" in *" FN_NATIVE_BP_HOST="*) ;; *) ENVS="FN_NATIVE_BP_HOST=\$T/build/fn-host-dtn-developer$ENVS" ;; esac
fi
# What each module reads, against what this run builds (PKT-437 (2)).
ENVARGS=
for assignment in $ENVS; do ENVARGS="$ENVARGS --env $assignment"; done
PLAN=$(python3 "$HERE/tools/native_env.py" plan --images "$IMAGES" $ENVARGS $ALLOW_SKIPS "$@") || exit 2
if [ "$REV" = . ]; then
    # The image's declared source: HEAD, marked +dirty for uncommitted edits
    # (before 2026-09-27 FN_NATIVE_IMAGE_SOURCE_SHA was the literal ".").
    SOURCE_ID=$(git -C "$HERE" rev-parse HEAD)$(git -C "$HERE" diff --quiet HEAD -- 2>/dev/null || echo '+dirty')
    SOURCE="worktree $SOURCE_ID"
    [ -n "$LABEL" ] || LABEL=wt-$(date -u +%Y%m%dT%H%M%SZ)
else
    FULL=$(git -C "$HERE" rev-parse --verify "$REV^{commit}") || { echo "hbox_native: no commit $REV" >&2; exit 2; }
    SOURCE_ID=$FULL
    SOURCE="commit $FULL"
    [ -n "$LABEL" ] || LABEL=$(echo "$FULL" | cut -c1-12)
fi
case $LABEL in ''|*[!A-Za-z0-9._-]*) echo "hbox_native: bad --label $LABEL" >&2; exit 2 ;; esac
# The images' own source is the set's commit, whatever tree runs the tests.
[ -z "$IMAGE_SET" ] || SOURCE_ID=$IMAGE_SET
# The box and its row (item 67).  auto takes hbox for --image-set and
# --reuse-image (the published sets and the earlier runs live there) and for
# a dry run (no ssh); otherwise the lower load per core now.
if [ "$BOX" = auto ]; then
    if [ -n "$IMAGE_SET" ] || [ -n "$REUSE" ] || [ $DRY -eq 1 ]; then
        BOX=hbox
    else
        BOX=$(sh "$FN_HBOX_NATIVE_COPY/boxes.sh" --pick) || { echo "hbox_native: no build box answers (tools/boxes.sh --pick)" >&2; exit 3; }
    fi
fi
HOST=$BOX
ROW=$(sh "$FN_HBOX_NATIVE_COPY/native_box.sh" "$BOX" "$HERE") || exit 2
eval "$ROW"
case "$BASE $CACHE" in
    '~/'*|*' ~/'*)
        if [ $DRY -eq 0 ]; then
            # Absolute paths in every ssh command and in the box script.
            REMOTE_HOME=$(ssh -n "$HOST" 'echo $HOME') || { echo "hbox_native: cannot reach $HOST" >&2; exit 3; }
            ROW=$(sh "$FN_HBOX_NATIVE_COPY/native_box.sh" "$BOX" "$HERE" "$REMOTE_HOME") || exit 2
            eval "$ROW"
        fi ;;
esac
# The test OpenSSL (a TEST TOOL only; the node links the box's libssl).
openssl_setup() {
    case $OPENSSL in
        bundled) cat <<'OSSL'
printf '%s\n' '#!/bin/sh' 'LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib exec /tank/fn/toolchains/openssl-3.5.8/bin/openssl "$@"' > $S/bin/openssl-test
OSSL
        ;;
        system) cat <<'OSSL'
printf '%s\n' '#!/bin/sh' "exec $(command -v openssl) \"\$@\"" > $S/bin/openssl-test
OSSL
        ;;
    esac
    echo 'chmod 0755 $S/bin/openssl-test'
}
if [ -n "$IMAGE_SET" ] && [ -z "$IMAGES_BASE" ]; then
    echo "hbox_native: $BOX holds no published image sets (they are published on hbox); use --box hbox with --image-set" >&2; exit 2
fi
S=$BASE/$NAME/native-$LABEL
case $REUSE in __NAME__/*) REUSE=$BASE/$NAME/${REUSE#__NAME__/} ;; __BASE__/*) REUSE=$BASE/${REUSE#__BASE__/} ;; esac
if [ -n "$REUSE" ]; then
    [ "$REUSE" != "$S" ] || { echo "hbox_native: --reuse-image $REUSE is this run's own tree (use --no-build)" >&2; exit 2; }
    # The images' identity source is the reused run's, read on the box from
    # the file link-run writes (its run.log's `== source` line).
    SOURCE_ID='$(cat build/REUSED_SOURCE)'
fi
case $S in /tank/fn/node*) echo "hbox_native: refusing the live node path" >&2; exit 2 ;; esac

# The box half.  Every step logs to $S/logs and a failure stops the run with
# that step's code in $S/status.
box_script() {
    cat <<BOX
#!/bin/sh
set -u
S=$S
T=\$S/tree
L=\$S/logs
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k  # the certify launcher (tools/farm.py HOSTS)
CACHE=$CACHE  # this box's (tools/farm.py HOSTS)
unset FN_OPENSSL_PREFIX
mkdir -p \$S/bin
$(openssl_setup)
export FN_TEST_OPENSSL_BIN=\$S/bin/openssl-test
export FN_ACL2=\$ACL2 FN_CERT_CACHE=\$CACHE FN_CERT_ORIGIN_KIND=run
mkdir -p \$L
rm -f \$S/status
cd \$T || { echo 9 > \$S/status; exit 9; }
step() {
    name=\$1; shift
    echo "== \$name \$(date -u +%H:%M:%SZ)"
    "\$@" > \$L/\$name.log 2>&1
    rc=\$?
    echo "   \$name exit \$rc (\$L/\$name.log)"
    if [ \$rc -ne 0 ]; then
        tail -n 15 \$L/\$name.log | sed 's/^/   | /'
        finish \$rc
    fi
}
# A module reads an image variable: the image must be in the tree.
need() {
    [ -x "\$3" ] || { echo "hbox_native: \$1 reads \$2: \$3 is not in the tree (build it with --images)"; finish 2; }
}
finish() {
    echo "== load at end: \$(uptime)"
    (cd \$S && find tree/build -maxdepth 1 -name 'fn-host*' -type f -exec sha256sum {} + ; sha256sum logs/*.log) > \$S/SHA256SUMS 2>/dev/null
    echo \$1 > \$S/status
    echo "== done status \$1; \$S/SHA256SUMS"
    exit \$1
}
echo "== source $SOURCE"
echo "== load at start: \$(uptime)"
# The toolchain SBCL (tools/farm.py HOSTS) first on PATH and as FN_SBCL:
# hbox's system /usr/bin/sbcl is 2.2.9, and a test running \`sbcl\` by name
# got it (tooling-truth-2's KNOWN_RED list).  A bare sbcl that is not the
# toolchain's is refused before any step (obstructions-5 item 41).
eval "\$(python3 tools/native_env.py sbcl --export)"
step sbcl-check python3 tools/native_env.py sbcl-check
BOX
    if [ $BUILD -eq 1 ]; then
        cat <<BOX
python3 tools/proof_artifacts.py roots --profile default > \$L/roots.txt || finish 13
BOX
        if [ $DTN -eq 1 ]; then
            # The dtn profile's roots are not a subset of default's
            # (books/records-concrete at 804896a1): certify their union.
            cat <<BOX
python3 tools/proof_artifacts.py roots --profile dtn >> \$L/roots.txt || finish 13
sort -u -o \$L/roots.txt \$L/roots.txt
BOX
        fi
        cat <<BOX
# The static pre-image gates first (seconds; make host-convert-check runs
# them with the ACL2 ones): a stale umbrella or interface registry used to
# surface only after the certify step, in acquire or the image build
# (limits-live-5, decision-keystones-3; obstructions-5 item 34).
step world-check python3 tools/extract/world.py --check
step interfaces-check python3 tools/interface_emit.py --check
toolchain=\$(python3 tools/acl2_toolchain.py identity "\$ACL2") || finish 14
step install python3 tools/certs.py --cache \$CACHE --toolchain-identity "\$toolchain" --acl2 "\$ACL2" install-partial \$(cat \$L/roots.txt)
step certify $WRAP python3 tools/certify_books.py --incremental --images ${FN_CERT_IMAGES:-on} --jobs $JOBS --timeout-seconds 900 \$(cat \$L/roots.txt)
step acquire python3 tools/proof_artifacts.py acquire --profile default --root \$T --cache \$CACHE --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}"
step validate python3 tools/proof_artifacts.py validate --profile default --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}"
# The ld host files in the image's order, before any image build: statically
# (a call before its definition, seconds), then through ACL2 in the certified
# world (tools/host_check.py's default).  limits-live-4 and online-reclaim-4
# each lost an image build to a forward reference in host/owner-host.lisp.
step host-forward python3 tools/host_check.py --forward
step host-ld env FN_ACL2="${IMAGE_ACL2:-\$ACL2}" python3 tools/host_check.py
BOX
        if [ $DTN -eq 1 ]; then
            # hbox-image-build.sh's dtn acquire/validate, before a DTN image.
            cat <<BOX
step acquire-dtn python3 tools/proof_artifacts.py acquire --profile dtn --root \$T --cache \$CACHE --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}"
step validate-dtn python3 tools/proof_artifacts.py validate --profile dtn --acl2 "\$ACL2" --load-acl2 "${IMAGE_ACL2:-\$ACL2}"
BOX
        fi
        for image in $(echo "$IMAGES" | tr ',' ' '); do
            # The (profile, session script, image) triple per image, as
            # tools/runbooks/hbox-image-build.sh's four build lines.
            if [ "$image" = prof ]; then
                # The profiling entry is loaded before build.lisp's
                # save-exec; the script owns the (developer, full) triple.
                cat <<BOX
step image-prof env FN_ACL2=${IMAGE_ACL2:-\$ACL2} $WRAP sh tools/profile/build_native_profile.sh build/fn-host-prof
BOX
                continue
            fi
            case $image in
                production) profile=production build=host/native/build.lisp out=build/fn-host world=stripped ;;
                developer) profile=developer build=host/native/build.lisp out=build/fn-host-developer world=full ;;
                reference) profile=production build=host/native/build.lisp out=build/fn-host-reference world=full ;;
                developer-stripped) profile=developer build=host/native/build.lisp out=build/fn-host-developer-stripped world=stripped ;;
                dtn) profile=production build=host/native/build-dtn.lisp out=build/fn-host-dtn world=stripped ;;
                dtn-developer) profile=developer build=host/native/build-dtn.lisp out=build/fn-host-dtn-developer world=full ;;
            esac
            cat <<BOX
step image-$image env FN_ACL2=${IMAGE_ACL2:-\$ACL2} FN_NATIVE_PROFILE=$profile FN_NATIVE_WORLD=$world FN_NATIVE_BUILD=$build FN_NATIVE_IMAGE=$out FN_NATIVE_LOG=\$L/native-build-$image.log $WRAP sh tools/build_native_host.sh
BOX
        done
    fi
    if [ -n "$REUSE" ]; then
        cat <<BOX
echo "== images: reused from the earlier run $REUSE"
step image-reuse python3 \$S/bin/image_set.py link-run $REUSE \$T $(echo "$IMAGES" | tr ',' ' ')
BOX
    fi
    if [ -n "$IMAGE_SET" ]; then
        cat <<BOX
echo "== images: the published set $IMAGE_SET ($IMAGES_BASE/$IMAGE_SET)"
step image-set python3 \$S/bin/image_set.py link --base $IMAGES_BASE $IMAGE_SET \$T $(echo "$IMAGES" | tr ',' ' ')
BOX
    fi
    # The production image's identity (tests/test_native_peering and
    # test_native_admin check the running process against it), computed by
    # tools/native_env.py identity from the image FN_NATIVE_HOST names by
    # --env, else build/fn-host, when the tree holds it; an --env below
    # still wins.
    identity_image=build/fn-host
    for assignment in $ENVS; do
        case $assignment in FN_NATIVE_HOST=*) identity_image=${assignment#FN_NATIVE_HOST=} ;; esac
    done
    cat <<BOX
if [ -x "$identity_image" ]; then
    eval "\$(python3 tools/native_env.py identity --image "$identity_image" --source $SOURCE_ID --export)"
fi
if [ -x build/fn-host-developer ]; then
    eval "\$(python3 tools/native_env.py identity --image build/fn-host-developer --prefix FN_NATIVE_DEVELOPER_ --export)"
fi
BOX
    for assignment in $ENVS; do
        echo "export $assignment"
    done
    echo "$PLAN" | while read -r module assignments; do
        for assignment in $assignments; do
            case ${assignment#*=} in
                '$T/build/fn-host'*) echo "need $module ${assignment%%=*} ${assignment#*=}" ;;
            esac
        done
    done
    # A scope of 48G or more waits for every other such scope on the box
    # (one flock, held for the module): two 80G open_depth runs collided on
    # hbox's 123 GiB (2026-09-28).  Smaller scopes run as before.
    BIGMEM=
    case ${MEM%G} in
        ''|*[!0-9]*) ;;
        *) [ "${MEM%G}" -ge 48 ] && BIGMEM="flock $BASE/.hbox-native-bigmem.lock" ;;
    esac
    # The modules run from $S/module.sh, one process per module, --jobs at
    # a time (xargs -P; 1 keeps the old serial order).  Each writes its exit
    # code to $S/rc/test-MODULE and prints its verdict as one line when it
    # ends, so parallel modules never share a counter or split a block;
    # the tally below reads the codes in the order the modules were named.
    # Parallel modules are independent processes: each harness Node binds
    # its own ephemeral ports and makes its own temporary directories, and
    # each module keeps its own MemoryMax scope (N jobs can hold N x --mem).
    echo "export S T L FN_TEST_OPENSSL_BIN"
    echo "rm -rf \$S/rc; mkdir -p \$S/rc"
    echo "cat > \$S/module.sh <<'MODULE'"
    cat <<'MOD'
#!/bin/sh
set -u
cd "$T" || exit 0
# A test module runs to the end whatever the others did; its verdict goes in
# run.log: OK (N ran, K skipped), FAILED, or SKIPPED (N of N), with every
# skip's reason (a skipped witness is not evidence).  SKIPPED is status 4.
tstep() {
    name=$1; shift
    echo "== $name $(date -u +%H:%M:%SZ) load $(cut -d' ' -f1-3 /proc/loadavg)"
    # A failed test's processes' stderr lands in $L/stderr/$name (and its
    # digest in the module log after the failure): tools/test_budget.py.
    FN_NATIVE_STDERR_DIR=$L/stderr/$name "$@" > $L/$name.log 2>&1
    rc=$?
    verdict=$(python3 tools/test_budget.py --verdict $L/$name.log)
    vrc=$?
    [ $rc -ne 0 ] || rc=$vrc
    echo "   $name exit $rc $(date -u +%H:%M:%SZ): $verdict ($L/$name.log)"
    if [ -d $L/stderr/$name ]; then
        echo "   $name: stderr of each failed test's processes in $L/stderr/$name ($(ls $L/stderr/$name | wc -l) files)"
    fi
    echo $rc > $S/rc/$name
}
case $1 in
MOD
    i=0
    echo "$PLAN" | while read -r module assignments; do
        i=$((i+1))
        cat <<BOX
$i)
tstep test-$module $BIGMEM env $assignments systemd-run --user --scope --quiet --slice=swarm.slice -p MemoryMax=$MEM -p MemorySwapMax=0 -- sh -c 'echo 0 > /proc/self/oom_score_adj 2>/dev/null; exec python3 tools/test_budget.py --one $module'
;;
BOX
    done
    echo "esac"
    echo "exit 0"
    echo "MODULE"
    count=$(echo "$PLAN" | grep -c .)
    echo "echo \"== modules: $count, $MODULE_JOBS at a time\""
    echo "seq 1 $count | xargs -P $MODULE_JOBS -n 1 sh \$S/module.sh"
    echo 'failed=0 passed=0 skipped=0 broke=0'
    echo "for name in $(echo "$PLAN" | while read -r module assignments; do printf 'test-%s ' "$module"; done); do"
    cat <<'BOX'
    rc=$(cat $S/rc/$name 2>/dev/null || echo 125)
    case $rc in 0) passed=$((passed+1)) ;; 4) skipped=$((skipped+1)) ;; *) broke=$((broke+1)) ;; esac
    [ $rc -eq 0 ] || [ $failed -ne 0 ] || failed=$rc
done
BOX
    echo 'echo "== modules: $passed OK, $skipped SKIPPED (no test executed), $broke FAILED"'
    echo "finish \$failed"
}

if [ $DRY -eq 1 ]; then
    box_script "$@"
    exit 0
fi

# A box reserved for a measurement (tools/boxes.sh reserve) waits here, printing
# who holds it and until when; the holder's own runs (this worktree) pass.
FN_BOX_AS=${FN_BOX_AS:-$(basename "$HERE")} sh "$FN_HBOX_NATIVE_COPY/boxes.sh" wait "$HOST" || exit 3
echo "hbox_native: $SOURCE -> $HOST:$S"
ssh -n "$HOST" "mkdir -p $S/tree $S/logs" || { echo "hbox_native: cannot create $S on $HOST" >&2; exit 3; }
# --no-build keeps the tree's certificates: its images and any REPL session
# there were made against them, and a re-ship that deleted them left those
# sessions refusing include-book (2026-09-28).  A build run re-installs them.
KEEP=
[ $BUILD -eq 1 ] || KEEP="--exclude=*.cert --exclude=*.port --exclude=*.fasl"
if [ "$REV" = . ]; then
    # shellcheck disable=SC2086
    rsync -a --delete --exclude=build/ --exclude=.git/ --exclude=__pycache__/ \
        --exclude=.venv/ --exclude='*.pyc' --exclude=LANEDUMP.md $KEEP \
        "$HERE/" "$HOST:$S/tree/" || { echo "hbox_native: rsync failed" >&2; exit 3; }
elif [ $BUILD -eq 0 ]; then
    ssh -n "$HOST" "find $S/tree -mindepth 1 -path $S/tree/build -prune -o -type f ! -name '*.cert' ! -name '*.port' ! -name '*.fasl' -exec rm -f {} +" || exit 3
    git -C "$HERE" archive --format=tar "$FULL" | ssh "$HOST" "tar -x -C $S/tree" \
        || { echo "hbox_native: shipping $FULL failed" >&2; exit 3; }
else
    ssh -n "$HOST" "find $S/tree -mindepth 1 -maxdepth 1 ! -name build -exec rm -rf {} +" || exit 3
    git -C "$HERE" archive --format=tar "$FULL" | ssh "$HOST" "tar -x -C $S/tree" \
        || { echo "hbox_native: shipping $FULL failed" >&2; exit 3; }
fi
box_script "$@" | ssh "$HOST" "cat > $S/run.sh" || exit 3
if [ -n "$IMAGE_SET" ] || [ -n "$REUSE" ]; then
    ssh "$HOST" "mkdir -p $S/bin && cat > $S/bin/image_set.py" < "$FN_HBOX_NATIVE_COPY/image_set.py" || exit 3
fi
ssh -n "$HOST" "rm -f $S/status; nohup sh $S/run.sh > $S/run.log 2>&1 < /dev/null &" || exit 3
echo "hbox_native: started; progress in $HOST:$S/run.log"
# The record here names the box (item 67): status and re-attach read it.
mkdir -p "$HERE/build/hbox-native"
printf 'box=%s\ndir=%s\nlog=%s\nstatus=%s\nsource=%s\n' "$HOST" "$S" "$S/run.log" "$S/status" "$SOURCE_ID" \
    > "$HERE/build/hbox-native/$LABEL.run"
if [ $DETACH -eq 1 ]; then
    echo "hbox_native: wait with: tools/wait_for.sh --host $HOST --deadline $DEADLINE --file $S/status"
    exit 0
fi
set +e
sh "$FN_HBOX_NATIVE_COPY/wait_for.sh" --host "$HOST" --deadline "$DEADLINE" --interval 30 --file "$S/status" >/dev/null
waited=$?
set -e
ssh -n "$HOST" "cat $S/run.log; echo '== SHA256SUMS'; cat $S/SHA256SUMS 2>/dev/null"
if [ $waited -ne 0 ]; then
    echo "hbox_native: no status after ${DEADLINE}s (wait_for exit $waited); the run may still be going in $HOST:$S" >&2
    exit 124
fi
status=$(ssh -n "$HOST" "cat $S/status")
echo "hbox_native: status $status ($HOST:$S)"
exit "$status"
