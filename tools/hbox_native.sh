#!/bin/sh
# Build a native image on hbox and run named test modules against it.
#
#   tools/hbox_native.sh [options] REV MODULE...
#
# REV is a commit (shipped with `git archive`, so the tree is exactly that
# revision) or `.` (this working tree, uncommitted edits included, rsynced with
# farm.py's excludes).  MODULE is a unittest name: tests.test_native_owner or
# tests.test_native_owner.SomeTests.
#
# On hbox, under /tank/fn/scratch/NAME/native-LABEL/ (NAME is the lane: the
# basename of this worktree, or --name), it
#   1. installs the default profile's closure from /tank/fn/certcache and
#      certifies the rest under swarm-build (a lane's changed books);
#   2. acquires and validates the image's artifact set (tools/proof_artifacts.py;
#      the dtn profile too when a DTN image is asked);
#   3. builds the requested images under swarm-build
#      (--images from developer,production,dtn,dtn-developer; default
#      developer).  dtn and dtn-developer are host/native/build-dtn.lisp's
#      images (build/fn-host-dtn, build/fn-host-dtn-developer), built exactly
#      as tools/runbooks/hbox-image-build.sh builds them;
#   4. runs each MODULE under systemd-run --user --scope -p MemoryMax (24G by
#      default, --mem), with FN_OPENSSL_PREFIX and LD_LIBRARY_PATH set, and
#      every --env NAME=VALUE exported.  When dtn-developer is built and dtn is
#      not, FN_NATIVE_BP_HOST defaults to the dtn-developer image (the BP
#      tests default to build/fn-host-dtn, which that run does not build);
#   5. writes every log to logs/ and SHA256SUMS (images and logs), then
#      `status` holding the first failing step's exit code, 0 if none.
#
# It prints the scratch path, then waits for `status` (tools/wait_for.sh) and
# prints the summary; start it with run_in_background.  --detach returns after
# the start instead.  The box run survives a dropped ssh (nohup).
#
# Options: --name NAME, --label LABEL, --images LIST, --mem SIZE,
# --jobs N (certify, default 8), --no-build (reuse the images already in that
# scratch tree), --env NAME=VALUE (repeatable; paths may use $T, the tree),
# --deadline S (default 5400), --dry-run (print the box script).
#
# Replaces the hand-rolled rsync + image.sh + OpenSSL exports 145 lanes wrote
# (friction review 2026-09-26 section 5).  Never touches /tank/fn/node.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
HOST=${FN_HBOX:-hbox}
NAME=$(basename "$HERE")
LABEL=
IMAGES=developer
MEM=24G
JOBS=8
BUILD=1
DETACH=0
DRY=0
DEADLINE=5400
ENVS=
usage() { sed -n '2,41p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2; }
while [ $# -gt 0 ]; do
    case $1 in
        --name) NAME=$2; shift 2 ;;
        --label) LABEL=$2; shift 2 ;;
        --images) IMAGES=$2; shift 2 ;;
        --mem) MEM=$2; shift 2 ;;
        --jobs) JOBS=$2; shift 2 ;;
        --no-build) BUILD=0; shift ;;
        --detach) DETACH=1; shift ;;
        --dry-run) DRY=1; shift ;;
        --deadline) DEADLINE=$2; shift 2 ;;
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
        *) break ;;
    esac
done
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
DTN=0
DTN_PRODUCTION=0
DTN_DEVELOPER=0
for image in $(echo "$IMAGES" | tr ',' ' '); do
    case $image in
        developer|production) ;;
        dtn) DTN=1; DTN_PRODUCTION=1 ;;
        dtn-developer) DTN=1; DTN_DEVELOPER=1 ;;
        *) echo "hbox_native: --images takes developer,production,dtn,dtn-developer" >&2; exit 2 ;;
    esac
done
if [ $DTN_DEVELOPER -eq 1 ] && [ $DTN_PRODUCTION -eq 0 ]; then
    case " $ENVS" in *" FN_NATIVE_BP_HOST="*) ;; *) ENVS="FN_NATIVE_BP_HOST=\$T/build/fn-host-dtn-developer$ENVS" ;; esac
fi
if [ "$REV" = . ]; then
    SOURCE="worktree $(git -C "$HERE" rev-parse --short=12 HEAD)$(git -C "$HERE" diff --quiet HEAD -- 2>/dev/null || echo '+dirty')"
    [ -n "$LABEL" ] || LABEL=wt-$(date -u +%Y%m%dT%H%M%SZ)
else
    FULL=$(git -C "$HERE" rev-parse --verify "$REV^{commit}") || { echo "hbox_native: no commit $REV" >&2; exit 2; }
    SOURCE="commit $FULL"
    [ -n "$LABEL" ] || LABEL=$(echo "$FULL" | cut -c1-12)
fi
case $LABEL in ''|*[!A-Za-z0-9._-]*) echo "hbox_native: bad --label $LABEL" >&2; exit 2 ;; esac
S=/tank/fn/scratch/$NAME/native-$LABEL
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
ACL2=/tank/fn/toolchains/w28/acl2-literal-4g
CACHE=/tank/fn/certcache
export FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8
export LD_LIBRARY_PATH=\$FN_OPENSSL_PREFIX/lib\${LD_LIBRARY_PATH:+:\$LD_LIBRARY_PATH}
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
# A test module runs to the end whatever the others did; its unittest summary
# line (with any skips: a skipped witness is not evidence) goes in run.log.
failed=0
tstep() {
    name=\$1; shift
    echo "== \$name \$(date -u +%H:%M:%SZ)"
    "\$@" > \$L/\$name.log 2>&1
    rc=\$?
    echo "   \$name exit \$rc: \$(grep -E '^(OK|FAILED)' \$L/\$name.log | tail -n 1) (\$L/\$name.log)"
    [ \$rc -eq 0 ] || [ \$failed -ne 0 ] || failed=\$rc
}
finish() {
    (cd \$S && find tree/build -maxdepth 1 -name 'fn-host*' -type f -exec sha256sum {} + ; sha256sum logs/*.log) > \$S/SHA256SUMS 2>/dev/null
    echo \$1 > \$S/status
    echo "== done status \$1; \$S/SHA256SUMS"
    exit \$1
}
echo "== source $SOURCE"
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
toolchain=\$(python3 tools/acl2_toolchain.py identity "\$ACL2") || finish 14
step install python3 tools/certs.py --cache \$CACHE --toolchain-identity "\$toolchain" --acl2 "\$ACL2" install-partial \$(cat \$L/roots.txt)
step certify swarm-build python3 tools/certify_books.py --incremental --jobs $JOBS --timeout-seconds 900 \$(cat \$L/roots.txt)
step acquire python3 tools/proof_artifacts.py acquire --profile default --root \$T --cache \$CACHE --acl2 "\$ACL2"
step validate python3 tools/proof_artifacts.py validate --profile default --acl2 "\$ACL2"
BOX
        if [ $DTN -eq 1 ]; then
            # hbox-image-build.sh's dtn acquire/validate, before a DTN image.
            cat <<BOX
step acquire-dtn python3 tools/proof_artifacts.py acquire --profile dtn --root \$T --cache \$CACHE --acl2 "\$ACL2"
step validate-dtn python3 tools/proof_artifacts.py validate --profile dtn --acl2 "\$ACL2"
BOX
        fi
        for image in $(echo "$IMAGES" | tr ',' ' '); do
            # The (profile, session script, image) triple per image, as
            # tools/runbooks/hbox-image-build.sh's four build lines.
            case $image in
                production) profile=production build=host/native/build.lisp out=build/fn-host ;;
                developer) profile=developer build=host/native/build.lisp out=build/fn-host-developer ;;
                dtn) profile=production build=host/native/build-dtn.lisp out=build/fn-host-dtn ;;
                dtn-developer) profile=developer build=host/native/build-dtn.lisp out=build/fn-host-dtn-developer ;;
            esac
            cat <<BOX
step image-$image env FN_NATIVE_PROFILE=$profile FN_NATIVE_BUILD=$build FN_NATIVE_IMAGE=$out FN_NATIVE_LOG=\$L/native-build-$image.log swarm-build sh tools/build_native_host.sh
BOX
        done
    fi
    for assignment in $ENVS; do
        echo "export $assignment"
    done
    for module in "$@"; do
        cat <<BOX
tstep test-$module systemd-run --user --scope --quiet --slice=swarm.slice -p MemoryMax=$MEM -p MemorySwapMax=0 -- sh -c 'echo 0 > /proc/self/oom_score_adj 2>/dev/null; exec python3 -m unittest -v $module'
BOX
    done
    echo "finish \$failed"
}

if [ $DRY -eq 1 ]; then
    box_script "$@"
    exit 0
fi

echo "hbox_native: $SOURCE -> $HOST:$S"
ssh -n "$HOST" "mkdir -p $S/tree $S/logs" || { echo "hbox_native: cannot create $S on $HOST" >&2; exit 3; }
if [ "$REV" = . ]; then
    rsync -a --delete --exclude=build/ --exclude=.git/ --exclude=__pycache__/ \
        --exclude=.venv/ --exclude='*.pyc' --exclude=LANEDUMP.md \
        "$HERE/" "$HOST:$S/tree/" || { echo "hbox_native: rsync failed" >&2; exit 3; }
else
    ssh -n "$HOST" "find $S/tree -mindepth 1 -maxdepth 1 ! -name build -exec rm -rf {} +" || exit 3
    git -C "$HERE" archive --format=tar "$FULL" | ssh "$HOST" "tar -x -C $S/tree" \
        || { echo "hbox_native: shipping $FULL failed" >&2; exit 3; }
fi
box_script "$@" | ssh "$HOST" "cat > $S/run.sh" || exit 3
ssh -n "$HOST" "rm -f $S/status; nohup sh $S/run.sh > $S/run.log 2>&1 < /dev/null &" || exit 3
echo "hbox_native: started; progress in $HOST:$S/run.log"
if [ $DETACH -eq 1 ]; then
    echo "hbox_native: wait with: tools/wait_for.sh --host $HOST --deadline $DEADLINE --file $S/status"
    exit 0
fi
set +e
"$HERE/tools/wait_for.sh" --host "$HOST" --deadline "$DEADLINE" --interval 30 --file "$S/status" >/dev/null
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
