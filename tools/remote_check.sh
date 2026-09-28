#!/bin/sh
# Run `make check-lane` (or another target) for this worktree on a build box.
#
#   tools/remote_check.sh BOX [--target T] [--fetch PATH]... [--no-dirty]
#                             [--tree PATH] [--log PATH]
#
# BOX is hbox, persvati or auto (tools/boxes.sh --pick: the lower load per
# core now; it prints both loads and the choice).  The laptop is not a build box (closeout-common,
# 2026-09-27): every repo-wide Python step runs there.  This does, in order:
#   1. bundles the commits of HEAD the box's mirror does not have yet (git
#      bundle over the mirror's refs; the whole history only the first time);
#   2. fetches the bundle into the box's shared bare mirror
#      (<base>/remote-check.git, ref refs/remote-check/LANE);
#   3. force-checks-out that commit in the lane's check tree
#      (<base>/LANE-check, default) and removes untracked files there (build/
#      kept), so a regeneration left over from the last run can never keep
#      make on an old head (batch AX, 2026-09-28);
#   4. applies this worktree's uncommitted tracked changes (git diff HEAD) on
#      top, unless --no-dirty; untracked files are named, never shipped;
#   5. runs `make T` there (T = check-lane by default) with the box's own
#      FN_ACL2 and FN_CERT_CACHE (tools/farm.py HOSTS), under swarm-build on
#      hbox, logging to <base>/LANE-check.log;
#   6. prints the log's step table, copies the log to
#      build/remote-check/BOX-T.log here, rsyncs each --fetch PATH (a file or
#      directory of the tree, e.g. planning/ledger.json) back into this
#      worktree, and exits with make's own status.
# <base> is /tank/fn/scratch on hbox and ~/fn-gates on persvati (hbox's
# mirror was seeded by `git clone --bare` of a box repo; seeding avoids the
# first run's whole-history bundle).  LANE is
# $FN_LANE, else the worktree's directory name.  Exit: make's status; 3 the
# bundle, fetch or checkout failed (nothing ran); 2 usage.
#
# Why: check-lane needs a git repository and a worktree's .git points at the
# laptop, so arena-store-2, openbsd-datasize and python-diet each bundled and
# cloned by hand on 2026-09-27, and batch AX lost a make check to a dirty
# box tree that refused a push.
set -u
# The whole script is one compound command, so the shell parses all of it
# before running any: editing this file during a run (sh reads a script as
# it goes) broke two runs mid-way on 2026-09-28.
{

usage() {
    sed -n '2,35p' "$0" | sed 's/^# \{0,1\}//' >&2
    exit 2
}

[ $# -ge 1 ] || usage
BOX=$1
shift
TARGET=check-lane
FETCH=
DIRTY=1
TREE=
LOG=
while [ $# -gt 0 ]; do
    case $1 in
        --target) [ $# -ge 2 ] || usage; TARGET=$2; shift 2 ;;
        --fetch) [ $# -ge 2 ] || usage; FETCH="$FETCH $2"; shift 2 ;;
        --no-dirty) DIRTY=0; shift ;;
        --tree) [ $# -ge 2 ] || usage; TREE=$2; shift 2 ;;
        --log) [ $# -ge 2 ] || usage; LOG=$2; shift 2 ;;
        -h|--help) usage ;;
        *) echo "remote_check: unknown option $1" >&2; usage ;;
    esac
done

if [ "$BOX" = auto ]; then
    BOX=$(sh "$(dirname "$0")/boxes.sh" --pick) || exit 3
fi
case $BOX in
    hbox) BASE=/tank/fn/scratch; WRAP=swarm-build ;;
    persvati) BASE='$HOME/fn-gates'; WRAP= ;;
    *) echo "remote_check: unknown box '$BOX' (hbox, persvati)" >&2; exit 2 ;;
esac
# The tests point these at a local directory and a local shell.
BASE=${FN_REMOTE_CHECK_BASE:-$BASE}
WRAP=${FN_REMOTE_CHECK_WRAP-$WRAP}
SSH=${FN_REMOTE_CHECK_SSH:-ssh -o ServerAliveInterval=30 -o ControlMaster=auto -o ControlPersist=600 -o ControlPath=~/.ssh/fn-remote-check-%r@%h:%p}

ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || {
    echo "remote_check: not inside a git worktree" >&2; exit 2; }
LANE=${FN_LANE:-$(basename "$ROOT")}
case $LANE in *[!A-Za-z0-9._-]*|'') echo "remote_check: lane name '$LANE' is not a plain word" >&2; exit 2 ;; esac
TREE=${TREE:-$BASE/$LANE-check}
LOG=${LOG:-$BASE/$LANE-check.log}
MIRROR=$BASE/remote-check.git
REF=refs/remote-check/$LANE
HEAD_SHA=$(git -C "$ROOT" rev-parse HEAD) || exit 3
WORK=$(mktemp -d "${TMPDIR:-/tmp}/remote-check.XXXXXX") || exit 3
trap 'rm -rf "$WORK"' EXIT INT TERM

remote() { $SSH "$BOX" "$1"; }

# 1. What the mirror already has, so the bundle carries only the rest.
KNOWN=$(remote "git -C $MIRROR for-each-ref --format='%(objectname)' 2>/dev/null || true") || {
    echo "remote_check: cannot reach $BOX" >&2; exit 3; }
: > "$WORK/revs"
echo "$HEAD_SHA" >> "$WORK/revs"
for sha in $KNOWN; do
    if git -C "$ROOT" cat-file -e "$sha^{commit}" 2>/dev/null; then
        echo "^$sha" >> "$WORK/revs"
    fi
done
if [ -n "$KNOWN" ] && remote "git -C $MIRROR cat-file -e $HEAD_SHA^{commit}" 2>/dev/null; then
    echo "remote_check: $BOX already has $HEAD_SHA"
    remote "git -C $MIRROR update-ref $REF $HEAD_SHA" || exit 3
else
    # A bundle needs a named ref: point a scratch ref at HEAD.
    git -C "$ROOT" update-ref "refs/remote-check/$LANE" "$HEAD_SHA" || exit 3
    sed "s|^$HEAD_SHA\$|refs/remote-check/$LANE|" "$WORK/revs" \
        | git -C "$ROOT" bundle create "$WORK/lane.bundle" --stdin 2>"$WORK/bundle.err" || {
        cat "$WORK/bundle.err" >&2; echo "remote_check: git bundle failed" >&2; exit 3; }
    git -C "$ROOT" update-ref -d "refs/remote-check/$LANE"
    SIZE=$(wc -c < "$WORK/lane.bundle" | tr -d ' ')
    echo "remote_check: bundle of $HEAD_SHA, $SIZE bytes, to $BOX"
    remote "mkdir -p $BASE && { [ -d $MIRROR ] || git init -q --bare $MIRROR; } && cat > $BASE/$LANE.bundle" \
        < "$WORK/lane.bundle" || { echo "remote_check: bundle upload failed" >&2; exit 3; }
    remote "git -C $MIRROR fetch -q $BASE/$LANE.bundle '+$REF:$REF' && rm -f $BASE/$LANE.bundle" || {
        echo "remote_check: the mirror on $BOX refused the bundle" >&2; exit 3; }
fi

# 3. The check tree at exactly that commit.
# A dirty check tree is named, then discarded: it belongs to this script, and
# keeping it is what left AX's make check silently on the old head.
remote "set -e; D=; if [ -d $TREE/.git ]; then cd $TREE
  D=\$(git status --porcelain --untracked-files=all -- . ':!build' | head -20)
else git clone -q --no-checkout $MIRROR $TREE; cd $TREE; fi
[ -z \"\$D\" ] || { echo 'remote_check: the box tree was dirty; discarding:'; echo \"\$D\" | sed 's/^/  /'; }
git fetch -q origin '+$REF:$REF' && git checkout -q -f --detach $HEAD_SHA \
  && git clean -fdq -e build/ && test \"\$(git rev-parse HEAD)\" = $HEAD_SHA" \
    || { echo "remote_check: checkout in $BOX:$TREE failed" >&2; exit 3; }

# 4. Uncommitted tracked changes ride on top; untracked ones are named.
if [ "$DIRTY" = 1 ]; then
    git -C "$ROOT" diff HEAD --binary > "$WORK/dirty.patch"
    if [ -s "$WORK/dirty.patch" ]; then
        echo "remote_check: applying $(git -C "$ROOT" diff HEAD --name-only | wc -l | tr -d ' ') uncommitted file(s)"
        remote "cd $TREE && git apply --whitespace=nowarn" < "$WORK/dirty.patch" || {
            echo "remote_check: the uncommitted changes did not apply on $BOX" >&2; exit 3; }
    fi
fi
UNTRACKED=$(git -C "$ROOT" ls-files --others --exclude-standard | grep -v '^LANEDUMP.md$' | head -20)
[ -z "$UNTRACKED" ] || { echo "remote_check: untracked here, NOT shipped:"; echo "$UNTRACKED" | sed 's/^/  /'; }

# 5. make there, with the box's own toolchain.
ENVS="eval \$(python3 -c 'import ast,os,sys
t=ast.parse(open(\"tools/farm.py\").read())
h=[ast.literal_eval(n.value) for n in t.body if isinstance(n,ast.Assign) and getattr(n.targets[0],\"id\",None)==\"HOSTS\"][0].get(sys.argv[1],{})
print(\"export FN_ACL2=%s FN_CERT_CACHE=%s\" % (h.get(\"acl2\",\"\"), os.path.expanduser(h.get(\"cache\",\"\"))) if h else \"\")' $BOX 2>/dev/null)"
echo "remote_check: make $TARGET in $BOX:$TREE (log $LOG)"
remote "cd $TREE && $ENVS; [ -n \"\${FN_ACL2:-}\" ] || { echo 'remote_check: no FN_ACL2 for $BOX (tools/farm.py HOSTS)' >&2; exit 3; }; { echo \"== remote_check $HEAD_SHA \$(date -u +%FT%TZ) load: \$(uptime)\"; $WRAP make $TARGET 2>&1; echo \"== make exit \$?\"; } > $LOG 2>&1; tail -n 1 $LOG | grep -q '^== make exit 0\$'"
STATUS=$?
remote "cat $LOG" > "$WORK/log" 2>/dev/null
mkdir -p "$ROOT/build/remote-check"
cp "$WORK/log" "$ROOT/build/remote-check/$BOX-$TARGET.log"
MAKE_EXIT=$(sed -n 's/^== make exit \([0-9]*\)$/\1/p' "$WORK/log" | tail -n 1)
[ -n "$MAKE_EXIT" ] || MAKE_EXIT=$STATUS
# The step table check_steps.py prints last, else the log's end.
if grep -q '^== check: ' "$WORK/log"; then
    sed -n '/^== check: /,$p' "$WORK/log" | tail -n 120
else
    tail -n 40 "$WORK/log"
fi

# 6. Generated files back into this worktree.
for path in $FETCH; do
    case $path in /*|*..*) echo "remote_check: --fetch $path: a path inside the tree" >&2; continue ;; esac
    mkdir -p "$ROOT/$(dirname "$path")"
    remote "cd $TREE && tar cf - '$path'" | tar xf - -C "$ROOT" \
        && echo "remote_check: fetched $path" || echo "remote_check: could not fetch $path" >&2
done
echo "remote_check: $BOX make $TARGET exit $MAKE_EXIT at $HEAD_SHA; log build/remote-check/$BOX-$TARGET.log"
exit "$MAKE_EXIT"
}
