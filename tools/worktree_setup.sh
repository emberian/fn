#!/bin/sh
# Make a lane worktree (or any clone) merge fn's registries by row, not text.
#
#   tools/worktree_setup.sh PATH BRANCH [START]   git worktree add PATH (BRANCH,
#                                                 new from START, default
#                                                 origin/dev, when absent), then
#                                                 set it up
#   tools/worktree_setup.sh [--check] [TREE]      set up (or only check) TREE,
#                                                 default the current tree
#
# Setting up registers the fn-registry merge driver (tools/merge_registry.py
# --install: a path relative to the work tree, so each tree runs its own
# driver) and checks that .gitattributes routes every registry to it.  Without
# the driver a plain `git merge origin/dev` merges planning/proofs.json and
# planning/reach-baseline.json as TEXT and silently keeps stale rows and event
# lists (assurance-hygiene-3 merged them field by field by hand, 2026-09-29).
# Exit 0 when the tree is set up, 1 when it is not (with the reason).
set -u

usage() {
    sed -n '2,10p' "$0" | sed 's/^# \{0,1\}//' >&2
    exit 2
}

REGISTRIES="planning/proofs.json planning/requirements.json planning/proof-events.json tests/scenarios/catalog.json planning/reach-baseline.json"

check_only=0
case "${1:-}" in
    -h|--help) usage ;;
    --check) check_only=1; shift ;;
esac

if [ $# -ge 2 ] && [ "$check_only" = 0 ]; then
    path=$1 branch=$2 start=${3:-origin/dev}
    [ -e "$path" ] && { echo "worktree_setup: $path exists; set it up with: $0 $path" >&2; exit 1; }
    if git show-ref --verify --quiet "refs/heads/$branch"; then
        git worktree add "$path" "$branch" || exit 1
    else
        git worktree add -b "$branch" "$path" "$start" || exit 1
    fi
    tree=$path
elif [ $# -le 1 ]; then
    tree=${1:-.}
else
    usage
fi

top=$(git -C "$tree" rev-parse --show-toplevel 2>/dev/null) || {
    echo "worktree_setup: $tree is not a git work tree" >&2; exit 1; }
cd "$top" || exit 1

if [ "$check_only" = 0 ]; then
    [ -f tools/merge_registry.py ] || {
        echo "worktree_setup: $top has no tools/merge_registry.py (merge origin/dev first)" >&2
        exit 1; }
    python3 tools/merge_registry.py --install >/dev/null || exit 1
fi

status=0
python3 tools/merge_registry.py --installed || status=1
driver=$(git config --get merge.fn-registry.driver)
case "$driver" in
    "python3 tools/merge_registry.py "*) ;;
    *merge_registry.py*) echo "worktree_setup: note: the driver runs another tree's copy ($driver), not this tree's; '$0' without --check registers the relative one" >&2 ;;
esac
for file in $REGISTRIES; do
    route=$(git check-attr merge -- "$file" | sed 's/.*: merge: //')
    if [ "$route" != "fn-registry" ]; then
        echo "worktree_setup: $file merges as '$route', not fn-registry: .gitattributes lacks '$file merge=fn-registry'" >&2
        status=1
    fi
done
[ "$status" = 0 ] && echo "worktree_setup: $top: registries merge by row (fn-registry driver registered and routed)"
exit $status
