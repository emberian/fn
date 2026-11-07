#!/bin/sh
# Certify books on bb2 (dregg-build2) from any worktree: rsync this tree to
# bb2:~/fn2-<name>/, run tools/certify.sh there under swarm-build, and sync
# the certificates back. Usage, from the worktree root:
#   tools/box_certify_bb2.sh <name> [-j N] books/foo.lisp tests/foo-unit.lisp ...
# <name> is the lane's name (one remote tree per lane; never share one).
# SWARM_MEM_MAX (default 20G) caps the job's memory on the box; keep the sum
# of running lanes' caps under the box's budget (MACHINES.md). The run is
# foreground: wrap it in nohup/setsid with a PID file for anything long.
# The remote certify keeps going past a red book (cert.pl --keep-going), streams
# each Built line as it happens, ends with "certify summary: N built, M failed"
# naming each red book and each target not built behind one, and while it runs
# its PID is in bb2:~/fn2-<name>/build/fn2-certify.pid (beside its lock).
set -eu
name=${1:?lane name}; shift
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
remote=fn2-$name
ssh_opts="-o ServerAliveInterval=10 -o ServerAliveCountMax=3"
# Content sync without mtimes: a changed file gets a fresh remote mtime, so make recertifies
# exactly its closure; an old local mtime can no longer hide behind a newer remote cert.
rsync -rlpgoDz --checksum -e "ssh $ssh_opts" --exclude='.git' --exclude='build' --exclude='*.fasl' \
  --exclude='*.cert' --exclude='*.cert.out' --exclude='meta/.lake' \
  "$root/" "bb2:~/$remote/"
# A red run still syncs its .cert.out back (the failing book is readable locally); the exit
# status is the certify's.
rc=0
ssh $ssh_opts bb2 "cd ~/$remote && SWARM_MEM_MAX=${SWARM_MEM_MAX:-20G} swarm-build env \
  ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k ACL2_SYSTEM_BOOKS=/tank/fn/acl2-8.7/books \
  ACL2_PROJECTS=/home/build/$remote/acl2-projects ACL2_BOOK_HASH_ALISTP=NIL sh tools/certify.sh $*" || rc=$?
for d in books tests sim meta/emit; do
  rsync -az -e "ssh $ssh_opts" --include='*/' --include='*.cert' --include='*.cert.out' \
    --include='*.port' --exclude='*' "bb2:~/$remote/$d/" "$root/$d/" 2>/dev/null || :
done
exit $rc
