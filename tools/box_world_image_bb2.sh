#!/bin/sh
# Build the saved world images (tools/cert_images.py, its fn2 section) on bb2
# from a lane's certified remote tree bb2:~/fn2-<name>/ (certify the roots there
# first: tools/box_certify_bb2.sh <name> books/executor.lisp ...). Usage:
#   tools/box_world_image_bb2.sh <name> [image ...]     # default: every image in tools/cert-images.json
# The build runs detached under swarm-build, holding the tree's certify lock;
# it prints its log, PID file and done file (bb2:~/fn2-images/logs/), and the
# done file holds the build's exit status when it ends. Each image lands in
# bb2:~/fn2-images/<image>-<key>/ (acl2 launcher, saved.core, meta.json, DONE);
# an image already built for the tree's key is not rebuilt; the two newest
# generations of each image are kept. Stop it only by the PID in its PID file.
set -eu
name=${1:?lane name}; shift
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
remote=fn2-$name
rev=$(git -C "$root" rev-parse --short HEAD 2>/dev/null || echo unknown)
stamp=$(date -u +%Y%m%dT%H%M%SZ)
logs=/home/build/fn2-images/logs
base=$logs/$name-$stamp
timeout 60 ssh -o ServerAliveInterval=10 -o ServerAliveCountMax=3 bb2 "mkdir -p $logs && cd ~/$remote && \
  (setsid nohup swarm-build env ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k \
    ACL2_SYSTEM_BOOKS=/tank/fn/acl2-8.7/books ACL2_PROJECTS=/home/build/$remote/acl2-projects \
    ACL2_BOOK_HASH_ALISTP=NIL sh -c 'until mkdir build/fn2-certify.lock 2>/dev/null; do sleep 5; done; \
      rc=0; timeout 7200 python3 tools/cert_images.py world-build --rev $rev $* || rc=\$?; \
      rmdir build/fn2-certify.lock; echo \$rc > $base.done' \
    > $base.log 2>&1 < /dev/null & echo \$! > $base.pid) && \
  echo log $base.log pid \$(cat $base.pid) done $base.done"
