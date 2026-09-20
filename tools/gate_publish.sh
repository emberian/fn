#!/bin/sh
# Publish a finished gate directory's certificate pairs into the box's cache.
#
# A gate is a fresh directory made from one commit, certified once, and never
# edited or certified into again.  That is what `--origin-kind gate` records:
# `tools/certs.py install` may then take these pairs anywhere on this box,
# including while the gate directory is still on disk, where the ordinary
# origin rule would refuse them as `foreign-local` (a live worktree's absolute
# sub-book paths must not be followed from another tree).
#
# Add this as the last line of a gate script, after `make certify` and the
# Python tests:
#
#     sh tools/gate_publish.sh
#
# The cache is the first argument, else $FN_CERT_CACHE, else ~/fn-certcache.
# Nothing here proves a book certifies: `publish` caches a pair only when the
# run's own manifest still vouches for both the source and the certificate.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cache=${1:-${FN_CERT_CACHE:-$HOME/fn-certcache}}
exec python3 "$root/tools/certs.py" publish \
  --root "$root" --cache "$cache" --origin-kind gate
