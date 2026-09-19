#!/bin/bash
# Graceful single-node shutdown: the daemons this node started, and only those.
set -eu
. "$(dirname "$0")/env.sh"
cd "$1"
bpadmin . || true
sleep 1
ltpadmin . || true
sleep 1
ionadmin . || true
