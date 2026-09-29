#!/bin/sh
# witness: raw
set -eu
cd "$(dirname "$0")/.."
exec sbcl --noinform --script tests/native_feed_peer_octets.lisp
