#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
sbcl --noinform --script tests/native_consumer_peer_raw.lisp
