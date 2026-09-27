#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
"${FN_SBCL:-sbcl}" --noinform --script tests/native_consumer_peer_raw.lisp
