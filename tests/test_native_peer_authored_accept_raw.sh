#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
exec "${FN_SBCL:-sbcl}" --noinform --script tests/native_peer_authored_accept_raw.lisp
