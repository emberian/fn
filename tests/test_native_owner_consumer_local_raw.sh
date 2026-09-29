#!/bin/sh
# witness: raw
set -eu
cd "$(dirname "$0")/.."
"${FN_SBCL:-sbcl}" --noinform --script tests/native_owner_consumer_local_raw.lisp
