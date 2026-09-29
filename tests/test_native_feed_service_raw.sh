#!/bin/sh
# witness: raw
set -eu
cd "$(dirname "$0")/.."
"${FN_SBCL:-sbcl}" --noinform --script tests/native_feed_service_raw.lisp
