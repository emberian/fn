#!/bin/sh
# witness: raw
set -eu
cd "$(dirname "$0")/.."
exec "${FN_SBCL:-sbcl}" --noinform --script tests/native_syncer_custody_raw.lisp
