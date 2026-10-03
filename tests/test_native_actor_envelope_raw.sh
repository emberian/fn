#!/bin/sh
# witness: raw
set -eu
cd "$(dirname "$0")/.."
exec "${FN_SBCL:-sbcl}" --noinform --script tests/native_actor_envelope_raw.lisp
