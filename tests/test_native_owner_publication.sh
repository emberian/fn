#!/bin/sh
# witness: raw
set -eu
cd "$(dirname "$0")/.."
exec "${FN_SBCL:-sbcl}" --noinform --disable-debugger --script tests/native_owner_publication.lisp
