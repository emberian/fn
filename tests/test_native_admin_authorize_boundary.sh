#!/bin/sh
# witness: raw
set -eu
cd "$(dirname "$0")/.."
exec "${FN_SBCL:-sbcl}" --noinform --script tests/native_admin_authorize_boundary.lisp
