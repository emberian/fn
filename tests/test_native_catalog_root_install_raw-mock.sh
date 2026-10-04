#!/bin/sh
# witness: raw (mock: recording ACL2 seams; cited by no claim)
set -eu
cd "$(dirname "$0")/.."
exec "${FN_SBCL:-sbcl}" --noinform --script tests/native_catalog_root_install_raw-mock.lisp
