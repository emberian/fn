#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
exec sbcl --noinform --script tests/native_owner_group_codes_raw.lisp
