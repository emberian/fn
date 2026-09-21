#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
exec sbcl --noinform --script tests/native_owner_bound_commit_raw.lisp
