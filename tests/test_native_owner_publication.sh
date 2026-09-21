#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
exec sbcl --noinform --disable-debugger --script tests/native_owner_publication.lisp
