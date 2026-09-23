#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
exec sbcl --noinform --script tests/native_owner_consumer_raw.lisp
