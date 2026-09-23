#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
sbcl --noinform --script tests/native_owner_consumer_local_raw.lisp
