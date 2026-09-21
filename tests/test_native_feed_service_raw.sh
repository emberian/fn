#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
sbcl --noinform --script tests/native_feed_service_raw.lisp
