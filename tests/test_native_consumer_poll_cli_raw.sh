#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
exec sbcl --noinform --script tests/native_consumer_poll_cli_raw.lisp
