#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
exec sbcl --noinform --script tests/native_live_config_cache_raw.lisp
