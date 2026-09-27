#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
exec "${FN_SBCL:-sbcl}" --noinform --script tests/native_live_config_cache_raw.lisp
