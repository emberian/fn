#!/bin/sh
set -eu

test_dir=${TMPDIR:-/tmp}/fn-native-crypto-saved-image.$$
core=$test_dir/core
trap 'rm -rf "$test_dir"' EXIT HUP INT TERM
mkdir -p "$test_dir"

FN_CRYPTO_TEST_CORE=$core sbcl --noinform --disable-debugger \
  --script tests/native_crypto_saved_image.lisp
sbcl --noinform --core "$core" --disable-debugger
