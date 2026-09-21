#!/bin/sh
# Run raw-native retry/progress tests without a Python node or launcher.
set -eu
cd "$(dirname "$0")/.."
exec sbcl --script tests/native_io_progress.lisp
