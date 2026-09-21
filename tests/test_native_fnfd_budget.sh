#!/bin/sh
# Exercise FNFD's production raw directory walk with a small ACL2 policy seam.
set -eu
cd "$(dirname "$0")/.."
exec sbcl --script tests/native_fnfd_budget.lisp
