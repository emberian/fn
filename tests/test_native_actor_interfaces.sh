#!/bin/sh
# witness: ACL2 loaded-world interface association, no native image
set -eu
cd "$(dirname "$0")/.."
mkdir -p build/runtime-tests
PYTHONPATH=. python3 tests/actor_interface_input.py > build/runtime-tests/actor-interfaces.lsp
tools/acl2 --timeout 90 --wait-seconds 30 --label runtime-actor-interfaces \
  < build/runtime-tests/actor-interfaces.lsp > build/runtime-tests/actor-interfaces.log 2>&1
if rg -q 'ACL2 Error|HARD ACL2 ERROR' build/runtime-tests/actor-interfaces.log || \
   ! rg -q ':ACTOR-INTERFACE-BATCH-PASS-' build/runtime-tests/actor-interfaces.log; then
  tail -70 build/runtime-tests/actor-interfaces.log
  exit 1
fi
rg ':ACTOR-INTERFACE-BATCH-PASS-|:WRONG-LITERAL-SUBJECTS-REFUSED' build/runtime-tests/actor-interfaces.log
