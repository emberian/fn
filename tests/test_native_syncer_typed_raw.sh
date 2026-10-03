#!/bin/sh
# witness: raw
set -eu
cd "$(dirname "$0")/.."
mkdir -p build/runtime-tests
log=build/runtime-tests/native-syncer-typed.log
# Includes are deliberately scoped, with no image build or closure request.
# The resulting raw run is a native correspondence witness, not a proof.
tools/acl2 --timeout 90 --wait-seconds 30 --label runtime-typed-syncer >"$log" 2>&1 <<'ACL2'
(include-book "books/resource-syncer")
(include-book "books/owner-queued-work")
(include-book "books/definterface")
(definterface create-fn-resource-ledger :class :common-lisp-compliant
  :raw-guarded (0 nil (fn-resource-ledger)))
(defttag :fn-runtime-typed-fixture)
(progn! (set-raw-mode t) (load "tests/native_syncer_typed_raw.lisp"))
(good-bye)
ACL2
if ! rg -q '^native_syncer_typed_producer_raw: PASS' "$log"; then
  tail -70 "$log"
  exit 1
fi
rg '^native_syncer_typed_producer_raw: PASS' "$log"
