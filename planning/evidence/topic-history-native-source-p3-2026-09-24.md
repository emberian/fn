# Experimental P3 local caller source checkpoint, 2026-09-24

This is source qualification, not a saved-image or served-admission claim.
`host/native/control.lisp` decodes the bounded FNCT topic request and calls
the existing `fnn-control-peer-is-owner-p` connected-socket credential gate.
Its second return value is the observed UID; the host does not derive the
topic administrator ID from it. `host/native/owner.lisp` serializes the
request, obtains a fresh 32-octet ID only for installation, and invokes
`fn-owner-topic-propose` in `host/owner-host.lisp`.

The owner wrapper calls the single logical `fn-th-local-propose` dispatcher
with the carried Store topic projection and current transaction coordinate.
The dispatcher selects an earlier exact T10 accepted event and pinned snapshot
from that projection for anchor/report proposals. Its anchor and report
theorems require the earlier accepted event on the successful branch; the
test book exercises install, valid root/report selection, wrong UID and
missing historical source. The publication path stages the ACL2-built event
through the existing owner Store durability gate and reports accepted only
after completion. No caller-supplied Boolean or relay field supplies topic
authority.

The ACL2 local proposal book and test passed on persvati in
[`certify-20260924T020813Z-3039371.json`](manifests/certify-20260924T020813Z-3039371.json).
The bounded FNCT local control book and test passed after using the total
`fn-th-at` accessor for malformed external arguments in
[`certify-20260924T020336Z-2999170.json`](manifests/certify-20260924T020336Z-2999170.json).
Both runs used ACL2 8.7/SBCL 2.6.8 on persvati, two jobs, 150-second
per-book timeout, explicit roots and no closure. `make check` passed after
ledger generation. `tests/test_native_topic_local.py` is staged for a
source-matched image but has not run; it currently covers administrator
install/reopen and missing-source refusal, not a valid root/report native
admission witness. Combined native image, reverse owner closure and physical
source-matched publication evidence remain open. No succession, fork healing,
automatic policy adoption or Mini application operation is inferred.
