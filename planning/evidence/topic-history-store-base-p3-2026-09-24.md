# Experimental P3 topic Store base, 2026-09-24

The fixed-controller experiment now has an ACL2 Store slot-12 projection for
one immutable local administrator install and bounded root/report admissions.
`fn-sn-prepare-topic` checks the carried historical T10 source and snapshot;
`fn-sn-finish` completes only the validated topic event. The positive
`fn-sn-finish-topic-completion` theorem says this completion advances the exact
Store sequence/transaction and topic projection while preserving article
acceptance contents. `fn-snt-prepare-topic-preserves-relation` extends the
mixed-trace relation's deferred arm to the actual topic prepare transition.

Two older statements required explicit scope corrections. A successful Store
completion no longer implies an **article** record binding when the completed
event is a topic installation or admission; the article-only conclusion in
`fn-snrt-new-success-is-actual-matching-durable-completion` therefore has a
`not fn-th-topic-eventp` premise. A structurally valid, article-replayable
image can have a duplicate administrator install; identity and consumer replay
also accept it, but topic replay faults. The observed reopen guarantees now
require `fn-sn-observed-topic-okp` alongside those other replay conditions.
`tests/acl2/store-observed-tests.lisp` constructs that two-install image and
checks the actual `fn-sn-open-observed` result is `(:error :replay)`.

The shared `fn-sn-with-configuration` updater preserves the file, consumer,
topic, and other unselected Store slots; named selector theorems expose its
four intentionally changed fields. Configuration observed-open carries the
topic replay result and uses the guarded ACL2 `fn-th-at` accessor. Historical
replay never reauthorizes old admissions against the process's current UID.

On exact source branch `integrate/topic-store-base` at `d3f8b97a`, persvati
run `run-20260924T015437Z-acc4` requested 13 explicit Store, trace,
resolution, observed-open and test roots with ACL2 8.7/SBCL 2.6.8,
Python 3.13.7, two jobs, 150-second per-book limit, and no `--closure`.
Eight roots installed at matching source/toolchain digests from the shared
cache and five newly certified; all passed in
[`certify-20260924T015446Z-2921507.json`](manifests/certify-20260924T015446Z-2921507.json).
The earlier source-matched scoped manifests for the Store dependents,
configuration book/test and observed refusal witness are
[`014310`](manifests/certify-20260924T014310Z-2817166.json),
[`014931`](manifests/certify-20260924T014931Z-2875258.json) and
[`015132`](manifests/certify-20260924T015132Z-2893327.json).
`make check` passed after ledger generation. The broad reverse closure,
combined saved image, authenticated native install/publication call and
source-matched native scenario remain separate qualification work. No
succession, fork resolution, automatic policy adoption, or Mini application
authorization is implied.
