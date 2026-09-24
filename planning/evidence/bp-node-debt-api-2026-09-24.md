# BP received-namespace debt API checkpoint

At source commits `c0babd09` and `6d29b4a1`, `books/bp-node-debt.lisp`
defines the exact §2.1 reference debt for the currently represented FNBS
state: one eventual discard per held row, one pending terminal record, one
result reserved by an active forwarding attempt, three records for a local
whole request not yet delivered, and three per owed application handoff.
Current kind-18 replacement is atomic, so the open-plan term is zero in
`fn-bpnd-debt`; `fn-bpnd-debt-with-plans` exposes the specified
`1 + 3 × unmaterialized children` term for a later persisted-plan state.
The received physical namespace cap is the single
`*fn-bpnf-received-max-records*` constant shared with the namespace planner:
`2 × 4096 = 8192` final names. It is not the volatile operation-id or held
row count. The rotation reserve is explicit and zero for this generation
protocol; the control margin is an ACL2 admission argument.

`fn-bpnd-admitp(used,debt,margin,delta,mode)` requires an actual physical
slot in every mode. A spending record requires
`remaining − D − R − margin ≥ 1 + delta`; a paying record requires negative
`delta` and a slot even if a recovered old history is below cover; a control
record may use the margin but not owed debt. The two admitted arithmetic
theorems show that spending preserves the debt cover and paying preserves an
existing cover. A fully occupied received namespace cannot settle even a
paying record until recovery/rotation provides a slot.

The selected persvati namespace run `run-20260924T050253Z-56b2`,
[manifest](manifests/certify-20260924T050306Z-394216.json), passed the
shared physical bound. The scoped dependency run
`run-20260924T050342Z-f8b7`,
[manifest](manifests/certify-20260924T050348Z-402491.json), installed six
exact-source parent certificates. The debt book run
`run-20260924T050551Z-37f7`,
[manifest](manifests/certify-20260924T050557Z-424764.json), passed. The
fragment test dependency run `run-20260924T051325Z-7936`,
[manifest](manifests/certify-20260924T051330Z-494869.json), passed, followed
by the debt test run `run-20260924T051436Z-b88c`,
[manifest](manifests/certify-20260924T051441Z-507929.json), which passed.
All runs used ACL2 8.7 on persvati, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
one ACL2 job, and exact source/dependency digests in the manifests.

The test book reaches two durable kind-5 receives and a durable kind-7
accepted handoff. Debt moves from 7 to 6: the local request's reserved
three-record future handoff becomes an actual three-record owed handoff,
while its terminal record is paid. A second trace durably receives both
fragments of a local request and applies the existing kind-18 family rule:
two fragments owe four records, while the resulting whole request owes
five, so replacement has `delta = +1` and must spend two free credits
including its own record. Frontier teeth distinguish `F=1` refusal,
`F=2` admission and a result payment at `F=0`; they also show that a new
obligation cannot use the debt-paying margin.

This is a source-present and certified arithmetic API, not a claim that the
native FNBS machine enforces it. The serving engine still needs replay-sourced
`used`, a cached `D`, local deltas for every durable kind-5/6/7/8/9/10/11/18
transition, and a theorem equating that cache to this cold reference. A
prospective forwarding-attempt row demonstrates `+1` then `−1`, but no live
kind-8/9 path or complete N05 counterexample has yet certified. Existing
birth and family publication remain to be gated by the same authority.
