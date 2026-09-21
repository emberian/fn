# Handoff: w18/bp-lifecycle-assurance — PRF-046 actual dispatcher invariants

Functional source commit `ff80403` is based on `df89f77`.  Evidence and this
handoff follow in a documentation-only commit.  No proof or requirement
registry was edited; the integrator owns those generated-ledger changes.

The batch adds `books/bp-node-machine-invariants.lisp`,
`books/bp-node-machine-authorization.lisp`, and
`tests/acl2/bp-node-machine-authorization-tests.lisp` to the declared ACL2
roots.  It also changes `fn-bpn-contact-step` so a contact observation is a
no-op while persistence is pending or the state is fenced.  That closes the
concrete violation in which an otherwise valid contact event changed contacts
while an unresolved publication obligation prohibited state mutation.

The public maintained predicate is `fn-bpn-lifecycle-invariantp`.  It implies
`fn-bpn-machine-invariantp`, and therefore `fn-bpn-machine-statep`, so callers
that carry the lifecycle invariant may discharge logical whole-state validity
without adding a native scan.  `fn-bpn-step-preserves-lifecycle-invariant`
proves preservation by the actual dispatcher used at
`host/native/bp-service.lisp:102`.  `fn-bpn-trace-preserves-lifecycle-invariant`
extends it to bounded-event traces.

`fn-bpn-step-cl-send-is-authorized-by-durable-attempt-record` binds every
observed send to the exact current pending token, a `:durable` persistence
result, an applicable `:attempting` record, and the retained job's exact route,
peer, key and wire.  `fn-bpn-step-queue-acceptance-is-durable-or-exact-duplicate`
separates newly durable acceptance from idempotent acknowledgement of an exact
existing job.  `fn-bpn-step-effects-are-typed` derives effect typing directly;
the actual effects unconditionally contain neither `:release` nor
`:receipt-prepare`.

The reachable witness and all hypothesis teeth are in the new test book.  The
exact certification transcript and limits are recorded in
[`bp-lifecycle-assurance-w18-2026-09-21.md`](../evidence/bp-lifecycle-assurance-w18-2026-09-21.md).

Integration order is:

1. `f4d061d2` — record application preservation and pending/fenced contact
   fence;
2. `ec64c5d3` — actual effect typing and enqueue preservation;
3. `29c8d8b2` — actual `fn-bpn-step` machine-invariant preservation;
4. `ff80403e` — exact pending authorization, lifecycle preservation, reachable
   restart witness, teeth, and declared book roots;
5. the documentation-only evidence commit after that functional range.

The strongest remaining PRF-046 gap is physical/native correspondence for the
host observation reported as `:durable`; these ACL2 theorems intentionally do
not turn filesystem promises into hardware facts.  The packet also does not
address the known cost of existing `fn-bpn-step` state recognition or add a
native build/runtime test.  It adds no second lifecycle machine and changes no
wire format, record codec, persistence outcome tags, or publication protocol.
