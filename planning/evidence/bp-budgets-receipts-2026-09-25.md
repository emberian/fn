# bp-budgets-receipts (2026-09-25): durable busy count, operator budgets, the stranded report, receipts from serve

Lane `lane/bp-budgets-receipts` from dev `3a1dcb34`. **Status: not green.**
The farm budget (three runs) is spent with three books still failing (below).
No native run was made.

## What changed

- **Durable busy count (kind 20).** `(:bpnf-deferred epoch op arrival identity count)`
  (`books/bp-forward-attempt.lisp`, codec in `books/bp-fnbs-forward-codec.lisp`,
  publication in `books/bp-fnbs-forward-publication.lisp`, replay arm in
  `books/bp-fnbs-family-replay.lisp`). The count lives in the local row's slot 13 as
  `(:busy n)`. A busy answer proposes the kind 20 (`fn-bpnp-busy-delivery-step`); its
  persist arm (`fn-bpnp-deferral-persist-step`) applies it with `fn-bpnp-deferral-apply`,
  which replay also calls. Only the backoff reading stays volatile. `:deferral` joins
  `fn-bpnf-operationp` (foundation). Kind 19 is left for n16's checkpoint.
- **Forward retry count.** It was already durable (kind 8/9 through slot 13). What changed:
  applying a kind 8, or a `:resumed` kind 9, now needs only an uncertain slot. The budget
  is checked only when the live node proposes (`fn-bpnp-forward-candidatep`,
  `fn-bpnp-resume-refusal`), so a budget the operator changes later cannot make the
  journal unreplayable.
- **Stranded report on every tick.** `fn-bpnp-progress-step` answers
  `(:delivery-stranded key n)` for the oldest busy-stranded row whenever it selects
  nothing else. `fnn-bpnode-dispatch-one` prints it and ends the pass. I chose this over a
  `bp-node status` line because the spec's report is a progress effect.
- **Operator budgets (D27).** Optional rows `owner-backoff N` and `retry-budget N` go in
  `JOURNAL/bp-node-budgets`. The host bounds the text (`fnn-bpnode-read-budgets`). ACL2
  owns the defaults (5000 ms and 3) and validates both values
  (`fn-bpnp-configured-budgets`, `fn-bpnp-budgetsp`: frame naturals, budget ≥ 1). The
  budgets travel as the optional last field of `:progress`, `:session`, `:resume`, the
  busy `:deliver-result` and `:operator-resume` (`fn-bpnp-budgeted-lengthp`).
- **Resume of a busy strand.** `:operator-resume` on a busy-stranded row proposes kind 20
  with count 0 (`fn-bpnp-busy-resume-step`).
- **Receipts from serve.** `fnn-bpnode-send-receipts` (host/native/bp-node.lisp) runs
  after each `fnn-bpnode-queue-outboxes`. It asks `fn-bpnp-receipt-contact-event`
  (`books/bp-node-receipt-send.lisp`) and drives the base contact as `bp-contact tick`
  does. In `fnn-bps-send-effect`, a connect that never produced a socket is now
  `:failed` (no octet left). This keeps an unreachable neighbour from turning `serve`
  uncertain.

## Theorems (subject is what the host calls)

| theorem | statement | host line |
| --- | --- | --- |
| `fn-bpnp-step-busy-delivery-proposes-its-count` | for the busy event with matching marker, epoch and nothing issued: held rows unchanged, marker cleared, and either the one effect is `:persist-deferral` of the kind 20 with count 1 + the row's count and that record issued `:pending`, or nothing is issued and the answer is `:progress-wait` | `fnn-bpnode-dispatch-one` → `fnn-bps-foundation-step` → `fn-bpnp-step` |
| `fn-bpnp-step-deferral-durable-applies-the-replay-function` | the durable `:persist-result` of an issued `:deferral` leaves held = `fn-bpnp-deferral-apply` of that record | same |
| `fn-bpnp-busy-count-after-recovery-is-the-live-count` | if the journal ROWS replay (`fn-bpnf-family-replay-rows`) to the live held list and ROW decodes to the live issued kind 20 (name and order hold), then the held list after the live durable arm equals the replay of ROWS then ROW. With `fn-bpnp-host-recovery-installs-the-durable-replay`, the count after restart is the live count | `fn-bpnf-family-recover-auto-event` (bp-service.lisp:827) and the step |
| `fn-bpnp-progress-reports-a-stranded-row` | progress entry conditions, nothing selectable, nothing uncertain, and some held row stranded: the effect is the report of the oldest stranded row with its count, and held is unchanged | `fnn-bpnode-dispatch-one` |
| `fn-bpnp-busy-stranded-row-is-not-offered`, `fn-bpnp-busy-deferral-ends-at-its-reading` | restated over the configured budget | progress selection |
| `fn-bpnp-forward-scan-offers-a-candidate`, `fn-bpnp-attempted-held-counts-one-more`, `fn-bpnp-attempt-apply-bounds-retries`, `fn-bpnp-step-attempt-persist-preserves-the-retry-bound` | retry budget restated: the scan offers only candidates under the budget; each durable kind 8 counts exactly one more; the bound is kept for a row that was under it | `fnn-bpnode-forward-contact` |
| `fn-bpnp-receipt-contact-event-needs-a-queued-job` | the event is non-nil iff peer is an EID, nothing is issued, no delivery is uncertain, the base is neither fenced nor pending, and a `:queued` job for that peer exists | `fnn-bpnode-send-receipts` |
| `fn-bpnp-receipt-contact-offers-the-queued-job` | over `fn-bpnp-step (:base event)`: the one proposal is `:attempting` for the first queued job to the peer, and its success effect is that job's `:cl-send` (route, peer, key, wire) | same |

Not claimed: once per contact as an ACL2 statement (it rests on the host loop and the job
status), and multi-candidate fairness.

## Teeth (tests/acl2/bp-node-counterexamples-tests.lisp, BP-R17 section, rewritten)

**Reachable trace.** Three busy answers go through `fn-bpnp-step`, each followed by its
durable kind 20:
- effects: deferred 1 at 6000, deferred 2 at 11000, then stranded 3;
- slot 13 goes `(:busy 1)` … `(:busy 3)`;
- two later ticks each report the strand.

**Byte replay.** The journal's kind-5 frame plus three kind-20 frames replays to the live
held list. A restart through `fn-bpnf-family-recover-auto-event` holds `(:busy 3)` and
reports the strand; it does not redeliver.

**Resume.** The resume writes count 0, the next tick delivers, and a resume under the
budget is refused.

**Budgets.**
- A retry budget of 2 strands at 2.
- A retry budget of 5 still defers at 3.
- A backoff of 100 gives a deferral at 1100.
- A zero retry budget is refused by `fn-bpnp-configured-budgets` and by `fn-bpnp-host-eventp`.

**must-fail cases.**
- Replay without the last row (count 2 ≠ 3).
- Rows out of order: replay faults.
- A count that is not one more: apply faults.
- Proposal: wrong marker op, an issued operation, another epoch.
- The blocked reading at the budget.
- The report replaced by a delivery.

The retry and resume tests take the budget argument. The retry teeth now show that a kind 8
at the bound applies at replay while the live proposal refuses it (`fn-bpnp-under-budgetp`).

**Not written:** teeth for `bp-node-receipt-send` (a base-job witness).

## Certification (hbox, `/tank/fn/toolchains/w28/acl2-literal-4g`, cache `/tank/fn/certcache`, 2 jobs, 300 s, `--affected-by books/bp-node-foundation --affected-by books/bp-forward-attempt`, 111 roots)

| run | rev | result | manifest |
| --- | --- | --- | --- |
| run-20260925T062001Z-6e69 | f50eacad | `bp-node-forward-lower-guards` failed on the `fn-bpnp-busy-slot` guard (`zp`), and everything above it failed with it | `manifests/certify-20260925T062025Z-2652547.json` |
| run-20260925T062717Z-2f83 | 5ed73f31 | foundation, attempt, codecs, replay, publication, progress, busy-delivery 8.2 s and lower-guards 9.8 s pass. Failed: premises (busy arm), forward-retry (count lemma), and receipt-send, bridge, resume and tests with them. progress-guards 32 s | `manifests/certify-20260925T062741Z-2664373.json` |
| run-20260925T063429Z-6629 | bd6ff1ca | still failing: `bp-node-progress-guards` (the `fn-bpnp-deferral-persist-step` guard, a `true-listp` of `fn-bpnp-with-credit` hidden by my disable, 31.5 s); `bp-node-progress-premises` (`fn-bpnpp-deferral-persist-step`); `bp-node-forward-retry` (`fn-bpnp-attempted-held-retries-within-bound`, arithmetic in ground-zero). The dependents failed with them | `manifests/certify-20260925T063455Z-2675359.json` |

Commit `0f590a4a` fixes two of the three: it removes the disable that hid `with-credit`'s
`true-listp`, and it adds the `attempt-retries` type to the retry lemma. **These fixes are
uncertified.** `fn-bpnpp-deferral-persist-step` still needs its hint theory fixed; the farm
checkpoint is Subgoal 4.2' in `books--bp-node-progress-premises.certify.log`. It proved in
the hbox `ld` session, which does not prove guards.

`bp-node-fragment-step` took 15.5 s in run 1 and 9.7 s in run 2. I did not change it.

Iteration ran in an hbox `tools/acl2` session through `ld`, with proofs skipped for
unchanged books. In that session every changed theorem book loads, and the counterexample,
retry and resume tests pass. That is not certification.

## Native

Not run: no DTN developer image was built from this branch. The lab option
`tests/bp-dtn7/run_fn_dtn7_app_receipt.py --no-contact-tick` exists but has not been run.

## Findings

1. The busy deferral was volatile by design. It is now a durable kind (20), so restarting
   a stranded row no longer gives it fresh tries. That is proved by
   `fn-bpnp-busy-count-after-recovery-is-the-live-count` and witnessed on bytes; it still
   needs certification.
2. A replay that checked the budget would make the journal unreplayable when an operator
   lowers it. The apply is now budget-free and the proposal checks the budget.
3. Sending receipts from `serve` made an unreachable neighbour turn the whole node
   uncertain (exit 3). A connect with no socket now reads `:failed`, and ACL2 requeues the
   job. `bp-contact tick` changes the same way.
4. n16's rotation checkpoint must carry slot 13 of every held row verbatim; the busy
   count is there now.
