# bp-budgets-receipts (2026-09-25): durable busy count, operator budgets, the stranded report, receipts from serve

Lane `lane/bp-budgets-receipts` from dev `3a1dcb34`, merged with dev twice (N16 rotation
and the routed session; then the ten-second lane). **Status: every root the change
affects is certified at the merge's bytes** (runs a412 and 9a3f below; `green_check
--changed-since dev`: 21 changed books, 98 including one, 0 not green). The first
agent's three runs are kept below as history.

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

See "Native (continuation)" below.

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


## Continuation (second agent, 2026-09-25)

### Merges

- `cdd8106e` merges dev (N16 rotation, `(:via HOP ANNOUNCED TABLE)` routing). Both sides'
  step arms, bridge and premises lemmas are kept. The `:session` event is now
  `(:session PEER SESSION OPEN MRU OBSERVATION [VIA] [BUDGETS])`. The two optional
  fields are told apart by tag (`fn-bpnp-session-via`, `fn-bpnp-session-base-length`).
  `fn-bpnp-routed-start` takes the retry budget. The host sends the routed session
  through `fnn-bpnode-budgeted`. The routing keystones in `bp-route-step`
  (`fn-bpnp-step-offers-only-the-routed-hop`,
  `fn-bpnp-step-unrouted-bundle-stays-held-and-is-reported`) now hold for any tail
  EXTRA after VIA, with the scan under the budget the event carries (`fn-bprts-budget`).
  Route tests witness the budgeted routed event.
- `c686852d` merges dev again (ten-second lane). Both sides' guard hints are kept.
- **Slot 13 under rotation.** The kind-19 checkpoint holds the replay's held list
  as one value (`fn-bpnr-checkpoint-of-replay`). `fn-bpnr-checkpoint-decode-of-octets`
  round-trips any value its codec encodes, and `(:busy n)` encodes because keywords and
  naturals do. `fn-bpnr-recover-from-checkpoint-equals-full-recover` equates recovery
  from the checkpoint with whole-history replay, and that replay includes the kind-20
  arm. So a checkpoint carries slot 13 of every held row unchanged. No separate
  theorem was needed. `bp-fnbs-replay-append` needed the kind-20 apply closed in
  its one-row lemma (`9a3a0448`); without that it timed out at 300 s.

### Proof fixes

| book | event | fix |
| --- | --- | --- |
| bp-node-progress-premises | `fn-bpnpp-deferral-persist-step` (the Subgoal 4.2' checkpoint) | the `(:ready HELD ROW)` read `fn-bpnpp-nth-1-of-ready` and the keep form of the held write `fn-bpnpp-premises-kept-by-held-write`, in the minimal defkeep theory |
| bp-node-progress-premises | `fn-bpnpp-session-event-row` (6.8 s) | keep the budget and VIA helpers closed |
| bp-node-progress-guards | `fn-bpnp-host-eventp` | verify the guards of the session helpers first |
| bp-node-progress-guards | `fn-bpnp-busy-wait` (3.6 s) | a type fact for the backoff |
| bp-node-progress-guards | `fn-bpnp-deferral-persist-step` (13.9 s in a clean session) | the minimal theory over `fn-bpnpg-true-listp-of-with-issued` |
| bp-node-forward-retry | `fn-bpnp-attempt-apply-bounds-retries` | the matched row is a true list (forward chaining from `fn-bpnp-attempt-matches-heldp`) |
| bp-node-forward-retry | `fn-bpnp-step-session-offer-is-the-scan-choice` | open the session helpers; this theorem covers the unrouted 6-field event, which the host no longer sends |

Book times at 2 jobs on hbox, from the manifests:

| book | time |
| --- | --- |
| bp-node-progress-guards | 8.4 s (it was 31.5 s in run 3 and 12.9 s before the lane) |
| bp-node-progress-premises | 9.0 s |
| bp-node-forward-retry | 9.3 s |
| bp-node-busy-delivery | 8.6 s |

Still over 10 s: `bp-node-forward-lower-guards` at 10.5 s. The lane touched it, but its
cost is the `bp-fnbs-dispatch-codec` include (3.1 s) plus the guards of
`fn-bpnp-forward-image` (2.4 s) and `fn-bpnp-forward-blocks` (1.7 s). This lane changed none of those.

### Teeth for bp-node-receipt-send (tests/acl2/bp-node-receipt-send-tests.lisp)

**Witness.** A queued and durable base job for the peer. The event is
`(:contact peer t)`. `fn-bpnp-step` persists exactly that job's `:attempting`
record, and the pending success effect is the job's `:cl-send` on its route.

**One separating state per conjunct of the iff:**
- a string peer;
- an issued operation;
- the delivery marker `:delivery-uncertain`;
- the same queued job, fenced;
- the in-flight state (pending);
- another peer with no job.

**Once per contact, at the step.** After the durable `:attempting` record the job is
no longer `:queued`, and the event is nil.

**must-fail cases:**
- the event-non-nil hypothesis;
- the token at `*fn-bpn-machine-max-records*` (the event still opens, and the effect
  is not `:persist`).

### Certification (hbox, w28 `acl2-literal-4g`, cache `/tank/fn/certcache`, 2 jobs, 300 s, `--affected-by books/bp-node-foundation`, 118 roots)

| run | rev | result | manifest |
| --- | --- | --- | --- |
| run-20260925T070339Z-a412 | c686852d | 133 passed. Failed: `bp-fnbs-replay-append` (timed out at 300 s: `fn-bpnr-family-replay-aux-cons` opened the kind-20 apply), and `bp-node-rotation` and `bp-node-counterexamples-tests`, which include it | `manifests/certify-20260925T070406Z-2708294.json` |
| run-20260925T071533Z-9a3f | c996c46a | the 8 remaining roots pass: replay-append 6.6 s, rotation, premises 9.0 s, premises tests, bridge, receipt-send, receipt-send tests, counterexamples tests; the other 110 roots were cached at these bytes from a412 | `manifests/certify-20260925T071636Z-2729359.json` |

### Registry

- `planning/proof-events.json`: PRF-046 gains the durable-count, report, budget and
  retry events. Each note carries the host line and its teeth.
- New target PRF-082 (receipts from `serve`) cites
  `fn-bpnp-receipt-contact-offers-the-queued-job` and
  `fn-bpnp-receipt-contact-event-needs-a-queued-job`. The row is in `planning/proofs.json`.
- **Open:** "offered once per contact" as an ACL2 theorem over the host loop. The host's
  `fnn-bpc-drive-contact` is not an ACL2 driver. The step half (a durable `:attempting`
  record takes the job out of `:queued`) is witnessed, not proved.
- `tools/ledger.py --check` reports only staleness of the generated files (no unknown
  or SUSPECT name). The ledger was not regenerated.

### Host

The `:delivery-stranded` report now names the held row's arrival
(`fn-bpnf-find-held` of the effect's key, looked up by ACL2). That arrival is the
number `bp-node resume` takes.

### DTN image certificates

The dtn profile has 119 roots. Its closure was not fully cached at the merged dev
bytes: 63 books were missing, mostly store/owner books from dev's latest landing.
`farm.py submit` refused the root list at its cache preflight (no count line) without
starting ACL2. I therefore ran the runner the farm drives directly on hbox, in the gate
`/tank/fn/gates/bp-budgets-dtn-d5d558fd` at d5d558fd:

```
swarm-build python3 tools/certify_books.py --incremental --jobs 2 --timeout-seconds 300 <119 dtn roots>
```

with `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g` and
`FN_CERT_CACHE=/tank/fn/certcache`. All 63 passed; the manifest is
`manifests/certify-20260925T072113Z-2744541.json`. After that,
`proof_artifacts.py validate --profile dtn` answers `roots=119 result=loaded` in that
tree. `acquire` into the scratch tree still answered "no complete current artifact
set" (not diagnosed), so the image was built in the gate tree.

### Native (continuation)

Image: `fn-host-dtn-developer` from d5d558fd, built with
`host/native/build-dtn.lisp` under `swarm-build`. The build log has 0 undefined lines.

| file | SHA-256 |
| --- | --- |
| launcher | `21b0024535a88431e93d532065316ed8af91fe93c72ede77ecb8922029c4d33f` |
| core | `d32cb163409264909e8bd248ee6732672766913b0a2a9273293660bd61a9897f` |

The script is [`native.sh`](bp-budgets-receipts-2026-09-25/native.sh). Tests and labs ran
under `systemd-run --user --scope -p MemoryMax=24G`.

**dtn7 app-receipt lab, `--no-contact-tick`.** rc 0 with `--relays 1` (fn A, dtn7 relay,
fn B) and rc 0 with `--relays 0` (control). No `bp-contact tick` ran. B's `serve`
printed `BP node receipt contact peer=dtn://sender/`, and A answered
`BP node delivery receipt-accepted` (outcome `receipt-accepted`). Logs:
`lab-dtn7-no-tick.out`, `lab-control-no-tick.out`.

**`tests.test_bp_node_native`: FAILED.** 13 ok, 11 failures, 537 s
(`test_bp_node_native.log`). All 11 failures are the same new behaviour: exit 3
(uncertain) from a `bp-node dispatch` or `serve` pass that owes a receipt. For example:

```
BP node receipt contact peer=dtn://sender/
TCPCL bp-service aux (:SEND :CONTACT 6)
BP transport work=bp-receipt:receipt:work-bp-node:0 status=attempted
BP forwarding retained reason=uncertain
```

The harness's contact neighbour is a `ByteRelay` with no target. It accepts the TCP
connection and drops it. A socket existed, so the lower machine reads the transfer as
`:uncertain` and the process exits 3. That is the model's answer, not a harness fault.

Affected tests:
- `test_absent_bp_trust_refuses_receipt_release`
- `test_ambiguous_fnrj_decision_fences_until_cold_replay`
- `test_ambiguous_outbox_publication_is_uncertain_not_refused`
- `test_death_after_durable_outbox_does_not_allocate_second_sequence`
- `test_death_after_fnrj_receipt_decision_replays_one_article`
- `test_death_after_kind_seven_replays_owed_outbox`
- `test_deletion_report_intent_recovers_and_observation_does_not_release`
- `test_identity_conflict_is_refused_recorded_and_replayed`
- `test_older_unrouted_transit_does_not_block_younger_local_request`
- `test_request_retry_queues_distinct_receipt_carriers_and_releases_pin`
- `test_permanently_busy_application_strands_row_until_resume`

The last is the new case. It fails only at its final dispatch: the resumed row is
delivered, a receipt becomes owed, and that pass exits 3. Before that point its new
assertions passed:
- the busy count strands at 3;
- two restarts each report `stranded busy=3 arrival=N` once and never redeliver;
- `bp-node resume N` answers `BP node delivery resumed`.

`test_busy_application_defers_and_redelivers_after_backoff`,
`test_rotation_killed_at_each_cut_keeps_held_rows` and
`test_uncertain_transfer_is_connection_local_and_resume_rearms` pass.

## Findings (continuation)

5. **Receipts from `serve` make the neighbour's transport uncertainty the whole node's.**
   `fnn-bpnode-send-receipts` runs in both `serve` and `dispatch`. When the lower machine's
   base transfer is `:uncertain`, the process answers exit 3. Forwarding is different: an
   uncertain transfer is connection-local by spec 4.3.1 (the kind 9 keeps the count and the
   node keeps serving). The base contact has no such rule. The honest repair is in the
   model: give the base receipt transfer a connection-local uncertain outcome, with its
   theorem, the way 4.3.1 does for forwarding. Changing the tests' expectations or
   dropping `dispatch` from the send would hide the defect. This lane stops here with
   the native module red for this one reason.
6. The stranded report did not name the arrival that `bp-node resume` needs. It does now.
