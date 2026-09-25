# bp-resume-verbs (2026-09-24): resume a stranded row, recover a fenced attempt, a connection-local uncertain transfer

Closes three findings: defaults-precise ("nothing can resume a stranded
row"; "a connect or receive failure after a durable kind 8 stops the whole
BP node, exit 3"), and m4-native-request findings 3 (no verb recovers a
fenced attempt; generic refusal line) and 1's open half (ION retries with
no retry record). Review of 2026-09-24, "Retry budget and duplicate ACK".

## Decisions (all in ACL2)

| decision | where | host call |
| --- | --- | --- |
| A transfer that ends without XFER_ACK/XFER_REFUSE after the durable kind 8 is `:uncertain` (was `:fence`) | `fn-bpnp-tcpcl-outcome`, books/bp-node-progress.lisp | host/native/bp-node.lisp:292, :326 |
| A kind 9 `:uncertain` keeps the slot, headed `:uncertain`, with its count; such a slot is uncertain at every epoch | `fn-bpnp-forward-result-slot`, `fn-bpnp-uncertain-attemptp`, books/bp-forward-attempt.lisp | via `fn-bpnp-step` (bp-service.lisp:170) |
| Resume of a stranded row, or a refusal with its reason | `fn-bpnp-resume-refusal`, `fn-bpnp-operator-resume-step` (`:operator-resume` arm of `fn-bpnp-step`) | bp-node.lisp:356 (`bp-node resume`) |
| `:resumed` kind 9 applies only to a slot stranded at the record's epoch | `fn-bpnp-resume-slot-namesp` in `fn-bpnp-forward-result-matches-heldp` | live persist arm and ordered replay |
| `:resumed` is appended to the kind-9 enum (old frames keep their octets); the `:forward-result` host event admits only transfer outcomes | books/bp-fnbs-forward-codec.lisp, `fn-bpnp-transfer-outcomep` | |
| Recovery outcome for a fenced attempt, or `(:refused reason)` | `fn-bprq-recovery-plan`, books/bp-request-plan.lisp | bp-obligation.lisp:205 via workflow-host.lisp:167 |
| ION attempt journals the `:retry-request` first after a restart | `fn-bprq-ion-attempt-plan` | workflow.lisp:366 via workflow-host.lisp:174 |

**Part 3.** The node-wide stop on an uncertain transfer is gone: that
fault is connection-local. The node still stops when a *publication* is
uncertain (the issued record is `:uncertain`), which is the shared-owner
fault. The confinement theorem
`fn-bpnp-step-emits-no-release-and-no-receipt-prepare`
(books/bp-node-progress-bridge.lisp) still holds with the new arm and
recertified. So do the guard premises (`fn-bpnp-step-preserves-guard-premises`)
and every existing retry keystone in bp-node-forward-retry.

## Theorems

- `fn-bpnp-step-resume-writes-only-for-a-stranded-row`: on
  `(:operator-resume A)`, a proposed durable record is exactly the `:resumed`
  kind 9 naming A, the row's primary identity and its last attempt. It is
  proposed only when the row's slot is stranded for its next hop at the
  current epoch and the row is forward-pending.
  `fn-bpnp-step-resume-refusal-keeps-the-state`: otherwise the answer is
  `(:resume-refused A reason)` and the state is unchanged.
- `fn-bpnp-resumed-result-clears-only-the-slot`: an applying `:resumed` kind 9
  (live or at replay) leaves the same row with slot nil, and only on a
  stranded slot.
- `fn-bpnp-resumed-row-is-a-forward-candidate`: while the bundle is live,
  that row is `fn-bpnp-forward-candidatep` for its next hop at any epoch,
  with the same arrival, next hop and primary identity.
  With `fn-bpnp-forward-scan-offers-the-only-candidate` and
  `fn-bpnp-step-session-offer-is-the-scan-choice`, the next session offers
  it. Not claimed: multi-candidate fairness.
- `fn-bpnp-uncertain-result-keeps-the-count`: after an applying kind 9
  `:uncertain`, the slot has the attempt's retries, the slot is uncertain
  at every epoch, and the row stays forward-pending.
- `fn-bpnp-no-transfer-reads-as-resumed`: the TCPCL reading never yields
  `:resumed`, and the `:forward-result` host event refuses it.
- `fn-bprq-recovery-plan-unfences-and-reopens-as-live`: if the journal
  opens and the plan answers `:recover`, then:
  - `fn-bpiw-apply` accepts the record.
  - The live image has no pending and no fence.
  - The journal with the record appended replays.
  - The next open installs the live image restarted, with ION state
    unchanged.
  - Not claimed: that the operator's `committed|absent` is true. That is
    their out-of-band finding.

## Teeth

- `tests/acl2/bp-node-forward-resume-tests.lisp`, over durable FNBS rows:
  - *bpfr-d4* (four restarts, stranded) is resumed, and replay of the
    `:resumed` frame equals the live held list.
  - The next session's kind 8 names arrival 0 and the original identity,
    sends the original wire, and restarts the count at 0.
  - Every refusal reason, with the state unchanged.
  - Four *in-process* uncertain sessions strand the row without a restart,
    resume works there too, and replay of the kind-9 `:uncertain` frames
    equals live.
  - must-fail: the stranded hypothesis; a `:sent` record; a `:resumed`
    record on a row under the bound; an expired bundle; a `:failed` result.
- `tests/acl2/bp-request-recovery-tests.lisp`, on the 5b journal
  (attempt durable, no outcome):
  - It opens fenced and the request is refused.
  - `committed` and `absent` both unfence it and replay.
  - The next request is accepted, live and after reopen, and its records
    replay.
  - Every refusal reason.
  - must-fail per keystone hypothesis.
  - ION: retry first, the history replays; without the retry, replay
    refuses.
- `tests/acl2/bp-node-forward-retry-tests.lisp`: `fn-bpnp-tcpcl-outcome`
  of `:uncertain` and `:connection-failed` is `:uncertain`.

## Certification (hbox, ACL2 `/tank/fn/toolchains/w28/acl2-literal-4g`, cache `/tank/fn/certcache`, 2 jobs, 300 s)

| run | rev | result | manifest |
| --- | --- | --- | --- |
| farm run-20260925T001336Z-9589 | e12d9def | 14 pass. `bp-node-forward-resume` and its test book failed (fixed after) | `manifests/certify-20260925T001351Z-2225850.json` |
| farm run-20260925T002622Z-9c98 (`--affected-by`, 47 roots) | d8884a58 | 30 pass, including progress, guards, invariants, retry, resume, recovery, codec and replay. Premises failed on the new arm (fixed), and bridge and counterexamples failed with it | `manifests/certify-20260925T002643Z-2239876.json` |
| farm run-20260925T002958Z-a20d (`--affected-by`) | faa8559f | premises and premises-tests pass. Bridge failed on the new arm (fixed) | `manifests/certify-20260925T003019Z-2243169.json` |
| `tools/certify_books.py` in the image tree (budget of three farm runs spent) | 59c20171 | `bp-node-progress-bridge` and `bp-node-counterexamples-tests` pass | `manifests/certify-20260925T003331Z-2245806.json` |

Every touched book is under 10 s. The largest is
`bp-node-forward-lower-guards` at 8.6 s; `bp-node-forward-resume` takes
6.0 s, most of it include time. The DTN profile validated 111 roots
(`result=loaded`) at 59c20171.

## Native (DTN developer image from `git archive 59c20171`, scratch `/tank/fn/scratch/bp-resume/img-tree`)

- Built by [`build-image.sh`](bp-resume-verbs-2026-09-24/build-image.sh). The log has 0 `undefined` lines.
- Launcher `1d05f3b6ecc81492`, core `5d7847f3b0556c62`
  (full hashes in `build.out`).

| module | result | log SHA-256 (16) |
| --- | --- | --- |
| test_bp_node_native (20 tests, 415 s) | OK | `c3db1ff2fcfa58ac` |
| test_bp_obligation_native (5 tests) | OK | `05e28c08d7c7a63c` |

- `test_uncertain_transfer_is_connection_local_and_resume_rearms`. A relay
  severs every forwarding connection after 200 client octets:
  - The node logs `status=uncertain` and keeps serving. It accepts another
    transfer and re-offers the row in the same process.
  - Two more cut dispatches exit 0. The next one reports
    `BP forwarding stranded ... retries=3`.
  - `bp-node resume` of an unknown arrival is refused (`reason=no-row`,
    exit 1, nothing written).
  - `bp-node resume` of the stranded arrival writes one record
    (`status=resumed`). A second resume is refused (`not-attempted`).
  - The next session offers the row, `status=sent`, and the peer holds
    exactly one copy.
- `test_kill_between_attempt_and_outcome_then_recover_committed`:
  - The process is SIGKILLed with the attempt durable (pause selector).
    Status is `outstanding pinned=yes`. The next request is refused and
    the refusal names the fence.
  - Wrong attempt, wrong work and outcome `maybe` are refused with their
    reasons and write nothing.
  - `recover committed` writes one record (`status=unknown pinned=yes`).
    A second recover is refused (`not-fenced`).
  - The next request's attempt is durable.
- This module's log comes from the test file at the lane head. The first
  version waited on a stdout marker that the image does not flush to a
  pipe, and hung for 10 minutes until its request process was killed by
  PID. It now watches the journal. Only the test file changed; the image
  is the same.

## Findings

1. A stranded row is now `(:uncertain ...)`-headed when its last transfer
   failed in-process, or `(:forwarding ...)` from an earlier epoch. Both
   are re-armed the same way. The row strands after four uncertain
   transfers in all (first offer plus three re-offers), not three.
2. The obligation pause marker (`BP OBLIGATION ATTEMPT DURABLE`) is not
   flushed to a pipe before the process ends. A harness should watch the
   journal, as the new test does. The m4 lab ran on a different capture.
3. `bp-node resume` takes the FNBS lifecycle lock, so it must run with the
   node stopped. There is no in-service resume.
4. Not done:
   - An ION native run of `workflow-ion-submit` after a restart. The fix is
     witnessed in ACL2 only.
   - Multi-candidate fairness after resume.
   - The model's own crash point between the `:resumed` publication and its
     `:persist-result` is the existing forwarding-result one, and it was not
     exercised natively.

Stopped by PID: request process 2252387 (lane-started). No pattern kills.
`/tank/fn/node` untouched.
