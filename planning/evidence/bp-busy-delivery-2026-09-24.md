# BP-R17 busy delivery, and :conflict in fn-bpnf-operationp (2026-09-24)

Lane p11-n16-r17, branch `lane/p11-n16-r17` from dev `ac572eb4`; commits
`7281e76f`, `27636fec`, `110619e0` and the evidence commit.

## What changed

- The machine (`books/bp-node-progress.lisp`, `fn-bpnp-step`): the event
  `(:deliver-result epoch op key :busy detail obs)` goes to
  `fn-bpnp-busy-delivery-step`. It clears the delivery marker (slot 7) and
  sets the volatile wait `(:bpnp-wait key :busy n m)` in slot 11, where
  `m` = monotonic + `*fn-bpnp-owner-backoff*` (5000 ms). Nothing is proposed.
  The effect is `(:delivery-deferred key n m)`, or `(:delivery-stranded key n)`
  once `n` reaches `*fn-bpnp-max-forward-retries*` (3). Progress selection
  skips a row with a live busy wait (`fn-bpnp-busy-blockedp`).
- Theorems (`books/bp-node-busy-delivery.lisp`):
  - `fn-bpnp-step-busy-delivery-defers`: for the busy event, a
    `true-listp` state, a matching marker, the epoch, and nothing issued,
    the state after `fn-bpnp-step` is `st` with only slots 7 and 11
    written. Held rows, handoffs, outcomes, `next-op` and credit are
    unchanged, nothing is issued, and the one effect is the deferral or the
    stranded report.
  - `fn-bpnp-busy-deferral-ends-at-its-reading`: below the bound, the wait
    does not block at any reading ≥ `m`.
  - `fn-bpnp-busy-stranded-row-is-not-offered`: at the bound, the row is
    never the selection that `fn-bpnp-oldest-eligible-with-credit` returns
    (the function `fn-bpnp-progress-step` calls).
- Carried invariants: `fn-bpnp-step-preserves-guard-premises` (premises)
  and `fn-bpnp-step-emits-no-release-and-no-receipt-prepare` (bridge) both
  cover the new arm.
- `fn-bpnf-operationp` lists `:conflict`. `fn-bpnf-conflict-operation-shapep`
  is now an operationp, and the kind-14 keystone concludes it.
- Host:
  - `fn-owner-app-plan-install` (host/bp-native-app-host.lisp) answers a
    `(:busy reason)` plan `:busy` (it used to answer `:refused`).
  - `fnn-bpapp-accept-locked` (host/native/bp-app.lisp) returns that `:busy`.
  - `fnn-bpnode-request-result` maps `:busy` to `:busy`. It used to fall
    through to `:uncertain`.
  - `fnn-bpnode-dispatch-one` (host/native/bp-node.lisp) issues the
    seven-field event with its observation.
  - `fnn-bps-drive-effects` prints the two new effects.
  - Developer selector `FN_BP_NODE_TEST_APP_BUSY=N` makes the first N
    application answers `:busy`.

## Certification (hbox, `/tank/fn/toolchains/w28/acl2-literal-4g`, 2 jobs)

| run | roots | result | manifest |
| --- | --- | --- | --- |
| 20260925T000022Z-42e6 | `--affected-by books/bp-node-foundation` (110 books) | 106 passed; premises, bridge, premises-tests, counterexamples failed on the new arm | certify-20260925T000044Z-2212223 |
| 20260925T000719Z-3713 | `--affected-by books/bp-node-progress-premises` | premises 5.8 s, premises-tests 5.3 s passed; bridge failed | certify-20260925T000737Z-2218458 |
| 20260925T000928Z-e637 | `--affected-by books/bp-node-progress-bridge` | bridge 5.0 s, counterexamples 5.6 s passed | certify-20260925T000946Z-2220457 |
| 20260925T001211Z-54a2 | store-history-marker, native-admin, native-config-observation, native-operator (dev drift from ac572eb4, needed for the image) | 4 passed, native-admin 9.8 s | certify-20260925T001223Z-2223797 |

Changed books: foundation 2.2 s, progress 5.4 s, progress-guards 8.8 s,
busy-delivery 5.5 s, conflict-publication 3.1 s, machine-gaps 6.5 s. The
slowest book in the first run was bp-node-forward-lower-guards at 9.1 s. No
book reached 10 s.

## Native tests (hbox `/tank/fn/scratch/p11-n16`, DTN developer image)

The image is `fn-host-dtn-developer` (core sha256 `021f1b9b9923475c…`), built
from the tree at `110619e0` with a composed artifact set (`8a02bb4d…`, 294
books).

- `tests.test_bp_node_native`: 20/21 on the first pass (log `3e57f6a9`). The
  one failure was the new busy test's own over-broad assertion, which matched
  `uncertain=0` in the TCPCL summary. After the fix, both BP-R17 cases pass
  (2/2, log `4dd014afb`):
  - busy then redelivery after the backoff: one article;
  - three busy answers strand the row: no refusal and no article; a cold
    recovery then delivers it.
- `tests.test_bp_service_native` 15/15 (log `b00f763d`).
- `tests.test_bp_app_native` 5/5 (log `e94a3072`).

## Limits

- The busy count is volatile, like every wait: a restart gives a stranded
  row a fresh budget of three.
- The stranded report is emitted once, at the third busy answer. Progress
  does not repeat it.
- The backoff is a constant in the book, not a configuration input.
- `:uncertain` from the application keeps its existing fence (recovery
  first). It does not take the `(:after m)` wait that spec 4.2 first named
  for it.
- The native busy source is a developer selector at the bp-node application
  boundary. No test drives a real `(:blocked)` dispatcher or `:defer` peer
  decision natively.
- N16 (rotation) is not implemented; see the lane handoff.
