# w6-workflow-restart handoff

Branch `w6/workflow-restart`, worktree `build/lanes/w6-workflow-restart`, from
`dev` `ccac524`.

Closes the v0.3 blocker the media lab left open in
[`HANDOFF-w3-media-lab.md`](HANDOFF-w3-media-lab.md).

## The cause: the host's accessor, not the model's replay

Two separate defects were behind one refusal, and neither is in
`fn-bp-replay-journal`.

**1. `fn-workflow-work-status` reported the attempt status.** It answered
`:absent` when the work had no attempt, which is also its answer for a work id
the image does not hold. Every work a history enqueued and had not yet
attempted therefore read `absent` after a reopen, and the lab read that as
"replay dropped the works". Replay does not drop them: a first attempt after a
reopen is admitted today and was admitted before this lane, which
`tests/test_workflow_restart.py::test_first_attempt_is_admitted_after_a_reopen`
demonstrates by making the attempt.

**2. The lab's refusal at `run_four_node_lab.py:541` was a lifetime
mismatch.** It submitted with `bp-lifetime=30` while the node's configuration
carries `300`, and `fn-bp-record-contextp` requires the attempt record's
lifetime to equal the configuration's. `fn-workflow-preflight-history` runs
before `fn-workflow-preflight-record` in `WorkflowJournal.publish`, so the
history message is the one that surfaces; the live preflight refuses it too.
That equality is the model's and was not relaxed. The lab now submits with the
configured lifetime and holds the window shut for longer than it.

## The fix

- `books/bp-workflow-records.lisp`: `fn-bp-work-status` (work-id, works) with
  three distinct answers -- `:absent`, `:receipted`, the attempt status,
  `:outstanding` -- so ACL2 owns the projection.
- `host/workflow-host.lisp`: `fn-workflow-work-status` reports it and computes
  nothing. The bridge and `tools/workflow_journal.py` are unchanged.
- `books/bp-workflow-records-invariants.lisp`: the keystone
  **`fn-bp-replay-preserves-works`** -- if a work id is found in `s`, it is
  found in the state `fn-bp-replay-records` returns, over arbitrary record
  lists and with *no* well-formedness hypothesis -- plus
  `fn-bp-step-preserves-works` (its step-level subject) and
  `fn-bp-durable-enqueue-holds-the-work` (the entry half: the `:ordinary
  :durable` outcome of a pending enqueue puts that work in the state). 26
  supporting lemmas are `local`.
  The `fn-bp-statep` hypothesis these began with **proved unnecessary and was
  deleted**: every transition that could drop a work id already demands a
  well-formed state through `fn-bp-pending-matchesp`, and the rest replace,
  cons or map over the list.
- `tests/acl2/bp-workflow-records-tests.lisp`: a non-degenerate witness (a
  replay that changes the state still finds the work), one tooth per
  hypothesis, and the four answers of `fn-bp-work-status` on states replay
  reaches. The kind hypothesis of `fn-bp-durable-enqueue-holds-the-work` has
  no reachable violating value and the test book says so next to it.
- `specs/bp-workflow-host.md`: the reopen read model and the lifetime equality.
- `tests/bp-dtn7/run_four_node_lab.py`, `tests/test_four_node_lab.py`:
  `relay_a_onward_obligation_recoverable_after_kill` **restored, not softened**
  -- it reads `outstanding` for the recovered obligation now that `absent`
  means only "no such work". `SHORT_LIFETIME` is gone.

## Evidence

- `tests/test_workflow_restart.py`: 4 cases, green against real ACL2. Case 1
  fails on `dev` with `'absent' != 'outstanding'`; case 4 reproduces the lab's
  exact refusal text for the short lifetime.
- `tests.test_workflow_journal tests.test_workflow_live tests.test_workflow_faults`:
  31 tests, green, unchanged.
- `tools/ledger.py --write` and `make check`: scaffold and ledger OK.

## Open

- The farm certification of the two edited books and their closure is
  `run-20260920T044427Z-61e8` on persvati
  (`--remote-root /home/ember/fn-lanes/w6-workflow-restart`,
  `--affected-by books/bp-workflow-records.lisp
   --affected-by books/bp-workflow-records-invariants.lisp --closure`).
  Both books were `ld`-clean end to end on the laptop first, test book
  included, with no error and `:PASSED`.
- The four-node lab now runs eight assertions past the old stop and fails at
  `the_pair_reaches_the_destination_in_the_reverse_of_its_submission_order`
  (`run_four_node_lab.py:557`), one of the eleven assertions that had never
  been reached. That is a lab defect newly exposed, not a workflow one; the
  evidence pair is still the incomplete run from w3/media-lab.
