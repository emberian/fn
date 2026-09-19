# HANDOFF — lane `w2/fault-campaign`

Worktree `/Users/ember/dev/fn/build/lanes/w2-fault-campaign`, branch
`w2/fault-campaign`, branched from `dev` at `4af825a`.

**HEAD: `3cb1bae`** "Generate the crash campaign from the host's own fault
points" (unsigned; produced while the user was away).

## What landed

`tests/campaign/` — a generated crash campaign over the integrated host:

- `cuts.py` reads `tools/run_store.py`, `tools/workflow_journal.py`,
  `tools/receipt_journal.py` and `tools/run_bp_receive.py` with `ast`,
  collects every `faults.at("<name>")` site together with the write path that
  encloses it, and `verify_table()` fails loudly when the declared table and
  the injector disagree in either direction. A fault point added to a durable
  path is automatically a new cut; a renamed or removed one fails the table
  test. Each cut records the model crash point it is, the record expectation
  for the operation it interrupts, the scenarios that reach it, and what the
  host had already acknowledged at that point.
- `child.py` runs one scenario to one cut. The only test-only code is the
  injector: `PauseAt.at` writes down what the host had already told the world,
  reports readiness on a pipe and blocks on a read the parent never answers,
  so the SIGKILL is ordered strictly after the named boundary.
- `campaign.py` copies a per-scenario template, runs the real entry point in
  its own process group, kills that group (killpg only, `ProcessLookupError`
  tolerated), reopens through the real recovery path and runs the checks. A
  failing pair is recorded as a minimal trace: scenario, cut, durable-state
  digest before and after the kill, ACL2 replay result, the pre-kill
  observation, and the checks that failed (`--json`).
- `test_campaign.py` — three table tests that need no ACL2, plus the campaign
  itself asserting zero failures. `FN_CAMPAIGN=quick` selects the marked
  subset; the subset is the iteration loop, not the gate.
- `tests/README.md` gains a "Crash campaign" section, and
  `specs/store-fault-matrix.md` §"Process-death cuts" now points at the
  campaign as the generated superset of its six hand-enumerated cuts.

Host change (`tools/`): the fault points those write paths were missing —
every barrier and side-effect boundary of `Store.advance_frontier`,
`Store.publish`, `Store.finish`, `Store.recover`, `WorkflowJournal.publish`,
`WorkflowJournal.stage_inbound`, `WorkflowJournal.retry_staged_delete` and
`ReceiptJournal.publish` — plus one injector per component threaded through
`receive_bpa_request` (`faults`, `store_faults`, `inbox_faults`,
`receipt_faults`), `open_live_bp_store` and `command_post`, all defaulting to
`NO_FAULTS`. No durable path carries a per-fault comparison; `FaultPoints.at`
still returns `None` in production.

## Numbers (generated, not typed)

`python3 tests/campaign/cuts.py` prints the table; at this HEAD it is **38
cuts**, **44 (scenario, cut) pairs**, **22 quick pairs**, 2 cuts no scenario
reaches, 2 model gaps. Scenarios: `cross-post`, `bp-receive`, `bp-retry`
(retry after a lost BPA delete reply), `capacity-refusal`, `sender-enqueue`
(the sender workflow journal's publish path, which none of the four named
scenarios reaches).

Runtime, sequential, this machine, after `make certify` completed:
**44 pairs, 0 failures, 171.6 s** (`build/campaign-full.log`,
`build/campaign-full.json`); quick subset 22 pairs in 76 s. No scenario needed
marking as slow: the full campaign is under three minutes, so `--quick` exists
for iteration rather than to keep the gate affordable. Slowest pair 7.2 s
(`bp-retry/workflow:inbound-reconciled`).

## Evidence run

- `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` → exit 0
  (`build/certify-baseline.log`, `build/acl2/certify-20260919T100428Z-84895/`).
- `python3 tests/campaign/campaign.py --json build/campaign-full.json` →
  `pairs=44 failures=0 seconds=171.6`.
- Affected existing tests (filtered, not the whole suite):
  `test_store_process_crash`, `test_workflow_process_crash`,
  `test_receipt_journal`, `test_receipt_journal_live`, `test_workflow_journal`,
  `test_bp_receive_faults`, `test_bp_receive_process_crash`,
  `test_host_boundary`, `test_store_fault_matrix` → `Ran 70 tests ... OK`
  (`build/affected-tests.log`).
- `make check` → green.

## Real defects found

**None in the host.** Every one of the 44 pairs recovered to a state the
checks accept on the first host revision the campaign ran against. The two
failures the campaign did produce were harness defects, fixed without
weakening a check:

1. The case builder deleted the copied `store/writer.lock`. Six pairs failed
   with `cannot open writer lock: [Errno 2]`. That is the host behaving
   correctly — an absent lock pathname is an invalid store, not a free one
   (the repaired `Store._open_lock`) — so the fix was to stop deleting the
   file, not to relax the host.
2. The record expectation was absolute where it had to be relative to the
   scenario's template. `bp-retry/receive:staged` failed with "record present
   at a cut that cannot have published" because that scenario's template
   already holds the article. The check now compares the record the
   *interrupted operation* would publish against the template state, and adds
   a clause that a "present" cut in a scenario that started without the record
   must have published exactly one.

## Cuts the model cannot express

Recorded in the table as `gap`/`uncovered`, reported by the campaign, not
skipped:

- `workflow:postlink` and `receipt:postlink` are the FNWF and FNRJ analogues
  of the store's `final-link` crash point, and the campaign observes both the
  absent and the present image. `books/journal.lisp:281-311`
  (`fn-journal-crash`, choices `:lost`/`:torn`/`:intact`) is a generic slot
  model; **no theorem binds an FNWF or FNRJ record file to a journal slot**,
  so these cuts are checked against the host contract and the model's shape,
  not against a proved correspondence. This is the journal-side counterpart of
  the store-side D4 that `fn-sf-frontier-new-visiblep` /
  `fn-sf-record-present-visiblep` closed on 2026-09-19.
- The BPA delete is a transport side effect outside both crash models
  (`receive:bpa-deleted`, and the two uncovered delete boundaries below).
  Nothing in `fn-sf-crash` or `fn-journal-crash` expresses "the bundle is gone
  from the peer's inventory"; the campaign checks it against the host's own
  reconciliation (`_in_inventory`, `delete_completed`) only.
- `workflow:inbound-deleted` and `workflow:inbound-retry-deleted` have no
  scenario: the receiver always defers BPA deletion (`_defer_delete` raises),
  and `retry_staged_delete` has no caller on the receiver path. Both are the
  same side effect the campaign does cut as `receive:bpa-deleted`. A sender
  lane that gives `retry_staged_delete` a caller should add a scenario rather
  than leave the reason in place.

## Open, for the next lane

- The campaign asserts `record present/absent` and count agreement; it does
  not yet compare the recovered record's **bytes** to the bytes the killed
  process staged. The staged file is available in the case directory
  (`--keep`), so the check is cheap to add and would catch a torn-but-accepted
  record that the current checks would see as merely "absent".
- Three scenarios post one group; only `cross-post` crosses two. Pin counting
  is compared against a reference run rather than against an independent
  expectation, so a bug that changed both the reference and the recovered run
  identically would pass.
- `tests/store_crash_child.py` and the six hand cuts in
  `tests/test_store_process_crash.py` are now a subset of the generated
  campaign (they monkeypatch `os.replace`/`os.link` where the campaign uses
  the injector). They were left in place and still pass; retiring them is a
  separate decision, since they are what `specs/store-fault-matrix.md` §"cuts"
  currently tabulates.
