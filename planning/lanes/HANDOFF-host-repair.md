# Lane `host-repair` handoff

Branch `lane/host-repair`, branched from `0bd0b5c`. Worktree
`/Users/ember/dev/fn/build/lanes/host-repair`. No book, `planning/` or
`tests/evidence/` file was touched: this lane changed only host code, host
specification prose and tests, so `make certify` here is a baseline for an
unchanged proof tree, not evidence about this work.

- `git rev-parse HEAD`: `PLACEHOLDER_HEAD`
- Commits: `PLACEHOLDER_COMMITS`

## Files changed

Host code (`tools/`): `run_store.py`, `run_reader.py`, `run_bp_ingress.py`,
`run_bp_receive.py`, `workflow_journal.py`, `receipt_journal.py`, `bpa_dtn7.py`.

Prose: `specs/host.md`, `specs/store-experiment.md`, `docs/local-experiment.md`.

Tests changed: `tests/test_bp_receive_faults.py`,
`tests/test_bp_receive_process_crash.py`, `tests/test_bpa_dtn7.py`,
`tests/test_reader.py`, `tests/test_receipt_journal.py`,
`tests/test_receipt_journal_live.py`, `tests/test_store.py`,
`tests/test_store_corruption.py`, `tests/test_store_fault_matrix.py`,
`tests/test_workflow_journal.py`, `tests/test_workflow_process_crash.py`.

Tests added: `tests/test_acl2_bridge.py`, `tests/test_host_boundary.py`.

Nothing in the not-owned list was modified: `metadata`,
`validate_post_boundary`, `frame`, `unframe`, `group_codes`, the
`DEFAULT_CONFIG["groups"]` table and `conservative_charge` in `run_store.py`;
`encode_record`, `encode_inbound` and their decoders in `workflow_journal.py`;
`encode_receiver_record` and its decoder in `receipt_journal.py`.

## What changed, and the test that proves it

### D1 — no `max_transactions` check on the BP receive path

`run_bp_receive.py` now refuses before any frontier advance or charge, on the
path that would otherwise allocate and publish. The refusal is a returned
`ReceiveResult("refused-capacity", b"", staged)`, not an exception: the BPA
request and its staged FNBI frame stay present for an operator.

Proof: `tests/test_bp_receive_faults.py`
`test_store_at_its_transaction_bound_refuses_and_stays_openable`. It reduces
the configured bound to one, accepts one request, then presents a distinct
request. It asserts the refusal outcome, that the BID and staged frame remain,
that the allocation frontier file is byte-identical to before, that the
transactions directory still holds exactly one file, and — the point of D1 —
that the store still reopens with one record, one article and one pin. Without
the guard the second record publishes and that reopen raises `StoreFault`.

The bound is exercised at a reduced configured value rather than by writing 128
real transactions; what a store's reopenability depends on is the guard, not
the particular number, and the number is the same `store.config`
`max_transactions` the other two admission paths read.

### D2 — no request/response correlation on the ACL2 pipe

Correlation. `Acl2Store.call` now writes `(cw "FN_CALL_<nonce>~%")` with a
fresh 16-byte `os.urandom` nonce and reads that marker to its own prompt
*before* writing the real form. The marker read requires exactly one prompt in
the output and the marker before it. The real form is written only after that,
so a reply that belongs to an earlier call cannot be returned as this call's
result. Two separate write/read pairs are used rather than one batched write,
because writing both forms at once admits a race where both replies arrive in a
single read and a strict single-prompt check would falsely trip.

Poisoning. A correlation failure, a reply timeout, an output-bound trip, an
`ACL2 exited before producing a prompt`, or a broken pipe sets
`Acl2Store.poisoned`. Every later `call` raises `StoreError("ACL2 bridge
poisoned")` without writing anything, and the only recovery is constructing a
new bridge, which is a new ACL2 process. A *correlated* reply that reports an
ACL2 error is an answer, not a loss, and does not poison: the pipe is still
synchronized and existing refusal tests keep working.

Reader. `run_reader.Acl2Reader` exposes `poisoned` (its own for an owned
process, the store bridge's when it shares one). `serve_client` raises
`ReaderBridgeFault` instead of returning when the bridge is poisoned, and
`main` prints and returns `EXIT_FAULT`. A merely invalid bridge result with a
live bridge still only ends that connection, as before.

Timeouts. The fixed 20 s is replaced by `ACL2_CALL_BASE_SECONDS` (20 s) plus
`ACL2_CALL_PER_KIB_SECONDS` (0.004 s/KiB, about 4 s/MiB) times the form size,
and `Acl2Store.recover` uses `max(ACL2_RECOVER_BASE_SECONDS (30 s) +
ACL2_RECOVER_PER_RECORD_SECONDS (1 s) × records, size bound)`. Constants and
their derivation are documented in `specs/host.md` and in a comment at the
constants. Derivation: the recorded maximum-profile reopen is 11.7 s for a
128-record form of roughly 34 MiB, about 0.35 s/MiB, so 4 s/MiB is an order of
magnitude above measurement and the 128-record recovery bound is about 158 s.

Proof: `tests/test_acl2_bridge.py` drives the real bridge code against a
scripted pipe with a real file descriptor.
`test_reply_without_this_calls_marker_poisons_the_bridge` is the D2 scenario
itself: the pipe is one result behind, the marker read sees the previous
result, the call refuses, the real form is never written, and every later call
refuses. `test_stale_reply_arriving_with_the_marker_is_a_correlation_failure`
covers the stale-plus-marker arrival in one read.
`test_timeout_poisons_the_bridge_for_good` and
`test_output_bound_trip_poisons_the_bridge` cover the two trips the packet
names. `test_acl2_error_reply_is_answered_without_poisoning` is the
counter-case. `test_marked_reply_is_accepted_and_returns_only_the_result` and
`test_fresh_nonce_per_call` check the normal path and nonce freshness.
`test_call_timeout_grows_with_form_size_and_bounds_the_recorded_reopen` checks
monotonicity and that the recovery bound exceeds ten times the recorded 11.7 s.
`ReaderFailClosedTests` covers both halves of the reader: `serve_client`
raising on a poisoned bridge but not on a live one, and the real listener loop
returning `EXIT_FAULT` versus `EXIT_OK` end to end.

### D11 — receipt-id length checked after the charge

`_receipt_identity` became `_work_identity`, which derives the work id and
receipt id and reports the receipt id's octet length without judging it. The
judgement is a preflight in `receive_bpa_request`, placed after the hard status
refusals and before every branch that writes: before the pending recovery
branch, before `accept_request`, before `advance_frontier` and before any
charge. An over-long receipt id returns
`ReceiveResult("refused-receipt-id", b"", staged)` with the BID retained.

Proof: `tests/test_bp_receive_faults.py`
`test_unreceiptable_work_id_refuses_before_any_store_mutation` (249-octet work
id: refusal, BID retained, nothing deleted, store still at zero records,
articles and pins, only the receiver config record on disk, and a retry reaches
the same refusal rather than a stuck `:context`) and
`test_a_receiptable_work_id_at_the_bound_is_still_accepted` (248 octets, the
exact boundary, still accepted).

### D12 — `fsync` only, on a platform where that is not the barrier

`run_store.durable_barrier(fd)` is the single helper. On darwin it issues
`fcntl(fd, F_FULLFSYNC)`; on `ENOTTY`, `ENOTSUP`, `EOPNOTSUPP`, `EINVAL` or
`EPERM` it falls back to `os.fsync` and the specification says that path then
carries only the `fsync(2)` contract; any other errno is raised, not
downgraded. Elsewhere it is `os.fsync`. `fsync_file`, `fsync_dir` and
`fsync_regular` in `run_store.py` call it, and `workflow_journal.py` imports it
(and re-exports it to `receipt_journal.py`) instead of calling `os.fsync`; no
`os.fsync` call site remains in any of the three modules outside the helper.

`specs/host.md` has a platform table saying exactly which platform gets which
guarantee, and `specs/store-experiment.md` points at it from the publication
boundary. Both say this is the strongest primitive each platform offers and
explicitly not a power-loss qualification; A-DURABILITY and A-WRITE-ISOLATION
remain assumptions about the device and filesystem.

Measured cost on this machine's APFS volume, 200 iterations each:
`fsync(2)` 0.039 ms per call, `F_FULLFSYNC` 5.532 ms per call. That is the
cost of asking for the flush instead of assuming it, and it is recorded in
`specs/host.md` and `docs/local-experiment.md`.

Proof: `tests/test_host_boundary.py::DurabilityBarrierTests` —
`test_darwin_barrier_asks_the_device_to_flush_its_cache` (the `fcntl` call is
made with `F_FULLFSYNC` and `os.fsync` is not called),
`test_a_filesystem_that_rejects_full_fsync_falls_back_to_fsync`,
`test_an_unrelated_barrier_error_is_not_swallowed`, and
`test_every_journal_barrier_goes_through_the_one_helper` (identity of the
helper object across the three modules, and that all three `run_store` barrier
wrappers route through it).

### D13 — exit codes conflated uncertain, refused and durable acceptance

| Code | Meaning | Source |
| --- | --- | --- |
| 0 | accepted, or the query answered | normal return |
| 1 | refused: known and clean, no durable state changed | `StoreError` |
| 3 | uncertain: recovery required before further mutation | `StoreIndeterminate` |
| 4 | fault: invalid durable state or I/O fault | `StoreFault`, `OSError` |
| 5 | usage: the invocation itself is wrong | `UsageParser`, `UnicodeError` |

`run_store.exit_code_for` is the single mapping; `UsageParser` makes argparse
report 5 instead of its default 2. Applied in `run_store.main` and
`run_bp_ingress.main`. `BpDeletePending` now carries the outcome, BID and
staged path it earned and is reported on stdout as
`accepted bid=… staged=… bpa-delete=pending` with exit 0, since it is a durable
acceptance awaiting a transport obligation, not a failure.

`run_store.py` post-link classification: a core rejection after `os.link`
already reached the filesystem is `StoreIndeterminate`, not `StoreFault`. Three
sites of the same class were changed together, all "the syscall happened and
the core will not record it": the record link, the record directory barrier and
the allocator replacement and its directory barrier. The packet named the first
one; the other three are the same defect and are listed here as an extension of
D13, not as a silent addition.

`Store.recover` also reclassifies: a plain `StoreError` raised while
reconstructing committed history (a malformed bridge result, an ACL2 error on a
corrupt record) becomes `StoreFault("cannot reconstruct committed history: …")`.
Committed history the core cannot decode is an invalid store state, not a
refusal of a request; without this a corrupt store exited 1.

`tests/test_store_fault_matrix.py::test_store_lock_close_after_success_matrix`
no longer enshrines "committed sequence=1 AND OSError" as one fact. It asserts
the acceptance line was printed, that the raised teardown failure is *not* a
`StoreError` (so it is not a refusal and not an uncertain acceptance), that
`exit_code_for` classifies it as `EXIT_FAULT`, and that the committed
transaction survives the reopen unchanged. Its docstring says which outcome
belongs to which event.

Proof: `tests/test_host_boundary.py::ExitCodeTests` — `test_documented_table`
(the mapping, and that the five codes are distinct),
`test_store_cli_maps_each_outcome_to_its_own_code` (four outcomes through the
real `main`), `test_store_cli_usage_error_is_its_own_code`,
`test_pending_bpa_delete_is_reported_as_acceptance_not_failure`,
`test_ingress_refusal_and_fault_stay_distinct`. End to end, the subprocess CLI
expectations in `tests/test_store.py` and `tests/test_store_corruption.py` now
assert the specific code: duplicate-Message-ID conflict, contended writer lock
and injected known abort are 1; injected post-publication uncertainty is 3;
truncation, sequence gap, integrity mismatch, unknown schema, final-namespace
symlink, a frontier behind history and every `assert_unusable` case are 4.

### D14 — a lost BPA delete reply was unresolvable

`workflow_journal.retry_staged_delete` splits on the inventory: a BID still
present is retried through the supplied delete callback, and a BID absent from
the inventory is reconciled as a completed delete — the durable frame is
re-barriered, its stored BID rechecked, and the method returns normally, which
is what clears the pending state, because `InboundDeletePending` is what
created it. `stage_inbound` does the same reconciliation when a BID is absent
from the inventory but a durable frame for it exists, so a retry does not
download again and does not raise `BID is not present in inventory`. Absence
with no durable frame is still refused. `bpa_dtn7.BpaDtn7Client.delete_completed`
is the transport observation that feeds this, and `delete`'s docstring now says
a lost reply is resolved that way and never by assuming an outcome.

Proof: `tests/test_workflow_journal.py` —
`test_pending_delete_with_the_bid_gone_reconciles_as_completed` (both the
`retry_staged_delete` and the `stage_inbound` entry, asserting no delete call
and no second download), `test_pending_delete_with_the_bid_present_is_retried`,
`test_absent_bid_without_a_durable_frame_is_still_refused`. Client side:
`tests/test_bpa_dtn7.py::test_delete_completion_is_observed_from_inventory_absence`.

### Smaller items

- **Initialization publishes through staging.** `Store._publish_initial_file`
  writes `config.json` and `allocation-frontier.json` to an exclusively created
  staging name, completes the data barrier, links into the final name without
  overwriting, barriers the directory and removes the staged name. An existing
  final name is loaded and checked, as before. The packet said "rename"; this
  uses `os.link` plus an unlink of the staged name instead, because `rename`
  would silently replace an existing `config.json`, and the previous code's
  `O_EXCL` on the final name specifically refused to. `link` keeps that refusal
  atomic (`EEXIST`) while gaining the staged data barrier, and it is the same
  primitive the transaction publication path already uses. Proof:
  `tests/test_host_boundary.py::test_initialization_publishes_metadata_through_staging`
  and the rewritten
  `tests/test_store.py::test_failed_config_file_barrier_is_reestablished_during_recovery`,
  which now asserts that a failed data barrier leaves *no* `config.json` and a
  staged orphan, where before it asserted a torn final name existed.
- **Receiver crash helper.** `tests/test_bp_receive_process_crash.py::_kill_group`
  always `killpg`s, tolerates `ProcessLookupError`, and falls back to
  `child.kill()` only on `PermissionError`, matching
  `test_store_process_crash.py`. Covered by the five existing process-death cuts.
- **Journal lock files.** `workflow_journal.open_exclusive_lock` (used by both
  journals) opens with `O_NOFOLLOW`, `fstat`s for `S_ISREG`, and separates
  opening the pathname from contending for the lock, so only a refused `flock`
  is "already owned". Proof:
  `tests/test_workflow_journal.py::test_a_symlinked_or_irregular_lock_pathname_is_refused`
  (symlink and FIFO) and the existing contention tests in both journals.
- **`ENOENT` on the store lock path.** `Store._open_lock` raises `StoreFault`
  for a lock pathname it cannot open (with `ELOOP` still its own message) and
  `StoreError("store is already locked")` only for a refused `flock`. Proof:
  `tests/test_host_boundary.py::test_absent_lock_pathname_is_a_fault_not_a_held_lock`
  and `test_a_contended_lock_is_still_a_clean_refusal`.
- **Linear octet parse.** `run_store.decimal_list` replaces the exponential
  `\((?:\s*[0-9]+)*\s*\)` at both `run_store.py` and `run_reader.py`. Proof:
  `tests/test_acl2_bridge.py::test_octet_list_parse_is_linear_on_malformed_output`
  (time-bounded on a digit run with a trailing non-digit, which is the
  backtracking case) and `test_octet_list_accepts_only_bounded_decimal_octets`.
- **Fault injection behind an injector object.** `run_store.FaultPoints` is the
  production object; its `at(point)` does nothing, so no durable path holds an
  injection branch and no production module holds `os._exit`.
  `run_store.ScriptedFaults` is the test-only injector, the single place in the
  host where a deliberate failure or process death is produced. `Store`,
  `WorkflowJournal` and `ReceiptJournal` take `faults=NO_FAULTS`; the `fault=`
  parameters are gone from `Store.publish`, `WorkflowJournal.publish`,
  `publish_intent`, `publish_outcome`, `ReceiptJournal.publish` and
  `persist_receipt_intent`. The `--inject-fault` CLI flag remains as a
  documented test-only hook that constructs a `ScriptedFaults`; `CLI_FAULTS`
  names its two points. Every existing fault test passes:
  `tests/test_workflow_process_crash.py` (both `os._exit` cuts, now produced by
  the injector's `exit_code`), `tests/test_workflow_journal.py`
  `test_reopen_replays_visible_uncertain_attempt`,
  `tests/test_receipt_journal.py`
  `test_postlink_uncertainty_fences_and_replays_visible_record`,
  `tests/test_receipt_journal_live.py`, and the CLI injections in
  `tests/test_store.py` and `tests/test_store_corruption.py`.
- **Non-ASCII BID.** `run_bp_receive.receive_bpa_request` catches
  `UnicodeEncodeError` and raises `BpReceiveError("BPA BID boundary")`. Proof:
  `tests/test_host_boundary.py::test_non_ascii_bid_is_refused_rather_than_raising_an_encoding_error`
  and `test_over_long_and_empty_bids_refuse_the_same_way`.
- **Double close.** Both journals retire the staging descriptor number before
  closing it (`handle, fd = fd, -1; os.close(handle)`), so a failing close
  cannot be followed by a second close of a number the runtime has reused.
  Proof: `test_a_failing_close_cannot_close_a_reused_descriptor` in both
  `tests/test_workflow_journal.py` and `tests/test_receipt_journal.py`, each
  opening a replacement descriptor inside the injected close failure and
  asserting it is still open afterwards.
- **TOCTOU on journal record reads.** `workflow_journal.read_regular_barriered`
  takes the type check, the size, the bytes and the barrier from one
  `O_NOFOLLOW` descriptor, replacing `is_symlink`/`is_file`/`stat`/`read_bytes`
  plus a second `os.open` for the barrier. Used for FNWF records, FNBI inbound
  frames and FNRJ records. Proof:
  `test_a_record_replaced_by_a_symlink_is_refused_on_reopen` in both journal
  test files, and the existing `test_malformed_namespace_refuses_image`.
- **BPA total-transfer deadline.** `BpaDtn7Client` takes
  `total_deadline_seconds` (default 30 s, capped at 300 s, validated), computed
  once per `_get` and checked in the bounded read loop, so a peer that answers
  inside every per-read window cannot hold a call open without limit. Proof:
  `tests/test_bpa_dtn7.py::test_a_transfer_inside_every_read_window_still_hits_the_total_deadline`
  (socket timeout 2 s, deadline 0.2 s, peer takes 0.5 s: the deadline message
  is raised and the call ends well before the per-read timeout) and the
  constructor bounds in `test_loopback_and_input_boundaries_are_enforced`.
- **Staging orphans.** `Store.staging_orphans` enumerates the staging namespace
  under the held lock, bounded to `MAX_STAGING_REPORT` names plus an ellipsis;
  `Store.recover` records them and `recover`/`status` print
  `staging-orphans=N [names]`. Nothing is deleted. Proof:
  `tests/test_host_boundary.py::test_recovery_reports_staging_orphans_without_deleting_them`
  and `test_orphan_report_stays_bounded`.

### Ownership note on `specs/store-experiment.md`

The packet allowed this lane the fsync/barrier prose in that file. Three hunks
landed there, and only the first is squarely inside that allowance. The other
two describe behavior this lane changed, and leaving them would have left the
specification describing an adapter that no longer exists — which is worse than
a merge conflict — so they were written rather than skipped. If another lane
touched the same paragraphs, drop these and re-apply:

1. **Publication boundary, barrier paragraph** (in scope): names `F_FULLFSYNC`
   on darwin, the `fsync(2)` fallback and its weaker contract, and points at
   the platform table in `specs/host.md`.
2. **Publication boundary, configuration paragraph** (beyond the allowance):
   replaces "Configuration creation also needs data and namespace barriers"
   with the staged/link/barrier sequence and the reason, and splits opening the
   lock pathname from contending for the lock.
3. **Recovery, operational-limits paragraph** (beyond the allowance): adds that
   every admission path enforces the transaction bound before allocating or
   charging, including the BP receiver, and that recovery enumerates and
   reports staging orphans without deleting them.

### One change the packet did not ask for

`run_store.py` ends by registering itself in `sys.modules` under both
`run_store` and `tools.run_store`. The two import spellings in this tree
(`run_bp_ingress.py` and `run_reader.py` use the bare name with `tools/` on
`sys.path`; `run_bp_receive.py` and the tests use the package) were producing
**two module objects**, with two `DEFAULT_CONFIG` dictionaries, two copies of
every constant and two independent `mock.patch` targets. D12's "one helper,
used everywhere" is not true under that split — the first version of
`test_every_journal_barrier_goes_through_the_one_helper` failed on exactly this
— and a test that patches `run_store.DEFAULT_CONFIG` silently misses the copy
the adapter reads. The registration makes it one object. It is recorded here
because it is a real change to import behavior, not a tidy-up.

## Commands run, with results

| Command | Result |
| --- | --- |
| `make check` | `Scaffold OK: 77 Markdown files, 49 requirements, 18 proof targets, 18 scenario specifications.` (76 before this file existed; `HANDOFF.md` is the 77th and is lane bookkeeping, not a specification.) |
| `make certify` (run 1, default `FN_ACL2_TIMEOUT_SECONDS=600`) | failed: `books/article-properties` `timed out after 600 seconds`; the other 112 of 113 roots returned exit 0. Evidence `build/acl2/certify-20260919T033046Z-67560`. Laptop contention with nine concurrent lane SBCL processes, not a proof failure: this lane changed no book. |
| `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` (runs 2 and 3) | both killed by an external `SIGTERM` part-way through — `make: *** [certify] Terminated: 15` at 20 and 85 of 113 roots. Not a proof failure and not memory pressure (about 26 GB free at the time); the runs were started from the agent's own shell and its background-task wrapper, and something outside `make` signalled them. Evidence `build/acl2/certify-20260919T053512Z-96358` and `certify-20260919T055003Z-8171`. Between runs 1 and 3, all 113 roots — `article-properties` included — produced certificates, which is why the Python suite runs. |
| `FN_ACL2_TIMEOUT_SECONDS=1800 make certify`, `nohup setsid`-detached (run 4) | `PLACEHOLDER_CERTIFY` |
| `python3 -m unittest discover -s tests -p 'test_*.py'` | `PLACEHOLDER_SUITE` |
| `fsync` vs `F_FULLFSYNC` microbenchmark, 200 iterations each, APFS temp dir | 0.039 ms vs 5.532 ms per call |

`make certify` on this lane certifies an unchanged book tree. It says the tree
still certifies; it says nothing about the host repairs, which are Python and
are covered by the suite above.

## Known defects

- The transaction-bound test (D1) reduces the configured bound rather than
  writing 128 real transactions. It exercises the guard and the reopen, not the
  literal 129th record at the shipped profile. `tests/store_capacity_probe.py`
  remains the manual maximum-profile probe and was not run in this lane.
- `durable_barrier` falls back to `fsync(2)` silently when a filesystem rejects
  `F_FULLFSYNC`. The fallback is documented in `specs/host.md`, but nothing at
  runtime records that a given store's barriers were the weaker kind. A store
  whose volume rejects `F_FULLFSYNC` looks identical to one whose volume
  accepted it.
- `F_FULLFSYNC` costs about 140 times an `fsync(2)` on this machine. The full
  Python suite absorbed it without a visible change in wall time, but any future
  throughput measurement must be re-taken; the old numbers were taken against
  the weaker barrier.
- The bridge correlation costs one extra round trip per call. No measurable
  suite slowdown, but it is a real doubling of ACL2 top-level evaluations.
- `ScriptedFaults`, including its `os._exit`, lives in `tools/run_store.py`
  rather than under `tests/`, because `run_store.main` must construct one for
  the `--inject-fault` hook and cannot import from `tests/`. Production code
  never constructs it and no durable path branches on it, but the class is
  physically in a `tools/` module.
- The staging-orphan report is a name list on stdout. It is not a structured
  record, is not persisted, and recovery does nothing with it beyond printing.

## Remaining gaps

- D3, D4, D5, D6, D7, D8, D9 and D10 are untouched: they are model and proof
  work, not host work, and were not in this packet.
- The Python twins in the review's §4 table are untouched by design; they are
  C1-13's packet. This lane did not move `metadata`, the group table, the charge
  policy, the Message-ID bound or the framing into ACL2.
- `run_bp_receive.BpReceiveDeletePending` now carries its outcome, receipt and
  staged path, but `receive_bpa_request` still signals a durable acceptance
  awaiting a delete by raising. There is no CLI for the receiver, so no exit
  code is involved; a caller must catch the exception to see the acceptance.
- `bpa_dtn7.delete_completed` exists and is tested, but no adapter calls it yet:
  the reconciliation it feeds is driven from `workflow_journal` by whatever
  inventory callable the caller supplies. Wiring the pinned client into the
  receiver's retry path is not done.
- No test covers a poisoned bridge arising from a *real* ACL2 process (the
  scripted pipe is the test vehicle). Killing a live ACL2 mid-call and asserting
  the next call refuses would be a stronger, slower test.
- `tools/run_simulator.py` and `tools/certify_books.py` were not touched; both
  have their own subprocess timeout handling that does not share the bridge's
  correlation discipline.

## Proposals outside this lane's ownership

1. **`tools/run_bp_ingress.py:43-55`, `load_workflow_journal`.** It loads
   `workflow_journal.py` by path under a synthetic module name, producing a
   second `WorkflowJournal` class whose module-level constants are a separate
   set from `tools.workflow_journal`'s. Tests that patch
   `tools.workflow_journal.MAX_INBOUND_COUNT` or `fsync_dir` do not affect the
   adapter's copy. Replacement: before building the spec, return an
   already-imported module whose `__file__` resolves to the same path, and
   otherwise load as now. The file is owned by this lane, but the change is a
   behavioral one about module identity that belongs with whoever owns the
   ingress contract, so it is proposed rather than taken.

2. **`host/store-node-host.lisp:61-63` (not owned).** The review's §4 row notes
   production passes `next-txid` for both txid and generation, making
   stale-generation rejection unreachable from the live path. The host exit-code
   work above makes the *host* outcomes distinct but cannot make that core
   branch reachable. Replacement belongs with the C1-14 crash-model packet.

3. **`books/store-files.lisp:455-480` (not owned), D4.** The two crash points
   `tests/store_crash_child.py` actually hits — after `os.replace`/`os.link`
   return but before ACL2 observes `:ok` — are exactly the positions this lane
   now classifies as `StoreIndeterminate`. The host side is consistent; the
   model still cannot express those transitions. Adding them would let the
   indeterminate classification be checked against a modeled state rather than
   against host bookkeeping alone.

4. **`tests/evidence/*.json` (not owned).** The evidence files pin host tool
   sources by SHA-256. Six of the pinned names changed in this lane:
   `tools/run_store.py`, `tools/run_reader.py`, `tools/run_bp_ingress.py`,
   `tools/run_bp_receive.py`, `tools/workflow_journal.py` and
   `tools/receipt_journal.py`. (`tools/bpa_dtn7.py` also changed but is not
   pinned in any evidence file, which is itself worth closing.) The integrator
   must regenerate those digests, or the next digest check will report drift
   that is this commit, not corruption. Affected files include
   `2026-09-18-assurance.json`, `2026-09-18-bp-composition-assurance.json`,
   `2026-09-18-bp-exchange.json`, `2026-09-18-composed-store.json`,
   `2026-09-18-wildmat-storage.json`, `2026-09-18-fields-transfer.json`,
   `2026-09-18-articles.json` and `2026-09-18-integrated.json`.

5. **`specs/bp-receive.md:65-96` (owned by this lane only for the fsync prose in
   `store-experiment.md`; `bp-receive.md` is not in the owned list).** Two
   sentences are now incomplete: the limits paragraph lists the covered
   `tests/test_bp_receive.py` cases without the new capacity and receipt-id
   refusals, and the evidence paragraph carries a hand-typed "combined 133-test
   result", which the assurance rule on generated counts forbids. Replacement
   for the limits paragraph's last sentence: "A distinct request with an
   already-used work ID is rejected before Store mutation and its BPA BID
   remains present; so are a request that would exceed the configured
   transaction bound and a work ID whose receipt ID exceeds its octet bound,
   each refused before any frontier advance or charge." Replacement for the
   evidence sentence: drop the count and name the property instead — "The
   composition assurance record contains the five process-death cuts and the
   Python suite result for that batch."

6. **`planning/proofs.json` and `planning/requirements.json` (not owned).**
   HST-003's three-outcome requirement now has a concrete host artifact (the
   exit-code table in `specs/host.md` and `run_store.exit_code_for`). If the
   registry tracks host evidence, this is the row to point at. No status was
   changed by this lane.
