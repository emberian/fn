# Validation plan

Executable ACL2 assertion books now exercise the components in `tests/acl2/`.
The [scenario catalog](scenarios/catalog.json) still specifies the broader
end-to-end tests with stable IDs; partial model traces do not make those entire
system scenarios pass. See [implementation status](../docs/implementation.md).

Use `make test` for the current combined batch. The
[assurance checkpoint](evidence/2026-09-18-assurance.md) captures 54 passing
certification roots, the simulator and 45 passing Python tests, including the
original stale-test failure and its corrected recheck; the
[first batch](evidence/2026-09-18-integrated.md) remains a historical snapshot.
Individual commands are:

```sh
make check
make certify
python3 tools/run_simulator.py
python3 -m unittest discover -s tests -p test_certify_runner.py -v
```

Certification covers the explicitly listed logical books and assertion events.
The simulator runs the same acceptance functions. The Python tests exercise
evidence-runner failure boundaries, socket behavior, and real-directory store
replay/fault handling. They do not prove the ACL2 definitions or qualify hardware
power-loss behavior.

## Evidence by layer

| Layer | Required validation |
| --- | --- |
| Abstract model | Executable examples; non-vacuous initial states; boundary cases; admitted definitions and certified invariants |
| Codec | Golden accepted/rejected vectors; independent decoder checks; round-trip/canonicality proofs; bounded-work cases |
| Storage | Small-state exploration of crashes at each write/barrier/publication point; uncertain failures; disk full; replay |
| Adapter | I/O ordering and stale-completion checks; fault injection; documented platform assumptions |
| NNTP | RFC clause checklist; independent transcripts and a real reader; all forms/ranges/errors; fragmented/coalesced input |
| Replication | Duplicate/reordered batches, missing dependencies, long contact gaps, carried media, replayed receipts |
| Retention/GC | Reservation exhaustion, multiple independent roots, release evidence, old-media reimport, interrupted compaction |
| Operations | Restart, checkpoint migration, corruption handling, backup restore/incarnation rules, concrete resource limits |

Use simulation seeds and bounded exploration parameters in reproducible evidence.
When a scenario is only partially executable, report the modeled boundary and
unmodeled effects. Process-kill tests alone do not establish power-loss behavior.
Tests of the logical core do not establish RFC compatibility of its future codec.

For a new durable path, enumerate its authoritative publication and externally
visible side-effect boundaries. Distinguish exception injection, actual child
process death, modeled loss of unflushed bytes, and physical power loss in the
evidence. After each supported recovery cut, check previously acknowledged
content and independent obligations as well as the interrupted operation.
Exercise rejection before mutation and lost completions after publication.
Passing an endpoint example is not coverage of every cut in its composition.

Behavior-changing batches use the [assurance scope rules](../docs/proofs.md#assurance-grows-with-the-implemented-surface)
and update the [closure inventory](../planning/assurance-closure.md). Avoid a
single coverage percentage combining proofs, tests and platform assumptions.

## Contact scheduling

`tests/acl2/scheduler-tests.lisp` carries the evidence for C2-06. Its
starvation counterexample is one trace run under two policies: under the
stated unfair policy (`fn-sched-unfair-step`, deterministic priority with the
promotion queue removed) the large article receives no submit, and under the
aging policy the same trace submits it on the third contact tick. The rest of
the book is the reachable witness for each keystone in
`books/scheduler-invariants.lisp` and one `must-fail` per hypothesis.

`tests/test_scheduler.py` tests only what the host owns: the bounded contact
plan reader, the durable decision log's trailer and sequencing, and the order
the driver calls the `:program` wrappers in -- select, durable decision,
durable attempt, commit -- with a fake host, so that no test here re-implements
a decision `books/scheduler.lisp` makes. `tests/bp-dtn7/fn_sender_lab.py`
runs the same driver against a two-window contact plan with an expiry, using
`MockBpa` when the pinned dtn7-rs build is unavailable; that mock transmits no
bundle and has no peer, and a report using it says so rather than claiming an
exchange.

## Crash campaign

`tests/campaign/` replaces hand-enumerated process-death cuts with a table
generated from the host itself. `cuts.py` reads `tools/run_store.py`,
`tools/workflow_journal.py`, `tools/receipt_journal.py` and
`tools/run_bp_receive.py`, collects every `faults.at("<name>")` injection site
with the write path that encloses it, and refuses to run when the declared
table and the injector disagree: a fault point added to a durable path is
automatically a new cut, and a removed one is a loud failure rather than a
silently dropped check. Each cut names the model crash point it corresponds
to -- the `fn-sf-crash` frontier and record choices of `books/store-files.lisp`
for the store, the `fn-journal-crash` slot choices of `books/journal.lisp` for
the two journals -- and a cut the model cannot express carries that gap in the
table instead of being skipped. `python3 tests/campaign/cuts.py` prints the
table, the pairs, the cuts no scenario reaches with the reason, and the model
gaps.

`campaign.py` runs each (scenario, cut) pair: it copies a prepared scenario
template, runs the real entry point (`run_store.command_post`,
`run_bp_receive.receive_bpa_request`, `WorkflowJournal.persist_enqueue`) in its
own process group, SIGKILLs that group at the named cut, and reopens the store
and journals through the real recovery path. It then checks that previously
acknowledged content and its pins are intact; that the interrupted operation
is absent or complete and never partial, against the crash choice the cut
declares; that a retry reaches exactly the state a run with no kill reaches;
that the receipt ADU regenerates byte-identically, including against bytes the
killed process had already produced; and that what the host had told the caller
or the transport before the kill is consistent with the recovered state -- a
receipt acknowledged without a durable record is a failure, and a pending
receipt intent must be reported as needing explicit recovery rather than
guessed. A failing pair is recorded as a minimal trace: scenario, cut,
durable-state digest before and after the kill, ACL2 replay result, the
pre-kill observation, and the checks that failed.

Run it with `python3 tests/campaign/campaign.py [--quick] [--json report.json]`
or as `python3 -m unittest tests.campaign.test_campaign`; `FN_CAMPAIGN=quick`
selects the marked subset for iteration. The subset is the iteration loop, not
the gate.

What the campaign does not show. It kills a process; the operating system page
cache survives, so nothing here is evidence about power loss, about a drive
cache that discards a `F_FULLFSYNC` acknowledgement, or about torn sectors and
partially written blocks. It does not corrupt bytes: `tests/test_store_corruption.py`
and `specs/store-fault-matrix.md` own that axis. It uses a single writer on one
host with a held lock, so it says nothing about concurrent writers or about a
filesystem losing cached metadata across a mount. The journals' cuts are
expressed by analogy with `fn-journal-crash`: no theorem binds an FNWF or FNRJ
record file to a journal slot, so those cuts are checked against the host
contract and the model's shape, not against a proved correspondence.

## Evidence record

Each meaningful validation summary records: requirement/scenario/proof IDs;
source revision or content digest; tool/runtime/platform versions; exact command;
result and artifact location; assumptions; omitted cases and remaining risks.
Update the registries after evidence exists, not when a test file is merely added.

## Current check

`make check` uses the standard library to check local Markdown links/anchors,
registry identities/references, milestone references, scenario coverage, and
evidence references for advanced statuses. It performs no network requests and
does not install dependencies, start a service, or run ACL2.
