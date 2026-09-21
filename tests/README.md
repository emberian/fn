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

## Tooling unit tests

The tools that decide what gets certified are themselves tested, with no ACL2
and no network: `python3 -m unittest tests.test_certify_runner tests.test_ledger
tests.test_certs tests.test_farm tests.test_proof_profile
tests.test_evidence_manifests`. `tests/test_certify_runner.py` drives the
real runner against a fake ACL2 in a throwaway repository (`FakeRepository`):
the parallel schedule, `--affected-by` selection and `--dry-run` listing
(`AffectedByTests`), the machine-wide process cap with one slot serialising
four jobs (`SlotTests`), and the certificate cache hook, including that a
failing run publishes nothing (`CachePublishTests`). `tests/test_certs.py`
holds the cache to its narrow promise: publish keys on book content, refuses a
certificate older than its book, install matches across worktrees, never
overwrites a newer matching local pair, and keeps two same-byte books apart.
`tests/test_farm.py` reads the exact commands `tools/farm.py` would issue --
the mirror that excludes `build/`, the detached runner, a bounded wait that
sleeps rather than spins, the fetch of evidence and pairs -- without running
ssh. `tests/test_ledger.py` covers the reader, the suspect detector, the export
lints, the `fn-defrecord` expansion the reader must perform to see a migrated
book, and the hand-written-record lint.
`tests/test_evidence_manifests.py` holds the evidence archive to the one
promise that matters: a citation resolves to what is COMMITTED, so an
archived-but-unstaged manifest does not answer it, a manifest never cites
itself, and the same run filed twice keeps the first copy while two
different runs under one id are reported rather than merged.
`tests/test_proof_profile.py` pins `tools/proof_profile.py`'s parser against
two real ACL2 8.7 logs in `tests/vectors/` -- one form that closed and one
that did not -- plus the driver it builds and its choice of the less loaded
farm box. None of this is evidence about ACL2; it is evidence that the
harness reports what ACL2 did.

## Evidence record

Each meaningful validation summary records: requirement/scenario/proof IDs;
source revision or content digest; tool/runtime/platform versions; exact command;
result and artifact location; assumptions; omitted cases and remaining risks.
Update the registries after evidence exists, not when a test file is merely added.

## What survives the run, and what does not

A certification run writes `build/acl2/certify-<UTC>-<pid>/`, and `build/` is
ignored (`.gitignore:6`). The directory exists only on the machine that ran
it, and a lane worktree, a farm root under `/home/ember/fn-lanes` or
`/tank/fn/lanes`, and a gate directory under `$HOME/fn-gates` or
`/tank/fn/gates` are all removed as routine housekeeping. Measured on dev at
`5698648`: 314 run ids were cited in tracked files, the oldest from
2026-09-19, and **not one of them resolved in the checkout**. 137 were still
recoverable from this laptop and the two boxes and are committed; the other
177 are gone and are named in `planning/evidence/manifests/LOST.txt`.

So the two halves of a run are treated differently.

- **The manifest is the claim and is durable.** `manifest.json` names the
  requested books, the expected and observed `FN_CERTIFY_SUCCESS` markers,
  the per-book verdict and wall seconds, the source and certificate SHA-256
  digests, the forbidden-facility audit, the ACL2 executable and its digest,
  the host Lisp banner, and -- since this lane -- the run id, the hostname,
  the worktree, the git revision and branch, and the start and finish times.
  It is 4 kB for a single root and up to 200 kB for a wide closure. Every
  one is filed under `planning/evidence/manifests/<run-id>.json`, keyed by
  run id alone, with no box, lane or gate in the path.
- **The logs are the bulk and are not durable.** `certify.log` is whatever
  ACL2 printed; it is not committed and it is deleted with its directory.
  The archived manifest's `archived_from` field says which machine held it
  and where, so a log that still exists can be found while it lasts.

Three tools write the archive, at the three points a manifest reaches this
laptop: `tools/certify_books.py` when a local run finishes (every exit,
including a refusal before ACL2 starts), `tools/farm.py wait` when a farm
run's evidence is fetched, and `tools/verdict.py` when a gate is harvested --
the gate manifest is carried home in the harvest's JSON rather than left on
the box for a reaper. The directory is ignored by default and a manifest is
tracked with `git add -f`, which `python3 tools/evidence_manifests.py sync
--add` does for exactly the runs a tracked file cites. Committing a manifest
and citing its run are therefore the same act.

**To re-run a claim from its manifest**: take `git_revision` and check it
out; `source_digests_sha256` says which book sources that revision must
have, and `requested_books`, `closure`, `affected_by`, `jobs` and
`timeout_seconds` say what was asked of the runner. `acl2_version`,
`acl2_executable_sha256` and `host_lisp_banner` say which ACL2 answered.
Re-running is `FN_ACL2_TIMEOUT_SECONDS=<timeout_seconds> python3
tools/certify_books.py <requested_books>`; the claim reproduces when the new
run's `certificate_digests_sha256` match, and `book_wall_seconds` says what
it should cost. A manifest whose `git_revision` is null predates this lane:
its source digests still identify the sources, but not where to find them.

## Current check

`make check` uses the standard library to check local Markdown links/anchors,
registry identities/references, milestone references, scenario coverage, and
evidence references for advanced statuses. It performs no network requests and
does not install dependencies or start a service.

It then runs `tools/host_check.py`, which is the one part of `make check` that
runs ACL2, and only when `FN_ACL2` names one: a host file is never certified,
so nothing else reads it until a bridge `ld`s it at start-up. Each host file
gets a fresh ACL2 that loads that file and nothing else, and must reach the
`ACL2 !>` prompt with no error reported while it loaded — the dynamic half of
the `host_names` lint in `tools/ledger.py`, which reports the same dependency
statically. With `FN_ACL2` unset the tool prints that it did not run and exits
0; a skipped run is not evidence. It needs installed certificates
(`python3 tools/certs.py install`), because an `include-book` inside a host
file reads a certificate `ld` will not produce.

`tools/evidence_manifests.py check` runs beside them and asks a different
question: not whether a book is right but whether a claim can be checked at
all. It compares the run ids cited in tracked files against the manifests
committed under `planning/evidence/manifests/`, and fails on a newly cited
run with no committed manifest -- the fix is `sync --add`, or `harvest
--host persvati|hbox` if the run was on a box. It tolerates the 177 rows of
`LOST.txt`, whose owners must re-run or retract them, and `--strict` fails
on those too once they are gone. `tools/cite_check.py` is the same family
for repository paths and deliberately does not read `build/`; this tool
reads nothing else.

Three static checks run beside it, none of them needing ACL2.
`tools/transcribe_check.py` is the crash model's cut correspondence;
`tools/teeth_check.py --summary` is the teeth audit's static half, which
reports and never fails; and `tools/session_depth.py` checks that every
session reaches the level its callee wants. That last one exists because the
served command chain is four session records deep and all three base
accessors read `car`, so a call that stops one level short is answered with a
plausible value rather than an error: four such misses shipped on 2026-09-20,
one of them leaving POST with no reply at all. It infers each formal's
session level from the calls the definitions make and fails on a wrong depth;
a walk spelled by hand instead of through one of the three named projections
is drift, counted and failed only under `--strict`. Its own cases are
`tests/test_session_depth.py`, four of which are the historical misses
reduced to their shape. `docs/proof-style.md` states the convention and what
the check cannot see.
