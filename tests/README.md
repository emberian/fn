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
| Operations | Restart, corruption handling, backup restore/incarnation rules, concrete resource limits |

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
and update the [closure inventory](../planning/archive/assurance-closure.md). Avoid a
single coverage percentage combining proofs, tests and platform assumptions.

## Contact scheduling

`tests/acl2/scheduler-tests.lisp` carries the evidence for C2-06. Its
starvation counterexample is one trace run under two policies: under the
stated unfair policy (`fn-sched-unfair-step`, deterministic priority with the
promotion queue removed) the large article receives no submit, and under the
aging policy the same trace submits it on the third contact tick. The rest of
the book is the reachable witness for each keystone in
`books/scheduler-invariants.lisp` and one `must-fail` per hypothesis.

## Crash campaign

`tests/campaign/` holds the native image's crash campaigns (the Python host's
campaign, `cuts.py` and `campaign.py`, retired with it in python-diet T5).
`native_cuts.py` is the cut table: every `fnn-at` cut of a native write path,
each naming the `:cut` step of the ACL2 program that transcribes it
(`books/byte-store-programs.lisp`, `books/store-log-route-programs.lisp`), and
`tools/native_program_check.py` (part of `make check`) checks, per program,
that the host function's syscalls, observations and cuts in source order equal
the program's steps. `native_operator_campaign.py` kills the developer image at
each cut through the public operator entry, reopens the store through the
owner's recovery, and checks the acknowledged content, the interrupted
operation and the retry against the crash choice the cut declares;
`native_production_kill.py` SIGKILLs the production image by pid at measured
instants of a POST stream, with no selector at all, and judges every reread.
Both run on hbox (`tools/hbox_native.sh`; their `test_native_*` modules).

What the campaign does not show. It kills a process; the operating system page
cache survives, so nothing here is evidence about power loss, about a drive
cache that discards a `F_FULLFSYNC` acknowledgement, or about torn sectors and
partially written blocks. It does not corrupt bytes: `specs/store-fault-matrix.md` and
`tools/power_loss.py` own that axis. It uses a single writer on one
host with a held lock, so it says nothing about concurrent writers or about a
filesystem losing cached metadata across a mount. The journals' cuts are
expressed by analogy with `fn-journal-crash`: no theorem binds an FNWF or FNRJ
record file to a journal slot, so those cuts are checked against the host
contract and the model's shape, not against a proved correspondence.

## The integration labs, and `make labs`

Two integration labs (both since retired with the Python host) were dead on
`dev` for a day and every `make check` was green for all of it. `receive_bpa_request` gained a required keyword-only
`bundle` on 2026-09-19; the callers in `tools/` were updated, two in `tests/`
were not; the four-node lab — the only end-to-end evidence for the
carried-media and crash-recovery rows of M3 — died at its first receive, and
`tests/ltp/run_fn_ltp_lab.py` died the same way. A lane recorded a 22-of-22
run from a branch predating the change, so the evidence record looked current.
Nothing in the tree ran a lab, so nothing noticed, and the one test that would
have failed had a skip keyed on a failure message and reported a SKIP.

`python3 tools/labs.py` runs them. Each lab is one row with three outcomes
kept distinct all the way to the exit code, the way D13 asks everywhere else:
**passed**, **failed**, and **not-runnable**, the last always carrying what is
missing and how to get it. A not-runnable lab is never a pass and never
silent; a lab that exits 0 and leaves no evidence file is a failure, because
that is the shape the four-node record took while the lab could not start.
The exit code is 1 only when a lab actually failed; `--require <name>` turns a
named lab's absence into a failure, which is how a box that is supposed to be
able to run one says so.

| Lab | Tier | Cost | Needs | What it carries |
| --- | --- | --- | --- | --- |
| `tcpcl` (`tools/tcpcl_lab.py`) | local | minutes, once the image exists | `build/fn-host` (`sh tools/build_native_host.sh`, which needs a certified tree) | two fn native hosts over TCPCLv4 on loopback: transfers both ways, a refused MRU, keepalives, a SIGKILL inside a transfer, a whole-bundle ADU, the trace folded back through the image |
| `inn` (`tools/inn_lab.py`) | box | about a minute | `--host` with the pinned INN (`tests/inn/pin.json`; `/tank/fn/inn/2.7.4` on hbox) and `--native-image` (D07) | the native fn owner against a real InterNetNews: fn's feed into innd, innfeed into fn, the octets each serves, duplicates and loops both ways, a cut on each side |

`tools/deploy_gate.py` (one commit shipped to a box, its native image
`--native-image` serving an independent client, the three outcomes, a
SIGKILL mid-session, the restart and the reread) is run by hand on a box; its
dry run is the `deploy-dry` row. The two-node gate's questions are
`tests/test_native_peering.py`'s (the receiver killed mid-`IHAVE` among
them), the dtn7 labs under `tests/bp-dtn7/` that drive the native image
(`run_mission_four_node.py`, `run_fn_bp_interop.py`) run by hand, and scale is
`tools/scale_curve.py`'s.

Two more rows are **harness dry runs**, printed in their own section and
never mixed with the labs: `deploy-dry` and `inn-dry` drive the real gate
scripts through bash on this machine with `HOME` redirected, a stand-in
native image and no ssh. They establish that the harness parses, sequences,
classifies and renders, and **nothing whatever about fn** -- and they are
what catches a gate script that no longer runs: `tests/test_inn_lab.py` was
red on `dev` on 2026-09-21 for exactly that reason, an `IndexError` on an
`nnrpd` pid the fake never wrote.

```sh
make labs-quick        # the two dry runs, about a minute
make labs              # the above plus every lab runnable off a box
python3 tools/labs.py --tier box --host hbox --commit dev
python3 tools/labs.py --list
python3 tools/labs.py --only tcpcl --json build/labs/report.json
```

Nothing here is wired into `make check`. `make check` is seconds and runs
before every commit; the quick tier is minutes and the box tier is hours, and
a gate nobody can afford to run is a gate nobody runs. What `make check`
gained instead is `tools/harness_check.py`, below.

## Two static lints on the harness

`python3 tools/harness_check.py` runs in about a second, needs no ACL2, and is
part of `make check`.

`signatures` binds every resolvable Python call in `tools/`, `tests/` and
`bin/` against the definition it names, the way CPython would at the call:
missing required parameters, unexpected keywords, too many positionals, a
parameter given twice. It resolves a call only when it can do so exactly — an
imported module attribute, an imported function, a constructor, or
`self.<method>` inside a class whose bases are all in the corpus — and counts
what it declined rather than guessing. On the tree at the time it landed it
resolved 3195 of 22719 call sites with 19 undecidable (`f(*rest)`,
`f(**rest)`), and it reported the missing `bundle` at
`tests/ltp/run_fn_ltp_lab.py` naming `tools/run_bp_receive.py:113` as the
definition. It fails on any finding.

`acl2-arity` asks the same question of two corpora that no certification
reads, and fails on unwaived mismatches: the `ld`ed files under `host/`, and **ACL2 forms
spelled inside Python string literals**. The second is the sharper target and
the one neither language can see. `d484e9a` gave `fn-served-open` a seventh
formal and updated both Lisp callers; a Python differential test (retired
with the Python host) spelled that call as text, so all seven of its tests
raised `FN-SERVED-OPEN takes 7 arguments ... given 6` instead of comparing
bytes, and no divergence check ran for a day.

It is deliberately not over `books/`: a book's arity is ACL2's own business,
`certify-book` refuses a wrong one, and what let the `books/owner` break
persist was a stale certificate rather than a missing check — which is what
content-keyed certificates (`docs/proofs.md`) fix. A host file is never
certified, and a Lisp form in a Python string is not Lisp to anything until it
reaches ACL2. `tools/host_check.py` answers the host half dynamically and only
when `FN_ACL2` names an ACL2; this is the always-on static half. Two kinds of
prose are skipped, each after it produced findings on the real tree: a
docstring, and a sentence that merely *mentions* a form — `"... the
authenticated principal's allowance (fn-auth-postingp, RFC 3977 section
6.3.1.1). The feed was never reached."` parses, so a string counts only when
every top-level item in it is a form, which prose never is. A form holding a
`{}` or a `%s` is not decided at all, because a `" ".join(...)` in that slot
stands for any number of arguments. Synthetic forms that deliberately use a
mismatched arity declare the exact callee and a reason in a same-line
`# acl2-arity-fixture:` comment. The gate counts these declarations, and a
declaration for one callee never waives a different call on that line.

`waivers` flags a skip whose predicate reads a **failure** rather than a
dependency: a substring of an exception, a non-zero return code, an NNTP
response code. An environmental skip names something that is missing; a waiver
names something that is broken, and a waiver with no identifier and no expiry
outlives its defect in silence. A flagged site may declare itself with a
`# waiver-ok: <reason>` comment, in the shape `tools/session_depth.py` already
uses — and a waiver with no reason is not a waiver. The reason must name a
registry identifier, an expiry, an owner, or a capability this tree has not
built; every accepted declaration is printed on every run, so they cannot pile
up unseen. It fails on any undeclared one. The lint reads one hop of
intra-function assignment and no further: a verdict that reached a guard
through a helper, a JSON file or another process is beyond a static reader,
and the sweep below is what those need.

## Host value shapes: static in `make check`, dynamic beside it

`acl2-arity` counts arguments; it does not count *values*. At `9c344d1d`
`host/owner-host.lisp` passed `(fn-owner-clock-observation state)`, a
`:program` function returning an error triple through `(value ...)`, as an
argument of `fn-pa-authorized-event`, and ACL2 refused the translate ("a
result of shape (MV * * STATE) where a result of shape * is required"). `make
check` was green; the image build on hbox was the first thing to see it.

`python3 tools/host_shape_check.py` is part of `make check`, needs no ACL2 and
takes about two seconds. It infers, to a fixpoint, how many values every
`defun` in `books/` and in the ACL2-mode host files returns (one, or an `mv`
of k, an error triple being k = 3), then walks every ACL2-mode host
definition and fails when a known shape meets a position that needs another:
a function argument, a `let`/`let*` binding, an `if`/`cond`/`case` test or
key, an `and`/`or`, `value` or `mv` argument, a non-final `pprogn`/`prog2$`
form, the term of an `mv-let` with k variables, an `er-progn` form or
`er-let*` binding that is not a triple, and conditional arms that disagree.
A head it does not model (a macro, `b*`, a lambda application, a definition
whose every arm is itself unknown) is counted as `undecidable`, never
guessed; on the tree when it landed there were none among 3703 checked
positions. It reports the `9c344d1d` file with exactly one finding
(`tests/test_host_shape_check.py`). It does **not** check stobj flow (a
`state` where a non-stobj formal is expected, which ACL2 also refuses), guards,
undefined names (the `host_names` lint's job), or the 28 raw Common Lisp files
the image loads under `(set-raw-mode t)`, where ACL2 translates nothing.

`make check-host-translate` is the dynamic check: it installs the cached
certificate pairs, then feeds ACL2 the ACL2-mode prefix of
`host/native/build.lisp` (every `include-book` and host `ld` before its first
`defttag`) exactly as `tools/build_native_host.sh` does, without saving an
image, under the slot pool. It exits 0 when every form translated, 1 on any
ACL2 error, and 2 (NOT RUN) when there is no ACL2, a book the prefix
includes has no certificate, or an include warned `[Uncertified]` because the
installed pairs do not compose. The whole prefix took about 7 s on the
maintainer's Mac; it is outside `make check` because a worktree rarely holds a
certificate set that composes, not because it is slow.

### The skip triage of 2026-09-21

All 32 unittest-level skip sites under `tests/`, and the 35 harness-recorded
skips under `tools/`, were read once. 33 were environmental and honest (no
ACL2, no openssl, not darwin, no `DTN7_REPO`, no `python3.12`, no
`cryptography`, no native image, not a git repository) and say what is
missing. Nine were capability probes in the gates — a surface this tree has
not built, recorded with the observed reply. The rest were waivers for a known
defect, and they are named individually in
[`planning/lanes/HANDOFF-w11-lab-gate.md`](../planning/lanes/HANDOFF-w11-lab-gate.md).

The structural repair was in `tools/deploy_gate.py`, which `inn_lab`
subclasses (as the retired two-node and scale gates did). `not_exercised()` builds a step with
`rc=None`, and `Step.failed` cannot see one, so the gate exits 0; every
"the server did not restart after recovery", "the lab produced no result",
"the profile pass printed no JSON" was recorded that way. There is now a
second recorder, `did_not_complete()` / `Gate.broke()`, for a step that did
not run because the gate's own subject failed: it records `rc=1` against
`expect=0`, so it is a failed step and the exit code says so. An absence is
still an absence; a symptom is now a failure.

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

`tests/test_gate_reap.py` is the same kind of test for the one tool that
deletes things: every verdict of `tools/gate_reap.py` is a pure function over
a gate listing, so the policy (a gate with a process in it is never stale; a
held box lock keeps everything; a box with no `/proc` keeps everything; the
newest gates of each tree and any revision git does not know are kept) is
exercised against listings the test writes, and the removal guards -- a
non-stale verdict, and six names that could widen an `rm -rf` -- are shown to
raise with nothing sent to the box.

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

Two tools write the archive, at the two points a manifest reaches this
laptop: `tools/certify_books.py` when a local run finishes (every exit,
including a refusal before ACL2 starts), and `tools/farm.py wait` when a farm
run's evidence is fetched. The directory holds ignored local drafts.
`python3 tools/evidence_manifests.py add RUN-ID` archives the bytes by SHA-256
and stages their logical name in `planning/evidence-index.tsv`; `sync --add`
does this for the runs a tracked file cites. Commit that index line with the claim.

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
so nothing else reads it until an image build `ld`s it. Each host file
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
`tools/native_program_check.py` is the crash model's cut correspondence;
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
