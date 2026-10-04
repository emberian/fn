# Iteration architecture: verdicts as cached facts, the red set as the target (2026-10-04)

Lane `iter-arch` (Fable), from ember: "review our python piles ... propose how
we can rip and tear and do this more sensibly from within the lisp OR actually
sensible with the python, and lets NOT BE EXECUTING ALL OF THIS EVERY TIME ...
do the least amount of work to iterate on exactly and only what is red ... we
will continue to converge-forward fixes rather than reverting or doing
full-green gates."  And: "we used to have <3 minute iteration times."

Everything below is measured on the batch-3 run on hbox (set-bdd4f40c4-r2,
`/tank/fn/scratch/integrate-20261004/native-set-bdd4f40c4-r2/`), the hbox
`make check` baseline at 4fd4cfc51
(`build/coordinator/check-baseline-4fd4cfc51.txt` in the integrate tree), the
loops lane's table (`planning/loops-2026-10-04.md`) and the tree at
origin/dev 6107ceb56.  Where a number is not measured it says so.

## 1. Diagnosis

### 1.1 One sentence

About seventy percent of every iteration is spent re-deriving verdicts the
tree already has: `make check` re-runs its 47 red steps every time because a
failure is never cached (2,038 of 2,849 step-seconds), and the native modules
spend 1,985 of 2,791 test-seconds in 23 tests, most of them known reds that
cost their full deadline on every run.  The rest is image-cycle work whose
inputs did not change (install and certify of 1,136 books that were all
already in the cache: 18.5 minutes; two acquires: 33 minutes).

### 1.2 The batch-3 image cycle, step by step (hbox, run.log timestamps)

| step | wall | what it did | input that changed |
|---|---|---|---|
| install (certs.py install-partial) | 6m57s | installed 1,136 of 1,136 books from `/tank/fn/certcache`, 0 missing | nothing: every pair was already keyed and present |
| certify (certify_books.py --incremental) | 11m34s | "installed 1136 of 1136 ... certifying 0" (`logs/certify.log`) | nothing: 11.5 minutes to certify zero books (lane_edges re-walk + source audit, `planning/loops-2026-10-04.md` row b) |
| acquire (proof_artifacts.py) | 19m42s | chose artifact set 940547090b, composed, 1,135 books | the chooser and the 2 GB pair memo (loops: "parsed whole on every check") |
| validate | 14 s | ACL2 loaded 469 roots and said `loaded` | this is the only step here that ACL2 itself needed |
| host-forward + host-ld | 1m + 2m51s | `host_translate_check`: 199 includes, 45 `ld`s in 171 s | host bytes (real work when host/ changed) |
| acquire-dtn + validate-dtn + host-ld-dtn | 13m08s + 11 s + 55 s | the same again for the DTN profile | nothing new: the dtn closure is a subset of the default one |
| image-developer / production / dtn / dtn-developer | 2m21s / 3m08s / 1m28s / 1m58s | four `save-exec`s of the same world | host bytes; the four differ only by profile and world stripping |
| modules, 35 at jobs 4 | 17m48s (2,791 s summed) | 351 tests: 19 modules OK, 16 FAILED, 55 red cases | see 1.4 |
| total | 83m26s | | |

What ACL2 and SBCL actually needed: validate 14 s, host-ld 171 s (x2), four
saves ~9 min.  Everything else, about 50 minutes, is Python deciding what to do
with inputs that had not changed since the previous set (the loops lane cut
the laptop-side install-set from 680 s to 36-46 s; hbox's acquire "waits for
the next image set built with these tools").

### 1.3 `make check`: a failure is never cached, and half the steps are red

`tools/check_steps.py` already does the right thing for a PASS: it traces every
file a step read (`tools/check_trace/sitecustomize.py`), keys the step by the
digests of exactly those inputs, and replays a stored output when nothing
changed (`check_steps.py:33-39`).  Two lines undo most of the benefit:

- `check_steps.py:41` "A failure is never cached", enforced at `:846`
  (`if code == 0:  # a forced run refreshes the cache too`).  The hbox
  baseline at 4fd4cfc51: 91 steps, 47 red, 994 s wall at 12 jobs, 0 cached;
  the 47 red steps sum to 2,038 of 2,849 step-seconds.  host_check --load
  alone is 792 s and red (NOT RUN: 190 books uncertified in that tree).  Every
  one of those reds re-runs on every `make check` and every `make check-lane`
  of every lane, although for 40 of them nothing they read changed (they are
  baseline ratchets: owner_globals 65 vs 50, list_codec 84 vs 92, cost
  obligations 161, premise_audit 1,378, hot_path 187, ...; the wave-0 list in
  `build/coordinator/decisions-20261004.md` disposes most of them as
  baseline-with-reason or design).
- `check_steps.py:108` `DEFAULT_CACHE = ROOT / "build" / "check-cache"` and
  `:622-626`: inputs are keyed by ABSOLUTE path.  The cache is per worktree
  and per box: a fresh lane worktree runs everything ("a step never traced
  here runs", `:52`; loops row e: 1,413 s cold against 186 s scoped), and no
  verdict produced on hbox or persvati is ever reused on the laptop or in a
  sibling worktree, even for identical bytes.

The per-step analyses are the other half: `ledger --load-tree` 131 s warms a
tree cache, then check_scaffold 112 s, certified_claims 76 s, current_view
80 s, proof_cost 78 s, cite_check 193 s, keystone_emit 125 s, interface_emit
74 s, reach_check 72 s, coverage 54 s, green_check 90 s each re-walk books.
Eleven of these tools carry their own Lisp reader
(`ledger.py:430 read_forms`, `lock_discipline_check.py:181`,
`native_overlay.py:216`, `native_program_check.py:117 tokenize`,
`reach_check.py:261`, `theory_check.py:90`, `clock_unit_check.py:105`,
`coverage.py:901 top_level_forms`, `proof_repl.py:349`,
`proof_artifacts.py:50`, `extract/world.py:85`), and 44 files grep for
`include-book` with their own regex.  38 `*_check.py` files, 23,089 lines,
each reading the tree from scratch.

### 1.4 Natives: a few real-time tests, re-paid in full every run

Per-test timings from `FN_TEST_BUDGET_RESULT` in the 35 module logs:

| | |
|---|---|
| tests | 351 (55 red: 49 failures + 6 errors; 16 of 35 modules FAILED) |
| median test | 1.3 s; p90 9.8 s |
| tests over 20 s | 23, summing 1,985 of 2,791 s (71 %) |
| the four worst | peering `test_feeding_past_the_queue_bound` 449 s (OK: 1,100 articles fed to a streaming peer, awaiting each batch under a 600 s deadline); page_io `test_cancel_retire_and_reuse` 381 s (FAIL at its deadline); over_pins `test_a_large_article_drained_slowly` 317 s (ERROR: a 300 s socket read timed out); bp_node `test_deletion_report_intent` 123 s (ERROR) |
| per-test fixed cost | about 3 s (test_native_owner: 30 tests in 91 s, 29 of them 3 s or less, each with its own `init` + owner start of the 242 MB developer core) |

So the modules are not slow because a core boots slowly (the owner module
shows 3 s per test, the live owner in `native_overlay.py live` starts in
0.35 s).  They are slow because (a) a red test costs its whole deadline
(`timeout=600` x 91 occurrences, `=300` x 68, `=120` x 105 in
`tests/test_native_*.py`), and the batch re-pays that on every run for every
known red; (b) a handful of tests wait on real policy time (idle limit 3 s +
`time.sleep(5)` x2 in over_pins; retire `--drain 120`; `await_article(...,
timeout=600)` per batch of 1,100).  175 `time.sleep` calls across the modules,
two of them `sleep(600)`.  The host has exactly one clock seam
(`host/native/io.lisp:671-675`, `*fnn-monotonic-ticks*`, "for bounded retry
tests and no other policy decision") and 77 direct uses of
`get-universal-time` / `get-internal-real-time` in nine host files, so
virtual time is not yet available to the policy paths the slow tests wait on.

### 1.5 The pipeline runs each verdict three times, then once; now twice

`planning/landing-pipeline.md` already moved from triple testing to "one owner
per check, evidence passed by content", and the overlay
(`tools/native_overlay.py`, 23 s to the first module) removed the image cycle
from the lane's host loop.  What remains duplicated: the lane's `make
check-lane` and the integrator's `make check FORCE=1` at the batch head recompute
every step from nothing even when the batch head's bytes for that step's
inputs equal the lane's (the FORCE=1 pass "must not rest on another tree's
cached verdicts", `check_steps.py:58-59` -- a rule written because the cache
was per tree and not content-addressed; with a content-addressed verdict
store, the pass can reuse a verdict whose inputs' digests it re-verifies and
still be the evidence).

### 1.6 Size of the Python

tools/: 238 `.py` files, 113,221 lines (+19 `.sh`, 3,705; 59 `.lisp` under
tools/).  Growth: the history was rewritten on 2026-09-20 (43 files in
tools/ at e9446ae75 then; 387 now), so churn is not measurable from `git
log`; the net diff is +125,140 / -11,293 in 14 days.  By kind:

| kind | files | lines |
|---|---|---|
| `*_check.py` | 38 | 23,089 |
| cert/farm/REPL (`farm`, `certs`, `certify_books`, `proof_repl`, `proof_artifacts`, `certify_triage`, `chain_schedule`, `acl2_slots`) | 8 | 12,487 |
| labs and measurements (`inn_lab`, `hostile_campaign`, `power_loss*`, `fitness`, `scale_curve`, `fundamentals`) | 7 | 11,370 |
| `resilience/` | | 7,470 |
| `ledger`, `current_view`, `coverage` | 3 | 7,058 |
| native run (`native_*`, `hbox_native.sh`, `image_set`, `test_budget`, `native_box.sh`) | | 6,906 |
| `extract/` (image world, ACL2-side) | | 5,040 |
| `*_emit.py` + `*_gate.py` | 10 | 5,918 |
| clients (`fn_client`, `fn_consumer`, `fn_verify`, `fn_dev`) | 4 | 3,212 |

tests/: 217 `test_native_*.py` (51,113 lines), 211 other `test_*.py`
(49,538), 166 raw SBCL harnesses (28,295), 1,202 ACL2 test books (245,504).
Makefile `ACL2_BOOKS`: 2,511 roots.  books/: 1,812 files, 683,794 lines.
host/: 78,135 lines (host/native: 83 files, 50,641).

Named by nothing else in the tree (Makefile, docs, planning, tools, tests,
packaging): 8 tools, 1,778 lines: `cost_gate.py` (825),
`native_sparse_newnews.py` (233), `codec_golden.py` (195),
`build_compress_dict.py` (167), `available_read_emit.py` (140),
`spw_entry_inventory.py` (81), `runtime_decoded_source_prefix.py` (74),
`repair_unittest.py` (63).

## 2. Target architecture

Three objects, and every tool either produces or consumes them.

### 2.1 Verdicts are content-addressed facts

A VERDICT is `(kind, subject, inputs-digest) -> (outcome, output, where,
when, tool-version)`.  `kind` is one of `check-step`, `test-case`,
`native-module`, `raw-harness`, `certify`, `host-ld`, `image`.  `outcome` is
one of PASS, FAIL, NOT-RUN, KILLED (the distinctions AGENTS.md already
demands).  `inputs-digest` is the SHA-256 of the sorted list of exactly what
the verdict depended on:

- check-step: the traced reads/listings/stats/git-outputs `check_steps.py`
  already records, with paths RELATIVE to the tree root for anything inside
  it (absolute only outside: the interpreter, site-packages), plus the
  command, the `FN_*` environment and the Python version.  This is the
  existing key with one change (relative paths) so it is the same key in
  every worktree and on every box.
- certify: the closure key `certs.py:587 closure_key` already computes
  (form hashes of the book and its whole include closure) plus the toolchain
  identity.  Already content-addressed; nothing changes.
- native-module / test-case: the digests of the test module file, of
  `tests/native_harness.py` and every tests/ import it pulls, of the image
  (core + launcher SHA-256, which `tools/native_env.py identity` already
  exports) or the overlay record (`OVERLAY.json`'s plan digest over the base
  set), of `tools/test_budget.py`, and of the `FN_*` environment the module
  reads (`tools/native_env.py` finds those).
- raw-harness: the harness file, the host files it `load`s and the books it
  reads (it names them; the tracer sees them when run under Python, or the
  harness prints its own `read` list), and the SBCL identity.
- host-ld: the build script's ACL2-mode prefix (`host_translate_check.py`),
  i.e. the closure key of every included book and the digests of the 45 `ld`
  files, and the ACL2 identity.
- image: host-ld's key plus the raw region and the build script, the C
  libraries, VERSION and the profile/world flags (what `native_overlay.py`
  calls "image inputs").

Staleness is exact, never heuristic: a verdict is reused only when every
input digest re-verifies against the bytes in front of the tool.  There is
no "since sha" and no mtime (the `FileMemo` keeps mtime+size only as a hint
for which digests to recompute).  A step the tracer cannot see into (an ACL2
child, a shell) keeps its `x` mark and is never cached, as today, until it
declares its inputs itself (certify and host-ld do, by closure key).

Where the cache lives: `build/verdicts/` is only a local view.  The store of
record is one directory per box under the certificate cache's roof
(`/tank/fn/certcache` already is the content-addressed store lanes share on
hbox; `~/fn-certcache` on persvati; `~/.cache/fn/verdicts` on the laptop),
laid out as `<kind>/<inputs-digest>.json`, written atomically (rename), and
synced the way `farm.py mirror_cache` and `certs.py mirror` already sync
pairs: rsync of new entries after a run, pull before a run.  A verdict entry
is small (the output, truncated to 64 KB, with the full log's evidence hash
when it was filed).  Nothing is ever invalidated: a changed input is a new
key.  Pruning is by age and by `kind` (certify entries are already pruned by
`certs.py prune`).

What a cached verdict is for, and what it is not (the integrator's
conditions, 2026-10-04, accepted): it is for the LOOP, so a lane never
re-runs a red whose inputs it did not touch.  It satisfies no READY and no
batch gate: a lane's READY is a live run of the steps its change reaches,
and the batch runner's `FORCE=1` pass stays a full live run.  For that to be
safe with one store per box, the key covers what a red usually depends on
outside the tree -- the interpreter path and version, the `FN_*`
environment, the ACL2 and SBCL launchers' paths and digests -- so an
environment red stops replaying the moment the box is fixed; and a replayed
red names the run that produced it (sha, box, time, log path), so the reader
opens the real failure, not a replay.  Non-verdicts (exit 2 NOT RUN, a
signal, 127) are never cached.

### 2.2 The red set is a first-class object

`build/reds.json` (and `planning/reds.md` generated from it, committed by the
integrator per batch): one row per red verdict, keyed by the verdict key,
carrying the subject, the first finding, the run it came from, the disposition
from `decisions-20261004.md` (fix / baseline-with-reason / design / delete),
the owner, and the IMPACT SELECTOR: the set of inputs whose change could flip
it.  For a check step the selector is its traced input list; for a test case
it is the module and the host/book files its subject names (reach_check and
`host_callers.py` already map host functions to books); for a certify red it
is the book's closure.

`tools/iterate.py` (new, small; the only new orchestration entry point) takes
the diff of this worktree against the last published verdicts and answers
"what must run": every red whose selector the diff touches, plus every green
whose inputs the diff changed (the existing `--changed-since` scoping, now
exact because it is by digest), and nothing else.  It then runs those in the
cheapest form that produces the verdict kind: a check step locally, a test
case against the warm owner (2.4), a book in the live REPL (`proof_repl.py
resync`, 0.17-0.29 s per event), a native module as an overlay on the
published set.  It prints the new red set and the delta.

The full suite becomes background confirmation: an idle box (`tools/boxes.sh
--pick` already knows which) runs the whole set against the newest published
image set and the newest dev head, writes verdicts into the store, and the
delta appears in `reds.md` at the next batch.  No lane and no batch waits for
it.  A red it finds blocks the affected claim, as landing-pipeline.md says, and
nothing else.

### 2.3 Lisp owns the facts about Lisp

- The dependency and impact map comes out of the world, not out of eleven
  Python readers.  One ACL2-side exporter (`tools/extract/world-facts.lisp`,
  loaded into the developer image or a REPL session): for every book in the
  world, its include list; for every function, its book, guard status
  (`guard-verified`), arity and `:program`/`:logic` mode; for every theorem,
  its book, its `rule-classes` and the functions it names; for every host
  file, the names it calls that the world defines.  ACL2 already holds all of
  this (`include-book-alist`, `symbol-class`, `formals`, `theorem` and
  `runic-mapping-pairs` properties).  Validate loads 469 roots in 14 s; the
  dump is one walk of the world, seconds (not yet measured: the first slice
  that builds it measures it).  `ledger.py`'s 131 s tree read and
  `harness_check`'s 24,612 definitions re-derived in Python (51 s) become
  readers of one JSON, and the "what ACL2 said" column is literal.
- The Python checks keep their rules but share ONE reader: the s-expression
  reader in `ledger.py` (which never interns or evaluates, the rule AGENTS.md
  sets for parsing) moves to `tools/lisp_reader.py`, cached per file digest
  under `build/cache/forms/<digest>.json`, and the other ten readers are
  deleted in favour of it.  The check rules (reach, theory, holder, payload
  kinds, clock units, alphabet, lock discipline) stay in Python; that is the
  right language for a lint over a form tree.  Where the rule is about the
  WORLD (guard verified, reachable from the host, arity), it reads the ACL2
  dump instead of re-deriving.
- The native test harness drives a warm owner over the seams the host already
  exposes, and the per-test process choreography moves next to the owner.
  `host/native/dev-repl.lisp` (`fnn-dev-load`, `fnn-dev-admit-file`, one form
  per connection on an AF_UNIX socket with UID check) plus
  `native_overlay.py live` (owner + REPL in 0.35 s) are the seam.  A module
  gets one owner for its class (`setUpClass`), a store snapshot taken after
  `init` and restored per test (the store is files under `root`; a copy of
  the directory, or a ZFS snapshot on hbox, is the reset), and the tests that
  need a FRESH process (crash cuts, startup refusals, `FN_NATIVE_TEST_*`
  stall files bound at start) say so and keep their own.  Python stays the
  test language: it is the NNTP client, the assertion library and the
  unittest runner; what goes is 2 x 242 MB core starts per test and the
  `Node.init` + `start` + `stop` + diagnostics choreography repeated 351
  times (`tests/native_harness.py:1094-1323`).  This is the scenarios lane's
  work (warm owners, test-profile deadlines); the verdict key above is what
  makes their result reusable, so their deliverable should write the
  `test-case` verdict rows and the module's `FN_TEST_BUDGET_RESULT` line is
  the record.
- Time.  Deadlines and stall windows become profile parameters (D27: bounds
  belong to the operator's supported profile), read by the host from the
  same `profile` the test selects, so a test profile declares
  `exposure-idle-seconds 1`, `feed-retry-backoff 0.2`, `retire-drain-grace 2`
  and the host's policy paths read them through one accessor.  Virtual time
  (a test-settable `*fnn-monotonic-ticks*`) only works once the 77 direct
  clock reads in nine host files go through that seam; until then the test
  profile is what shortens real waits without weakening what is tested (the
  bound is the same function of the profile).  The 449 s feed test waits on
  real backoff; with a test-profile backoff it is the time to feed 1,100
  articles (not measured; the scenarios lane measures it).

### 2.4 Orchestration stays in Python, in one place

`check_steps.py` (1,064 lines) is already the right shape: a planner, a
tracer and an input-keyed cache.  It becomes the verdict engine for every
kind (its `Executor` gets a `kind` and a store), and `farm.py`,
`hbox_native.sh`, `remote_check.sh`, `scenario_suite.py` become thin clients
that ship a tree and ask the engine on the box to produce verdicts.  The
three overlapping closure/selection implementations (`certs.py closure /
_closure / include_graph / closure_key`, `certify_books.py local_closure /
dependency_graph / lane_edges / affected_roots`, `farm.py closure_keys`,
`proof_artifacts.py`'s own include walk) collapse onto the ACL2 dump when it
exists and onto one `closure.py` until then.

## 3. Rip-and-tear list

| action | what | size | risk | coverage kept by |
|---|---|---|---|---|
| CHANGE | `check_steps.py`: cache FAIL verdicts too; relative-path keys; `FN_VERDICT_STORE` for a shared store; `kind` on entries | ~120 lines | low: replay is exact by digest; `--no-cache` unchanged | `tests/test_check_steps.py` + a new case "a red whose inputs are unchanged replays as the same red; a changed input re-runs" |
| CHANGE | `certify_books.py --incremental` when nothing certifies: answer from the cache index in seconds, never re-walk `lane_edges` (loops row b cut 426 s to 20 s; the remaining 11.5 min on hbox is the audit + umbrella build for a zero-book run) | ~60 lines | low | same manifest line "installed N of N, certifying 0" |
| REPLACE | the second `acquire` (dtn, 13 min in r2) by a lookup against the first set's chosen pairs (r2: dtn set 1,085 books, 427 roots; default 1,135 books, 469 roots, same toolchain; whether the dtn closure is a subset of the default one is NOT verified here -- the slice checks it first, and where it is not, acquires only the difference) | ~40 lines in `proof_artifacts.py` | low: `validate-dtn` still loads the roots | validate-dtn unchanged |
| MOVE TO LISP | the dependency/definition/theorem facts: `tools/extract/world-facts.lisp` dump; `ledger.py` reads it for include graph, guard status, arity | new ~300 lines Lisp, deletes the include-graph half of `certs.py` (~400 lines), `certify_books.py:418-535` (~120), `harness_check`'s arity derivation (~300) | medium: the ledger's SUSPECT shapes still need the forms; keep the reader for those | `ledger --check` output identical on the tree; `harness_check acl2-arity` finding count identical |
| MERGE | eleven Lisp readers into `tools/lisp_reader.py` (ledger's), per-digest form cache | deletes ~10 x 60-150 lines; adds the cache (~80) | medium: readers differ at the edges (`#\\(`, `|bars|`, `#.`); the merged one takes the union and each check's test file is the oracle | each `*_check.py`'s unittest module passes unchanged |
| DELETE | the 8 tools named by nothing (`cost_gate.py` 825, `native_sparse_newnews.py` 233, `codec_golden.py` 195, `build_compress_dict.py` 167, `available_read_emit.py` 140, `spw_entry_inventory.py` 81, `runtime_decoded_source_prefix.py` 74, `repair_unittest.py` 63) | 1,778 lines | low; verify each with `git log -1 --format=%cd -- tools/X.py` and ask the owner named there before deleting `cost_gate` (it looks like a gate someone meant to wire) | nothing ran them |
| MOVE | the per-test owner start/stop choreography in `tests/native_harness.py` `Node` (`:1094-1323`, 230 lines) to a class-scoped warm owner + store snapshot (scenarios lane) | -2 x 242 MB core starts per test | medium: tests that depend on a fresh process must say so (`fresh=True`) | per-module `FN_TEST_BUDGET_RESULT` counts identical, timings lower |
| REPLACE | deadlines and sleeps in tests by profile parameters (D27) read by the host | 175 `time.sleep`, 400+ `timeout=` kwargs | medium: each shortened bound must still be the policy's bound | the same assertions; the test profile is named in the verdict key |
| KEEP, THIN | `farm.py` (2,144), `hbox_native.sh` (799), `remote_check.sh`: ship + ask the engine; the preflight/selection logic moves into the engine | -600 lines over time | low if done per command | their unittest modules |
| KEEP | `proof_repl.py` (4,432), `native_overlay.py` (942), `test_budget.py`, `image_set.py`, `chain_schedule.py`: these are the fast loops | | | |
| LEAVE | labs and measurement tools (11,370 + `resilience/` 7,470 + `runtime_floor/` + `image_anatomy/`): not on the iteration path; audit for dead ones separately | | | |

## 4. Build plan, in slices

Each slice is independently useful, measured before and after, READY to the
integrator with the measurement in the commit.  Shared tools (`check_steps`,
`farm`, `hbox_native`, `certify_books`, `native_harness`) keep their command
lines; a change is announced to the integrator before the push.

### Slice 1 (one lane-day; this lane, today): reds are cached verdicts

`check_steps.py`: store a FAIL entry under the same input key as a PASS and
replay it ("red (inputs unchanged since <sha>)", exit code and output
preserved, the row still red, `NEW reds vs baseline` unaffected); key inputs
by tree-relative path; `FN_VERDICT_STORE=DIR` names a store shared by every
worktree on the box (default stays `build/check-cache`).  `make check-lane`
on the laptop twice on an unchanged tree: before, the second run re-runs all
47 reds; after, 0 steps run.  A fresh worktree of the same bytes with the
shared store: before 709 s (loops row e), after close to 0 (measured on lat1
when the slice lands).  Prerequisite for every later slice: the verdict
record and the store layout.

### Slice 2 (one lane-day): the red set and `iterate.py`

`tools/reds.py` reads `build/check-steps/results.jsonl`, the native run logs'
`FN_TEST_BUDGET_RESULT` lines and `certify_triage.py`'s table into
`build/reds.json` with impact selectors; `tools/iterate.py --since REV` runs
exactly the reds and the reached greens, locally, and prints the delta.
Measured: a one-file host edit on the laptop: before `make check-lane
CHECK_CHANGED_SINCE` 186-313 s; after, the steps the file reaches only (the
scoped run already skips the unreached; the gain is the reds it no longer
re-runs: expected 60-70 % of the scoped wall, measured when built).

### Slice 3 (two lane-days): native and test-case verdicts in the store

`tools/test_budget.py --one` writes a `test-case` verdict per test with the
key of 2.1 (module digest, harness digests, image identity, FN env);
`hbox_native.sh` and `scenario_suite.py` ask the store before launching a
module and run only the cases whose key is new or red, unless `--all`.
Measured on the published set: a second run of the 35-module core on the same
set and tree: before 17m48s, after only the 55 reds' cases (sum of their
timings in r2: not computed separately here; bounded by 1,985 s at jobs 1,
under 9 min at jobs 4).  With the scenarios lane's warm owner and test
profiles, the same reds cost seconds.

### Slice 4 (two lane-days): the image cycle does only what changed

`certify --incremental` answers "nothing to certify" from the index; one
acquire serves both profiles; the image build is skipped when the `image`
key is in the store and the published set's cores carry it (`image_set.py`
records the key).  Measured: a host-only change at the batch head: before
83 min (r2), after host-ld 2 x 3 min + 4 saves 9 min + modules; a tests-only
or docs-only batch: no certify, no acquire, no image (zero).

### Slice 5 (three lane-days): the world dump and one reader

`tools/extract/world-facts.lisp` + `ledger.py` reading it; the ten extra
readers deleted.  Measured: `ledger --load-tree` 131 s cold on hbox against
the dump's load time; `harness_check` 51 s against reading arity from the
dump; `make check` summed step-seconds before/after at the same head.

### Slice 6 (background, the cloud lane): the full suite as confirmation

An idle-box loop over the newest published set and dev head writing verdicts
into the store; `planning/reds.md` regenerated per batch.  Measured: time
from a dev push to a complete red set for it, with no lane waiting.

## 5. The target loop

Times are expected on an unloaded laptop or lat1 with the store warm; the
measured anchors are in parentheses.

(a) Book edit.  `proof_repl.py resync NAME BOOK --from EVENT` on the live
session (0.17-0.29 s per event, measured); `iterate.py --since dev`
selects the test books and direct includers whose closure key changed and
submits `farm.py submit auto --lane --affected-by BOOK` (69 s measured for 7
books on a loaded laptop); reach/keystone/cite steps whose traced inputs
include the book re-run from the form cache (seconds each once slice 5
lands; today 72-193 s each).  Verdict on the book: under 2 min; make-check
steps it reaches: 2-4 min today, under 1 min after slice 5.

(b) Host edit.  `host_check.py --read` (0.5 s) and `--load` of the raw files
(4.8-5.9 s measured for the ACL2 load; 180 s end to end today, the rest
being install-set, which slice 4 makes a lookup); `native_overlay.py plan`
(seconds) and the overlay on the published set (23 s to the first module,
measured); the test cases whose key names a changed host file or that are
red, against a warm owner (seconds per case after the scenarios lane; today
the module: 91 s for owner, 3 s per case).  Verdict: 1-2 min for the module
that owns the change; a red that depends on timing is confirmed on a built
image in the background, never in the loop.

(c) Test edit.  Only that module's key changed: image-free half under
`native_source_check.py` (43 s for all 217 modules today; one module is
seconds), image half as an overlay-free run on the published set: ship 10 s,
link 6 s, the module (its cases, not the suite).  Under 1 min for a
typical module; the slow modules are the scenarios lane's deadlines work.

The three loops share one rule: nothing with an unchanged key runs, a red
with an unchanged key is reported from the store (with its run id), and the
suite runs in the background on a box nobody is waiting for.

## 6. What to measure to prove each slice

| slice | measurement | before (measured) |
|---|---|---|
| 1 | `make check-lane` twice on an unchanged tree: steps run on the second pass; fresh worktree with the shared store: wall | 47 of 91 run again; 709 s fresh |
| 2 | one-file host edit: steps run and wall of `iterate.py` vs `make check-lane CHECK_CHANGED_SINCE` | 186-313 s |
| 3 | second native run on an unchanged set + tree: cases run and wall | 351 cases, 17m48s at jobs 4 |
| 4 | batch head with a host-only change: wall to the first module; docs-only: wall | 65 min (r2) ; same |
| 5 | `ledger --load-tree`, `harness_check`, `reach_check` seconds at one head; `make check` summed step-seconds | 131 / 51 / 72 s; 2,849 s |
| 6 | push-to-complete-red-set latency with no lane waiting | not measured today (nobody runs the full set unasked) |

Not measured here, and said so: the world dump's own time; the per-case
cost of the 55 reds separately from the 23 slow greens; which of the 8
orphan tools someone still runs by hand; the warm-owner per-case floor.
