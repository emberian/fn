# Testing fn

One way to run each kind of test: the command, where it runs, what a pass
shows and what it does not.  The long account of validation by layer is
[tests/README.md](../tests/README.md); the scenario specifications are
[tests/scenarios/catalog.json](../tests/scenarios/catalog.json).

| kind | files | one test | where |
|---|---|---|---|
| ACL2 test book | `tests/acl2/*-tests.lisp` | `python3 tools/farm.py submit auto tests/acl2/NAME-tests` then `farm.py wait BOX RUN` | a farm box (persvati, hbox); the laptop only through `tools/acl2` |
| raw SBCL harness | `tests/native_*_raw.lisp` | `python3 -m unittest tests.test_native_raw_scripts` (all), or `sbcl --script tests/native_NAME_raw.lisp` | anywhere with the toolchain SBCL; `make check` |
| native module | `tests/test_native_*.py` | image-free half: `python3 tools/native_source_check.py tests.test_native_NAME`; image half: `tools/hbox_native.sh --image-set SHA . tests.test_native_NAME` | image-free: anywhere, `make check`; image: a build box |
| scenario | a row of `tests/scenarios/catalog.json` | run its witnesses (rows above, or a `tests/*.sh` its row cites) | where the witness runs |
| tooling test | `tests/test_*.py` that are not `test_native_*` | `make test-modules MODULES="tests.test_NAME"` | anywhere; `make tooling-test` runs the set |

## ACL2 test books

A test book includes the book it tests and asserts about it with
`assert-event`, `defthm` and `must-fail-checked`.  Every
`tests/acl2/*-tests.lisp` is a root of the Makefile's `ACL2_BOOKS`, listed
after the books it tests (`tools/test_roots_check.py`, in `make check`); a
book that cannot be a root yet names why in a `; UNHOOKED <who> (<date>):
<why>` first line.  Certify the root, never a closure:
`tools/farm.py submit auto tests/acl2/NAME-tests` installs what the box's
cache holds at current bytes and certifies the rest; `--affected-by
books/X.lisp` adds every root whose closure contains a changed book.
A lane's READY gate is a narrow `--recertify` of the books it touched, on
the laptop (with `FN_CERT_ORIGIN_KIND=run`, so other worktrees may install
the pairs: a `worktree`-origin pair is refused elsewhere as foreign-local)
or on persvati; the closure certify is the integrator's, once per batch.

A pass shows: each event holds in ACL2's logic, executed by ACL2's evaluator,
over the definitions at these bytes.  It does not show that the host calls
those definitions (`reach_check`), that the image's compiled code behaves the
same, or anything about I/O.  A test book about a function no host path calls
is deleted, not kept as coverage.

## Raw SBCL harnesses

`tests/native_*_raw.lisp` read host source (`host/native/*.lisp`) and the
ACL2 `defun`s it calls from their files, evaluate them in a plain SBCL, and
drive them with recording stubs for the I/O seams.  Each ends by printing a
line containing `PASS`.  `tests/test_native_raw_scripts.py` is the one
runner: it discovers every `tests/native_*_raw.lisp`; a harness that another
test module or `tests/*.sh` names is run there (it needs arguments, a fixture
directory or an ACL2 world), and every other one is run by this module as
`sbcl --script` from the tree's root under the toolchain SBCL (`FN_SBCL`,
else the image's runtime, else `sbcl` on PATH).  Adding a harness needs no
wiring; a one-line wrapper that only runs one is refused.  `make check` runs
the module through `tools/native_source_check.py`.

Six harnesses run over the real certified ACL2 definitions instead of
copies: six `tests/test_native_*.sh` scripts (`# witness: needs-acl2`)
include the books through `tools/acl2` and load the harness in raw mode.
They need a certified tree and run once per convergence (row 15a of
`planning/release-v6.6.0.md`).

A pass shows: the host function, as written, takes the branch the harness
asserts for the inputs and seam answers it supplies.  It does not show the
image (a different build, other definitions loaded, the real seams), guard
conformance, or real I/O.  Where the harness answers `fnn-core` -- the host's
call into ACL2 -- with values it made up instead of the real ACL2 function,
it tests host plumbing only: its file name ends in `-mock.lisp`
(`tests/native_*_raw-mock.lisp`, `*_source-mock.lisp`) and no proof or
requirement in `planning/` cites it as evidence; a scenario row may still
name it for the host step it drives.  To make one real, read the `defun`
from its book and route `fnn-core` to it (`tests/native_web_reactor_raw-mock.lisp`
does this for `fn-web-host-action-kind`, `native_live_config_cache_raw-mock.lisp`
for `fn-nret-request`); when no fabricated answer is left, drop `-mock`.

## Native modules

`tests/test_native_*.py` start a built image (`build/fn-host`,
`build/fn-host-developer`, the DTN images) and talk to it over its sockets
and files.  Each module also has image-free tests that read the source; with
no image those run and the image tests skip with a reason
(`tests/native_harness.py` `requires(...)`), and `make check` runs every
module that way (`tools/native_source_check.py`; a module that runs nothing
or errors for a missing image is a failure).  The image tests run on a build
box: `tools/hbox_native.sh --image-set SHA . tests.test_native_NAME` links the
published image set for dev commit SHA (`hbox:/tank/fn/images/SHA`) under
this tree; `tools/hbox_native.sh . tests.test_native_NAME` builds images
from this tree first (certify + build, tens of minutes).  The integrator's
set of twelve core modules is the release bar.

A pass shows: the behaviour, on that image, for that run.  It is evidence to
file (`tools/evidence_store.py put`), never a proof; a skipped test is not a
pass, and a module's image tests count only with the image's identity named.

## Scenarios

A catalog row (`SCN-NNN`) is a specification -- steps, expected outcomes,
`execution_scope` -- not a runner.  Its witnesses are tests of the kinds
above, or a `tests/*.sh` script that needs an image or a certified tree and
runs once in the convergence checklist.  `tools/witness_check.py` (in `make
check`) holds every `tests/*.sh` to a `# witness: CLASS` header, a runner for
its class, and a catalog row that cites it or the harness it drives.  A
scenario is exercised exactly as far as its row's `execution_scope` says.

## Scenario tiers

`tests/scenarios/tiers.tsv` groups the native modules that drive an image
(and the kits `hbox_native.sh` cannot launch) by the question each answers
and by how long a run takes; `planning/scenarios-2026-10-04.md` is the
coverage map behind it (questions x scenarios, the gaps, which assertions
did not test their claim).

| tier | what it answers | wall at `--jobs 4` |
|---|---|---|
| `peer` | can a stranger's server peer with us safely and usefully: transit both ways, catch-up, IHAVE/CHECK/TAKETHIS, NEWNEWS and HDR/XPAT past the cache, misbehaving peers, peer credentials, real INN (`FN_INN_SRC`) | ~20 min |
| `smoke` | one short module per question (durability cuts, the three outcomes, resend, bounds, reader bytes, TLS, cursor, web, feed, BP, store identity) | minutes |
| `core` | the integrator's twelve: the release image bar | ~10 min |
| `e2e` | one whole module per user-visible surface, consumer and hybrid opt-ins on | 30-45 min |
| `resilience` | crash cuts, fault injection, hostile input | an hour, plus kits |
| `scale` | fixture stores and the F1-F8 measurements (quiet box, current fixtures) | hours |

Run a tier against a published image set (no certify, no build):

    python3 tools/scenario_suite.py run smoke --image-set SHA        # tests at SHA
    python3 tools/scenario_suite.py run peer --image-set SHA --rev .  # this worktree's tests
    tools/hbox_native.sh attach smoke-SHA9                             # wait; print run.log

`--box lat1` (or cloud1, cloud2) runs a tier on a rented box: they mirror
the published image sets, but hold neither hbox's INN tree, nor docker, nor
the fixture stores, so peer_pull's INN cases, reader_clients and the scale
tier's fixtures need hbox (the default).  `run` prints the `hbox_native.sh`
command it starts and, for a tier's kits,
the command to run by hand on hbox.  `list [TIER]` shows each entry with its
questions and reason; `modules TIER` prints the module names for any other
runner (an overlay image is picked up through the same `FN_NATIVE_*`
variables every module reads).  Tell the integrator before a run; one run
at a time on hbox.  `tools/scenario_suite.py check` (in `make check`) keeps
the file honest: every module exists and drives an image, codes and opt-ins
are known, no `-mock` or source-only module is listed.

A tier's result is the run's `run.log` (OK / FAILED / SKIPPED per module,
with the image set named); a red is classified (implementation, harness,
environment) with the run id, never re-expected.

## What `make check` is

`make check` plans ~90 steps and `tools/check_steps.py` runs them in parallel,
skipping a step whose recorded inputs are unchanged since it last passed
(`make check FORCE=1` runs every step).  It needs no image; a step that needs ACL2 or
certificates it cannot find says NOT RUN and counts as failed.  `make check-lane`
is the same in a scratch directory; `tools/remote_check.sh auto` runs it on a
build box.

**Scoped and baselined runs.**  `make check-lane CHECK_CHANGED_SINCE=<rev>` (or
`tools/remote_check.sh BOX --changed-since <rev>`) runs only the steps the diff
from `<rev>` (committed, uncommitted and untracked files) can reach: the steps
whose last traced run, passing or failing, read, stat'ed or listed a changed
path, ran a git command the change can move, or could not be traced (ACL2, a
shell child).  The rest print `skipped`; a docs-only diff skips host_check,
reach_check and green_check.  A step this tree has never run is not skipped, so
the first run in a fresh worktree is a full one.  `CHECK_BASELINE=<table>`
(`--baseline`) reads a step table such as
`build/coordinator/check-baseline-<sha>.txt` (or a remote_check log holding
one), prints `NEW reds vs baseline: ...` and exits nonzero only for a red step
the baseline did not have red (matched by step name and, for a name planned
several times like host_check, by finding with its numbers ignored);
`CHECK_BASELINE_OUT=<file>` (`--write-baseline`) writes this run's table in that
format.  A scoped run is a lane's gate, not the integrator's: a full
`make check FORCE=1` at the batch head stays the evidence.
