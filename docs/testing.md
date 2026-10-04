# Testing fn

One way to run each kind of test: the command, where it runs, what a pass
shows and what it does not.  The long account of validation by layer is
[tests/README.md](../tests/README.md); the scenario specifications are
[tests/scenarios/catalog.json](../tests/scenarios/catalog.json).

| kind | files | one test | where |
|---|---|---|---|
| ACL2 test book | `tests/acl2/*-tests.lisp` | `python3 tools/farm.py submit auto tests/acl2/NAME-tests` then `farm.py wait BOX RUN` | a farm box (persvati, hbox); the laptop only through `tools/acl2` |
| raw SBCL harness | `tests/native_*_raw.lisp` | `python3 -m unittest tests.test_native_raw_scripts` (all), or `sbcl --script tests/native_NAME_raw.lisp` | anywhere with the toolchain SBCL; `make check` |
| native module | `tests/test_native_*.py` | image-free half: `python3 tools/native_source_check.py tests.test_native_NAME`; image half: `tools/hbox_native.sh --image-set SHA . tests.test_native_NAME`; a host edit over a published set: `tools/hbox_native.sh --image-set SHA --overlay . tests.test_native_NAME` | image-free: anywhere, `make check`; image: a build box |
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

## Overlay: a host edit's native verdict without an image build

`tools/hbox_native.sh --image-set SHA --overlay REV tests.test_native_NAME`
(REV `.` is this worktree, uncommitted files included) runs the modules
against the published set for SHA with REV's changes since SHA applied to
its cores.  `tools/native_overlay.py plan SHA REV` runs here first: it diffs
every file an image loads (the build scripts' `ld` and raw `load` files and
the books their worlds include) form by form, and either lists what it will
apply or refuses, naming each form, a change a definition swap cannot carry:
a changed defmacro, defconst, defconstant, defparameter, defvar, declaim or
inline function (callers hold the old expansion or value), a defstobj,
defabsstobj, attach-stobj, defstruct or defclass (never mix obsolete
layouts), a table, definterface or defattach event, a top-level form with a
load-time effect, a function some build-time form calls (its result is in
the saved core) or whose object a registration captured (`#'NAME`), a
deleted definition still named, and every image input (build scripts, C
libraries, VERSION, the world umbrellas, the sealed dispatch table).  On the
box `native_overlay.py build` restarts each base core into ACL2's loop,
admits the ACL2 forms with redefinition allowed (and proves again, under a
fresh name, every unchanged theorem of the images' host files and the
changed books that names a changed function), loads the raw forms, checks
that no changed function is a raw-dispatch target and that every trap and
`:raw-with` declaration still holds, and saves the derived core into the
tree's `build/` beside an `.overlay.json` record (base set, source, plan
digest, applied forms).  A stripped image (production, dtn) takes only a
raw-only plan; under an ACL2 change it is refused, and so is every module
that reads it.  About 20 seconds of overlay, then the modules; the image
cycle it replaces is 25 to 70 minutes on hbox (`planning/loops-2026-10-04.md`).

A pass shows the behaviour of REV's host over SHA's certified world on that
run.  It is a lane's verdict, not an image: the integrator's image cycle
(certify, host-ld, the four builds) is what a release or a claim names.
Overlay cores are not timing-identical to built ones: a re-saved
production core lost `tests.test_native_state_checkpoint`'s running-owner
compaction race (stop right after the request) 3 of 3 where the published
core won it 3 of 3, and both pass with a pause before the stop; a red that
depends on timing is confirmed on a built image.

A live owner for exploration: `python3 tools/native_overlay.py live --image
build/fn-host-developer --root DIR` (on the box, in the run's tree) starts a
developer owner on a scratch store with its developer REPL and prints the
NNTP port and the socket; `python3 tools/fn_dev.py repl --socket DIR/dev.sock`
attaches (`:load` a raw file, `:acl2-file` events), `native_overlay.py stop
--root DIR` ends it.  A definition loaded into a running owner does not
re-run what already ran (startup, threads holding closures); for a verdict,
build the overlay again and restart.

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

`run` prints the `hbox_native.sh` command it starts and, for a tier's kits,
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
skipping a step whose recorded inputs are unchanged since its last verdict: a
pass is replayed as a pass, a red (exit 1) as the same red, naming the run,
box and log that produced it; a NOT RUN, a signal or a missing program is
never cached (`make check FORCE=1` runs every step).  Tree files are keyed by
relative path, so `FN_VERDICT_STORE=DIR` lets every worktree on a box share
one store; a cached verdict satisfies no READY and no batch gate, which are
live runs.  It needs no image; a step that needs ACL2 or
certificates it cannot find says NOT RUN and counts as failed.  `make check-lane`
is the same in a scratch directory; `tools/remote_check.sh auto` runs it on a
build box.

**The red set and one iteration.**  `python3 tools/reds.py collect` writes
`build/reds.json`: every known red (a red check step from the last
`execute`, a `FAIL`/`ERROR` case from native module logs named with
`--native`, a `real` red of a certify run named with `--certify`) with an
impact selector, the paths whose change could flip it (the step's traced
inputs, the module and the paths it names, the book's include closure).
`reds.py affected --since REV` prints the reds a diff reaches with why and
the narrowest command for each; `reds.py delta OLD NEW` the reds that
appeared and the ones fixed.  `python3 tools/iterate.py --since REV [--fast]`
is the lane loop: the scoped check-lane (unreached verdicts replayed from
the store), then the collection, the delta against the previous red set and
the reds of other kinds the diff reaches, each with its command, printed and
never started (overlays run on a build box through the integrator, certifies
through the farm).  Neither is a gate; `FORCE=1` and a READY stay live runs.

**Scoped and baselined runs.**  `make check-lane CHECK_CHANGED_SINCE=<rev>` (or
`tools/remote_check.sh BOX --changed-since <rev>`) runs only the steps the diff
from `<rev>` (committed, uncommitted and untracked files) can reach: the steps
whose last traced run, passing or failing, read, stat'ed or listed a changed
path, ran a git command the change can move, or could not be traced (ACL2, a
shell child).  The rest print `skipped`, with the store's last verdict beside it when that was red (`last verdict exit 1: ...`; the row's own exit stays 0); a docs-only diff skips host_check,
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
