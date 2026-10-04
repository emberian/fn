# Testing fn

One way to run each kind of test: the command, where it runs, what a pass
shows and what it does not.  The long account of validation by layer is
[tests/README.md](../tests/README.md); the scenario specifications are
[tests/scenarios/catalog.json](../tests/scenarios/catalog.json).

| kind | files | one test | where |
|---|---|---|---|
| ACL2 test book | `tests/acl2/*-tests.lisp` | `python3 tools/farm.py submit auto tests/acl2/NAME-tests` then `farm.py wait BOX RUN` | a farm box (persvati, hbox); the laptop only through `tools/acl2` |
| raw SBCL harness | `tests/native_*_raw.lisp` | `sbcl --script tests/native_NAME_raw.lisp`, or the module that names it | anywhere with the toolchain SBCL; `make check` |
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

A pass shows: each event holds in ACL2's logic, executed by ACL2's evaluator,
over the definitions at these bytes.  It does not show that the host calls
those definitions (`reach_check`), that the image's compiled code behaves the
same, or anything about I/O.  A test book about a function no host path calls
is deleted, not kept as coverage.

## Raw SBCL harnesses

`tests/native_*_raw.lisp` read host source (`host/native/*.lisp`) and the
ACL2 `defun`s it calls from their files, evaluate them in a plain SBCL, and
drive them with recording stubs for the I/O seams.  Each ends by printing a
line containing `PASS`.  Today a harness is run either by the test module
that names it (with the arguments or fixture directory it needs) or by a
one-line `tests/test_native_*_raw.sh` wrapper marked `# witness: raw`, which
`tests/test_native_raw_scripts.py` runs under the toolchain SBCL (`FN_SBCL`,
else the image's runtime, else `sbcl` on PATH).  `make check` runs both
through `tools/native_source_check.py`.

A pass shows: the host function, as written, takes the branch the harness
asserts for the inputs and seam answers it supplies.  It does not show the
image (a different build, other definitions loaded, the real seams), guard
conformance, or real I/O.  Where the harness answers `fnn-core` -- the host's
call into ACL2 -- with values it made up instead of the real ACL2 function,
it tests host plumbing only.

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

## What `make check` is

`make check` plans ~90 steps and `tools/check_steps.py` runs them in parallel,
skipping a step whose recorded inputs are unchanged since it last passed
(`make check FORCE=1` runs every step).  It needs no image; a step that needs ACL2 or
certificates it cannot find says NOT RUN and counts as failed.  `make check-lane`
is the same in a scratch directory; `tools/remote_check.sh auto` runs it on a
build box.
