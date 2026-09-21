# Handoff: w12/artifact-set

Branch `w12/artifact-set`, based on `8b474e2`.  Evidence:
[`artifact-set-w12-2026-09-21.md`](../evidence/artifact-set-w12-2026-09-21.md).

## What changed

`tools/certs.py` now has a set-level selector.  The source identity is the
digest of the requested roots' complete local include union.  Candidates are
grouped by absolute origin and certification toolchain; the selector installs
one complete group or nothing.  Published entries retain the ACL2 version,
executable digest, certification environment and runner/reader digests from
the certification manifest.

`tools/proof_artifacts.py` declares the two native profiles.  `default` is
`host/native/build.lisp` -> `build/fn-host`; `dtn` is
`host/native/build-dtn.lisp` -> `build/fn-host-dtn`.  It derives each
profile's roots from the session script, its loaded host files, and the
deployed `host/owner-host.lisp` entry point.  An owner root newly included by
the shipped source therefore joins the same set without a hardcoded book
list.  The helper installs candidate sets one at a time, actually loads the
declared roots in ACL2, and rejects a whole set on an ACL2 error,
absolute-origin conflict, missing ready marker or uncertified warning.

The deployment gate uses that acquisition instead of the newest neighbouring
gate.  On a miss it certifies only the selected profile closure and load-checks
it.  `V0Matrix` and `InnLab` no longer run a second per-book installer after
that decision.  The deployment directory and lock are both keyed by
`<tree>-<revision>`, so equal revisions under different `--tree` values do
not share a remove target or lock.

## Evidence and scope

The hbox run certified the default native image's 89-book closure and the
owner entry point's 78-book closure with four jobs.  Their union was one
96-book origin/toolchain set; ACL2 loaded its 23 declared roots.  The declared
default image then built with no error or uncertified marker.  The DTN-only
image was deliberately not substituted for it.  The evidence file holds the
exact commands and digests; both certification manifests are archived beside
the other project manifests.

The 97-test local integration suite covers the incompatible two-origin reproducer, no
partial install on rejection, toolchain separation, retry after a real load
failure, explicit default/DTN declarations, deployment path/lock identity,
and the deploy/two-node/INN dry runs.  It passed, as did `make check`; the
latter remained a structural check and skipped its real ACL2 host load because
`FN_ACL2` was unset locally.
