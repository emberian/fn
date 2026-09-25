# deploy-fixes, 2026-09-25

Three runtime defects the qualification of e747dbcc found
(`planning/evidence/qual-e747dbcc-2026-09-25.md` A3, A4, U1), fixed before
the next cut. No new PRF: the keystones join PRF-089 (live status) and
PRF-095 (operator verdicts).

## A3: `control list` printed no grant

**Cause.** Not the report and not the slot: `fn-cfg-authorities` is the
eighth slot and `fn-native-admin-query-report` selects it. The host chose
the report kind itself: `host/native/operator.lisp`
`fnn-operator-execute-admin` sent every accepted query plan to
`fnn-operator-status-once` with the literal kind `:peers`, so `control list`
printed the (empty) peer report, live and offline. The same-source rule was
broken by a host constant.

**Fix.** The status path gains the `:control` kind
(`books/native-live-status.lisp` `fn-nls-report`, FNLS kind code 5), and
ACL2 names the kind for a query plan: `fn-native-admin-result-report-kind`
(`books/native-admin.lisp`), which the host calls at
`host/native/operator.lisp:332` through `fn-native-admin-host-report-kind`.

**Theorems.**
- `fn-nls-report-of-query-kind-is-query-report` (KEYSTONE, PRF-089): for
  every plan, `(fn-nls-report (fn-native-admin-result-report-kind plan)
  profile s bytes cfg pins obs)` equals `(fn-native-admin-query-report plan
  (fn-cfg-value cfg))`. `fn-nls-report` is what both arms of
  `fnn-operator-status-once` render (live `fn-nls-live-report`, offline
  `fn-nls-offline-report`), so `control list` renders the authority rows.
- `fn-native-admin-control-report-empty-iff-no-rows` (supporting): the
  listing is empty exactly when there is no authority row.
- Teeth (`tests/acl2/native-live-status-tests.lisp`): a configuration with
  one grant (cancel over fn.mod.*) renders `grant <P> cancel fn.mod.*\n`
  under the plan's kind and nothing under `:peers` (the defect); `peer list`
  still names `:peers`; the kind code round-trips; `must-fail` of the
  equality at `:peers`. The keystone has no hypothesis to drop.

## A4: an ACL2 invariant-risk warning on the owner's stdout at the first POST

**Cause.** `host/owner-host.lisp` `fn-owner-subject-id-buffer` was a
`:program` wrapper around the guard-verified `fn-shb-subject-id`, whose
local `fn-shs` stobj is written by `fn-shs-w-set`. An unverified caller of a
stobj updater is invariant risk: ACL2 runs the call through the executable
counterparts and prints the warning to standard output.

**Fix.** `books/sha256-buffer.lisp` `fn-shb-subject-id-bounded`,
guard `t`, guard-verified (the length test is the old wrapper's), which
`host/native/io.lisp:987` `fnn-subject-id-buffer` calls directly through
`fnn-core`. The `:program` wrapper is removed; no `:program` function
reaches the digest's updaters. `fn-shb-subject-id-bounded-unfolds` is
by definition (not a registry event). `tests/test_build_lists_check.py`
drops the expected finding for the removed wrapper's name (host/native/io.lisp
is outside the `ld` closure that check reads).

## U1: rollback-check said sound over a dropped history-marker requirement

**Fix.** `fn-profile-rollback-verdict (old current lengths)` takes the
store's own profile; `fn-profile-rollback-drops-markerp` (current requires
the marker, old does not) answers `(:refused
:history-marker-required-dropped)` before any record is measured.
`host/native/io.lisp:2326` `fnn-command-rollback-check` passes the store's
config.json profile (`fnn-store-config`); the operator sees `rollback
refused history-marker-required-dropped`, exit 1.

**Theorems (PRF-095).**
- `fn-profile-rollback-sound-iff-records-within` (KEYSTONE, restated):
  `:sound` exactly when the kept profile is admitted, does not drop the
  requirement, and every length is within the older image's record bound.
- `fn-profile-rollback-keeps-a-required-marker` (KEYSTONE): current
  requires the marker and the verdict is `:sound` imply the kept profile
  requires it.
- Teeth (`tests/acl2/store-profile-upgrade-tests.lisp`): the kept format-7
  scale tuple over the scale preset marked required is refused by name, as
  is the unmarked scale preset; a required kept profile is sound; the
  marker refusal precedes an over-bound record; `must-fail` without the
  current requirement (the kept format-7 tuple over an unmarked store is
  sound and unmarked) and without the `:sound` verdict.
