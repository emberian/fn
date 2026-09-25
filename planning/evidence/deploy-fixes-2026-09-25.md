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

## Certification

| run | box | books | result | manifest |
|---|---|---|---|---|
| run-20260925T205559Z-2502 | persvati, 2 jobs, w25 | 32 (`--affected-by` the four changed books) | passed; `tests/acl2/store-profile-upgrade-tests` 18.3 s (a new must-fail opened the sound-iff rule into 1,098 subgoals) | `manifests/certify-20260925T205626Z-1190099.json` |
| run-20260925T205859Z-e8bb | persvati, 2 jobs | the test book after narrowing that must-fail's theory | passed, 1.27 s | `manifests/certify-20260925T205921Z-1217435.json` |
| run-20260925T210013Z-7328 | hbox, 2 jobs, w28 | the same 32, at commit `ba958541` | passed; slowest `books/native-admin` 9.2 s | `manifests/certify-20260925T210036Z-3850666.json` |

Every changed book is under 10 s at two jobs.

## Native cases (hbox)

The tree is `git archive ba958541` at `/tank/fn/scratch/deploy-fixes/tree`.
The developer and production images were built with `swarm-build`, using
`FN_OPENSSL_PREFIX` and `LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib`
([`dfx-build.sh`](deploy-fixes/dfx-build.sh)). Neither build log contains
`invariant-risk`. Image digests are in
[`images.sha256`](deploy-fixes/images.sha256): `fn-host.core` `6cccdf74…`,
`fn-host-developer.core` `606863ed…`. Tests ran under
`systemd-run --user -p MemoryMax=24G`.

| case | result | log SHA-256 |
|---|---|---|
| A3 `tests.test_native_control_authority` (failed on e747dbcc) | 1/1 ok; lists both grants, then one after revoke | `adcef266a288d61251ff1ac7777371969e1dac1b0b0917722ce0ca62cd719e8e` |
| A4 `test_native_control` `test_two_clients_sigterm_cleanup_and_restart`, `test_lost_reply_after_submission_is_uncertain_and_recovers` (the two the warning broke) | 2/2 ok; no log has `invariant-risk` | `12047a6506265bdef0b457d2d3914e28e9f1a2541d1d17bbcf07dfcf05fe27f1` |
| U1 `test_native_history_required` `MigrationTests.test_migrate_then_absence_and_loss_are_damage` (new assertions: the kept unmarked config is sound before `required` and refused by name after) | 1/1 ok | `72a0d8ec3a851084f78f00dcf2e9aa8ca522be9b1ebd799a451eec5c0359f2e9` |
| U1 on a `cp -a` of the qualification's migrated copy of the live store (format 8, `required`), production image | `rollback-check config.json.format-7` answers `rollback refused history-marker-required-dropped`, rc 1 (e747dbcc said `sound`). The store's own required config is `sound transactions=18`. Offline `control list` prints the rehearsal's grant | `763b63af6b0e9cee04c39ff9db380ce2cb18d921ec488b0bd6b0e448de0fa3c7` |

## Not done

- No full module requalification; the next cut's qualification owns that.
- The DTN images were not rebuilt. They load the same `host/native/io.lisp`
  and include `books/sha256-buffer`, so the A4 path is the same code.
- `make check` in this worktree reports only the generated ledger as stale.
  The deputy regenerates it on merge.
- The `control list` rows are rendered and not parsed back. The theorem
  equates the listing with the rendered authority rows. It does not
  establish a line-per-row reading.
