# Lane migration-removal (wave 5 lane 6, D34), 2026-09-26

D34 (fresh deploys, no migrations) confirmed by ember 2026-09-26 ~18:40 UTC.
Base dev 91c59dabb. Ids: PRF-205, STO-028, HST-014, SCN-132, SCN-133, PKT-587.

## What now holds

- The store has one format (`fn-store-8`). `fn-spo-config-open`
  (books/store-profile-open.lisp; host: host/native/io.lisp
  `fnn-metadata-config-decode` through host/store-host.lisp
  `fn-store-metadata-config-open`, every open) answers `(:refused :store-format)`
  for a sealed profile frame of any other format; keystone
  `fn-spo-config-open-store-format-is-exactly-a-foreign-frame` (iff: outside the
  window, not decoded, a foreign format word). JSON metadata is refused with the
  same ACL2 line (`fnn-load-config`). Nothing is translated.
- `store export DIR` / `store import DIR [--FIELD N ...]` (books/store-export.lisp,
  prefix fn-sxp-). Keystone PRF-205 `fn-sxp-import-of-export-replays-the-same-history`:
  for a valid profile, records in strictly increasing sequence and configuration
  names in order, the import plan over the archive the export renders (entries and
  MANIFEST ACL2's) with no field raised is `(:import VALUES FRONTIER CONFIGS RECORDS)`.
  Host subjects: `fnn-command-store-export` (fn-sxp-entries, fn-sxp-manifest),
  `fnn-command-store-import` (fn-sxp-import-plan).
- Assurance chain: native entry `fnn-command-store-import` -> ACL2 subject
  `fn-sxp-import-plan` -> files written as init writes its files -> maintained
  relation established by the ordinary open entry (`fnn-open-live-store` ->
  `fnn-recover`, full replay `fn-store-sn-recover`, marker catch-up) -> behavioural
  theorem PRF-205 (same records, same order, same profile) -> observed result
  tests.test_native_store_export (NOT RUN in this lane; the batch's).
- DEVIATION from the brief, stated: the import does not run the publish program
  per record. `fnn-publish` commits a transaction the owner prepared in-process; an
  archived record is replayed, not prepared. The import writes the plan's files
  into ROOT.import-XXXX, admits them by the ordinary open, and renames the
  directory onto ROOT only after that open admitted it (an interrupted import
  leaves no store at ROOT). No new program is modelled for the import's file
  writes: they are the init's initial-file shape without its cut names; this is an
  open item for transcribe_check (the import has no process-death cut in the
  model because a death leaves only the staged directory, never a store).
- The MANIFEST is a transport check under the abstract digest seam (fn-digest,
  SHA-256 under crypto-attach); it proves nothing about an adversary.

## Deletion map (design 4.7, first row)

| Removed | Covered before by | Now |
| --- | --- | --- |
| format-7 tuples, `fn-bs-meta-format-7-valuesp`, `fn-bs-profile-from-format-7`, the decoder's format-7 arm | byte-store-frame-tests, store-profile-upgrade-tests (format 7 to 8) | the open refuses by name (fn-spo-config-open, SCN-132); presets keep their values (store-profile-facts-tests) |
| `upgrade-profile` and its relation (`fn-profile-upgradep`, `fn-profile-upgrade-verdict`, keeps-* keystones, PRF-072) | test_native_profile_upgrade, store-profile-upgrade-tests | a reinstall plus `store import --FIELD N` (PRF-205, SCN-133) |
| `repair-profile` (`fn-spo-repair-verdict`, PKT-471's repair) | test_native_control_reply_fit's repair rows | the window refusal names the reinstall and import |
| `needs-upgrade` (`fn-profile-needs-upgrade-verdict`) | test_native_operator_verdicts | nothing to decide: one format |
| `rollback-check KEPT` (`fn-profile-rollback-verdict`) | test_native_history_required MigrationTests, operator_verdicts | no store rollback exists (HST-014) |
| `rollback-check --snapshot` (`fn-native-operator-history-*`, PRF-141) | test_native_rollback_history | the archive is the kept copy; import refuses a tampered one by name |
| P-PROFILE (`fn-bs-profile-program`, PROFILE_CUTS, FN_NATIVE_PROFILE_FAULT, K0 profile arms) | profile cut tests, k0-step-bridge-root-tests | no profile write after init |
| `:migrate` step, `fn-hmr-upgrade-verdict`, two-step keystones | store-history-required-tests, MigrationTests | `fn-hmr-step-keeps-the-profile`; `required` birth is PKT-587 |
| packaging/upgrade-native.sh, releases/REV + current | tests/test_frozen_image_upgrade.sh (deleted) | install-native.sh's one libexec/fn/ (unchanged: it never versioned) |
| docs "Upgrade, and what a rollback loses" | docs_check | "Deploy a new release (D34)" |
| test_native_stamp_migration, test_native_newnews_migration | themselves | reinstall and import |
| dependents' upgrade-monotonicity theorems (maintenance reserve, capacity vector, compaction preservation, article verdict, namespace counts) | their test books | the profile is written once |

## PKT-587 (for ember): how is a store born `required`?

Trace: D31's `required` became durable only through `store upgrade-profile
--history-marker required` (the two-step). D34 removed that verb, and `init`
refuses `required` because it writes no marker. Today every store is born
`unmarked`; the `required` arm of `fn-hmr-open-verdict` is
unreachable-in-composition. Default proposed: `init` (and `store import`) under
`required` write the covering marker of the empty history before the profile
frame (`fn-hmr-birth-marker`; `fn-hmr-birth-holds-the-invariant` is proved for
that birth), which adds the marker's five cuts to the init program and its model
(transcribe_check). Rejected: admitting an absent marker with zero records under
`required` (it would admit a store whose records and marker were both deleted).
Continues without it: everything; `required` is simply not offered. An import of a
`required` archive is refused by init's name.

## Validation

- persvati REPL (session mr1, ~/fn-gates/migration-removal-repl, chain from
  books/consumer-position with unchanged books skip-loaded): byte-store-frame,
  store-profile-facts, tests/acl2/store-profile-facts-tests, byte-store-profile-v1,
  store-profile-open, store-history-required, store-export admitted.
- The other changed books and test books: see LANEDUMP (a helper lane edited the
  test books; results recorded there).
- Not done here: the native module (tests.test_native_store_export), the format-7
  fixture registration under /tank/fn/scratch/fixtures/format-7-store, the
  300-article SCN-133 store (the module drives articles only).
