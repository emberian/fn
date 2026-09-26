# native-harness-env (2026-09-26): hbox_native.sh sets what a module reads; SKIPPED is not OK

Lane `lane/native-harness-env` from dev d47d6b80; PKT-437 (2), PKT-374
(retired), PKT-490 (what remains). Tooling only: no book, no host code, no
test expectation changed.

## The trap

Seven lanes (keys-and-accounts-2, peer-feeds, multi-peer-relay,
served-path-scale, reader-2, carrier-bound-test, operator-daily-2) ran a
module through `tools/hbox_native.sh`, which set no `FN_NATIVE_HOST`,
`FN_RUN_HYBRID_E2E`, `FN_TEST_OPENSSL`, `FN_NATIVE_CONTACT_*`, ...; every
test skipped and run.log said `OK (skipped=N)`; operator-daily-2 set
`FN_NATIVE_HOST` to the developer launcher by hand and the production-only
selector case started owners that never exit.

## What changed

- `tools/native_env.py` (new): the table below and `plan`. A module reads a
  variable when its own source calls `os.environ.get("X"`, `os.environ["X"]`
  or `os.getenv("X"` (helpers it imports are not scanned). `plan --images
  LIST [--env N=V] MODULE...` prints each module's assignments, or refuses:
  `tests.test_native_hybrid_author reads FN_NATIVE_HOST: build the
  production image with --images developer,production` (exit 2). One rule
  for image names: `FN_NATIVE_HOST` is only ever the production image
  (build/fn-host); reads that fall back when unset (public_exposure, profile,
  key_statements for FN_NATIVE_HOST) are neither set nor refused, so the
  module keeps its default.
- `tools/hbox_native.sh`: runs `plan` before shipping (a refusal exits 2,
  nothing ships; `--dry-run` shows it and each module's `env ...`); each test
  step is `env ASSIGNMENTS systemd-run ... python3 tools/test_budget.py --one
  MODULE`; a `need MODULE VAR PATH` line per image checks the tree on the box
  before the first test (the `--no-build` case), finishing 2; run.log gives
  each module `OK (N ran, K skipped)`, `FAILED (...)` or `SKIPPED (N of N; no
  test executed)` with every skip's reason, then `== modules: A OK, B
  SKIPPED, C FAILED`; a SKIPPED module makes the status 4.
- `tools/test_budget.py`: skips counted per module (`executed`, `skips` with
  reasons; a setUpClass SkipTest counts as a skip of tests testsRun never
  counted); a module that executed no test is `SKIPPED (N of N)`, not passed;
  exit code is a sum of bits, 1 failures and 2 over budget unchanged, **4 a
  module executed no test**; `--allow-skipped` drops bit 4 (only `make test`'s
  `--discover`, where native modules lack their image on the laptop; the
  report and its SKIPPED count stay); `--verdict LOG` prints a `--one` log's
  verdict (0/1/4). The summary line reads `N modules, S s; P passed within
  budget, K SKIPPED (no test executed), O over budget; T tests skipped`.
- Opt-in flags set automatically: `FN_RUN_HYBRID_E2E=1`,
  `FN_RUN_CONSUMER_EXCHANGE=1` (both mean "against this run's image"). The
  others (clone, relocation, consumer E2/poll/inspect/bounds, reader index,
  topic local/metadata) need an image or input this script does not build, so
  they stay manual: `plan` prints a note naming each unset one for a
  requested module, and the cases they gate show as skips in run.log.
- Tests: tests/test_test_budget.py (all-skipped with a decorator skip and a
  setUpClass skip, partial skips, exit 4 and 5, `--allow-skipped`,
  `--verdict`); tests/test_hbox_native.py (the refusal by name through
  `--dry-run`, `--env` lifting it, per-module assignments, the `need` line
  before the test, and a guard: every `*_HOST` or `FN_RUN_*` a native module
  reads is classified in the table, which caught FN_T2B_NATIVE_DEVELOPER_HOST
  and FN_NATIVE_TOPIC_V1_HOST).

## The table (generated: `python3 tools/native_env.py table`)

Image/opt-in/input variables only; the test-internal fault-injection and
evidence variables the tests set for their children are omitted.

| variable | modules reading it | what hbox_native.sh gives it |
|---|---|---|
| FN_BUILD_OPENSSL_PREFIX | test_native_frozen_relocation | not set: the build-time OpenSSL for the relocation case |
| FN_DTN7_REPO | test_native_source_corpus_bp | not set: a dtn7-rs checkout |
| FN_INN_SRC | test_native_peer_pull | not set: an installed INN 2.7 tree |
| FN_NATIVE_BP_HOST | test_bp_contact_native, test_bp_receive_integrity_native, test_bp_service_native | image: dtn or dtn-developer (set when built; refused when not) |
| FN_NATIVE_BP_NODE_HOST | test_bp_node_native | not set: falls back to FN_NATIVE_DEVELOPER_HOST (the DTN developer image by --env) |
| FN_NATIVE_CONTACT_RECEIVER | test_bp_contact_relay_native | image: dtn or dtn-developer (set when built; refused when not) |
| FN_NATIVE_CONTACT_SENDER | test_bp_contact_relay_native | image: dtn or dtn-developer (set when built; refused when not) |
| FN_NATIVE_CRASH_HOST | test_native_crash_model, test_native_served_crash_model | image: developer (set when built; refused when not) |
| FN_NATIVE_DEVELOPER_HOST | test_bp_app_native, test_bp_fragment_node_native, test_bp_node_native, test_bp_obligation_native, test_fn_web_native, test_native_admin, test_native_checkpoint, test_native_consumer_e2, test_native_consumer_exchange, test_native_consumer_exchange_two_nodes, test_native_consumer_inspect, test_native_consumer_project_bounds, test_native_control, test_native_history_marker, test_native_image_profiles, test_native_initializer_fidelity, test_native_operator_verbs, test_native_owner, test_native_profile, test_native_protected_peering, test_native_public_exposure, test_native_recovery, test_native_served_differential, test_native_storage_codec, test_native_topic_local | image: developer (set when built; refused when not) |
| FN_NATIVE_DTN_DEVELOPER_HOST | test_native_app_journal, test_native_image_profiles | image: dtn-developer (set when built; refused when not) |
| FN_NATIVE_DTN_HOST | test_native_image_profiles, test_native_source_corpus_bp | image: dtn (set when built; refused when not) |
| FN_NATIVE_HOST | test_native_admin, test_native_auth, test_native_checkpoint, test_native_control, test_native_control_across_peers, test_native_control_filing, test_native_friends_accounts, test_native_friends_feed, test_native_frozen_relocation, test_native_hybrid_author, test_native_image_profiles, test_native_initializer_fidelity, test_native_key_statements, test_native_live_reconfiguration, test_native_operator_cli, test_native_operator_verbs, test_native_peer_pull, test_native_peering, test_native_pre_c1_open, test_native_profile, test_native_public_exposure, test_native_reader_index, test_native_recovery, test_native_source_corpus, test_native_source_corpus_bp, test_native_starttls, test_native_topic_metadata, test_native_visibility_join | image: production (set when built; refused when not); not set for test_native_key_statements, test_native_profile, test_native_public_exposure (own fallback) |
| FN_NATIVE_READER_HOST | test_bp_node_native | not set: falls back to FN_NATIVE_DEVELOPER_HOST |
| FN_NATIVE_SOURCE_ROOT | test_bp_fragment_node_native, test_bp_node_native | not set: defaults to the tree the module runs from |
| FN_NATIVE_TEST_ROOT | test_fn_web_native | set to $T: the shipped tree |
| FN_NATIVE_TOPIC_V1_HOST | test_native_topic_local | not set: a topic-v1 image (legacy topic cases) |
| FN_OLD_IMAGE | test_native_friends_accounts | not set: an older image (upgrade cases) |
| FN_OLD_NATIVE_HOST | test_native_operator_verdicts, test_native_outcome_algebra | not set: an older image (upgrade cases) |
| FN_OPENSSL | test_native_peer_invite | set to $FN_OPENSSL_PREFIX/bin/openssl: the toolchain's OpenSSL 3.5 |
| FN_PRE_T2_NATIVE_DEVELOPER_HOST | test_native_newnews_migration, test_native_stamp_migration | not set: a pre-T2 developer image (migration) |
| FN_RUN_CONSUMER_E2E | test_native_consumer_e2 | not set: opt-in for the consumer E2 gate |
| FN_RUN_CONSUMER_EXCHANGE | test_native_consumer_exchange, test_native_consumer_exchange_two_nodes | set to 1: opt-in: the consumer exchange against this run's image |
| FN_RUN_CONSUMER_INSPECT | test_native_consumer_inspect | not set: opt-in for consumer inspect |
| FN_RUN_CONSUMER_POLL_E2E | test_native_consumer_e2 | not set: opt-in; requires the ACL2-owned consumer poll command |
| FN_RUN_CONSUMER_PROJECT_BOUNDS | test_native_consumer_project_bounds | not set: opt-in for consumer project bounds |
| FN_RUN_HYBRID_E2E | test_native_control_filing, test_native_hybrid_author | set to 1: opt-in: the OpenSSL 3.5 saved-image gate |
| FN_RUN_NATIVE_CLONE | test_native_checkpoint | not set: opt-in for a combined E2/checkpoint developer image |
| FN_RUN_NATIVE_READER_INDEX | test_native_reader_index | not set: opt-in for the integrated reader-index gate |
| FN_RUN_RELOCATION_E2E | test_native_frozen_relocation | not set: opt-in; also needs FN_BUILD_OPENSSL_PREFIX (a second OpenSSL build) |
| FN_RUN_TOPIC_LOCAL_E2E | test_native_topic_local | not set: opt-in for a source-matched topic image |
| FN_RUN_TOPIC_METADATA_E2E | test_native_topic_metadata | not set: opt-in for the source-matched topic-metadata gate |
| FN_T2B_NATIVE_DEVELOPER_HOST | test_native_newnews_migration | not set: a T2b developer image (migration) |
| FN_T2_NATIVE_DEVELOPER_HOST | test_native_stamp_migration | not set: a T2 developer image (migration) |
| FN_TEST_OPENSSL | test_fn_web_native, test_native_auth, test_native_checkpoint, test_native_consumer_e2, test_native_consumer_exchange, test_native_consumer_exchange_two_nodes, test_native_control_across_peers, test_native_control_filing, test_native_frozen_relocation, test_native_hybrid_author, test_native_key_statements, test_native_peer_pull, test_native_source_corpus, test_native_source_corpus_bp, test_native_topic_metadata, test_native_visibility_join | set to $FN_OPENSSL_PREFIX/bin/openssl: the toolchain's OpenSSL 3.5 (ML-DSA-65) |

34 rows (`native_env.py table`); `readers()` scans tests/test_native_*.py and
tests/test_*_native.py.

## Runs

- Laptop: `python3 -m unittest tests.test_test_budget tests.test_hbox_native`
  19/19 OK; `make tooling-test` 30 modules passed, 0 SKIPPED; `make
  check-lane` exit 0 (at e9009399; docs/proofs.md's paragraph after it,
  `tools/docs_check.py --check` 0 failures).
- A local simulation of the box script (`--dry-run --no-build`, systemd-run
  and `need` stripped) over the laptop, which has no image: run.log read
  `tests.test_native_hybrid_author: SKIPPED (11 of 11; no test executed)`
  with the 11 reasons (`build/fn-host is required`), status 4; before this
  lane the same module reported `OK (skipped=11)` (carrier-bound-test).
- hbox, the one real run: `tools/hbox_native.sh --images developer,production
  e9009399 tests.test_native_hybrid_author`
  (/tank/fn/scratch/native-harness-env/native-e900939965f4): `OK (11 ran, 0
  skipped)`, status 0, no FN_NATIVE_HOST or FN_RUN_HYBRID_E2E by hand.
  SHA-256: test log faad07527a40b402061afcbc24480a70d59771d3c4e270f6620264efc3460e63,
  fn-host 5e132d82f34a9803340f4ed5249ed0e44293723021419e0d5f7abe52c97719fd,
  fn-host-developer 814cfcdae3c83c087a02970417529422ce0ef53e187eff17ece997716caa60f0.
- The default run (`HEAD tests.test_native_hybrid_author`, developer only)
  now exits 2 before shipping with the refusal sentence above.

Classification of the trap: harness (the environment the script gave a
module), not implementation. No assurance chain changed: no ACL2 subject,
refinement or behavioural theorem is involved; what changed is that a
native case whose antecedents were never exercised can no longer be read as
observed.

## Not done (PKT-490)

1. The opt-ins that need an image or input this script does not build stay
   manual (the table's "not set" rows); `plan` notes each unset one for a
   requested module and its gated cases show as skips. Which of them mean
   "this run's image" is a per-module check with a native run each.
2. `native_env` scans a module's own file, not helpers it imports
   (tests/native_differential.py writes FN_NATIVE_HOST for its children and
   reads FN_NATIVE_DEVELOPER_HOST, which the importing modules also read).
3. Options must precede REV: the brief's `hbox_native.sh HEAD MODULE
   --images ...` is refused as a bad module name (exit 2).
4. build/coordinator/BRIEF-COMMON.md (the coordinator's file) still says
   run.log prints "each module's OK/FAILED/skipped line"; it now reads OK /
   FAILED / SKIPPED (N of N) and a SKIPPED module makes the status 4.

## Continuation: the stderr pipe (hot-path-checker-2, PKT-505)

**The trap.** exposure-reply-size's record (§4, and the "Not done" list)
describes it. `start_owner` in tests/test_native_operator_verbs.py started
the owner with `stderr=subprocess.PIPE` and read the pipe only after the
owner stopped. The owner writes one log line per accepted POST while
holding its log mutex. After about 500 POSTs the 64 KiB pipe was full, the
logging thread blocked in pipe_write, and every later request waited: 512
transactions, then `health` fenced as owner-unanswering. Classification:
harness, not product. The product half, where a log sink that does not
drain wedges the owner, is PKT-508.

**Exposed modules.** Every module that starts an owner through this fixture
is exposed. Each either calls `start_owner` or borrows it:

- test_native_operator_verbs;
- test_native_bounds_join and test_native_bounds_blob (through
  ProfileUpgradeFixture);
- test_native_control_reply_fit;
- test_native_history_required;
- test_native_outcome_algebra;
- test_native_profile_namespace;
- test_native_profile_upgrade;
- test_native_state_checkpoint.

Only bounds_join's LargeReplyTests (2,003 POSTs) crossed the threshold, and
it drained stderr privately. The others post at most 130 articles, so for
them the trap was latent. test_native_consumer_profile already filed its
own owner's stderr. test_native_public_exposure starts its owner with
stderr in a file of its own, so it was never exposed; it ran as the
control. Outside this fixture, twelve modules keep a private `start_owner`
on an unread pipe. They are listed, not fixed, in PKT-504 (d).

**The fix, at the fixture (583cda60).** The fixture now starts the owner
through tests/native_process.py `start_filed(argv, log_path, ...)`:

- stdout stays a pipe, which the fixture reads for LISTENING;
- stderr goes to `owner-N.err` in the test's temporary directory;
- `process.stderr` is a read handle on that file, so every caller that
  reads `owner.stderr` after the owner stops still reads the whole log,
  exactly as it did from the pipe;
- `process.stderr_path` names the file;
- a failed start reports the last 8 KiB of the log.

No timeout or budget was raised. test_native_bounds_join drops its drain
thread and reads the log on stop.

tests/test_fixture_stderr.py runs with no image, in tooling-test. A
stand-in owner, run through the real `start_owner`:

- writes 1 MiB to stderr (about 2,000 POSTs' worth of log lines);
- announces LISTENING;
- writes 1 MiB more while "serving", then marks that it answered;
- exits 0 on SIGTERM.

The test asserts that it announces and answers, that the caller reads back
all 2 MiB, and that each owner a test starts has its own file. The control
runs the same stand-in with stderr on an unread pipe, as the old fixture
did. It never announces within 3 s, which shows the stand-in reproduces
the trap.

**Native (hbox, tools/hbox_native.sh --name hot-path-checker-2 --label
stderr --images developer,production 583cda60).** The images: developer
launcher `4e16e5ca...` (core `c93e2277...`), production `20a974c5...`
(core `562bc562...`). run.log SHA-256 `473ea3ce...`. The logs are in
planning/evidence/native-harness-env-2026-09-26-stderr/ with the box's
SHA256SUMS.

| module | result | log SHA-256 |
| --- | --- | --- |
| tests.test_native_bounds_join | OK (2 ran, 1 skipped: DeployRehearsal needs FN_FORMAT7_IMAGE). LargeReplyTests passed through the fixture's owner with no private drain: 3 large POSTs and 2,000 more, then a 3.95 MB OVER, owner exit 0 (29.6 s) | `53cbbccc...` |
| tests.test_native_public_exposure | OK (1 ran; the flood campaign, 55.0 s) | `c5f90b77...` |
| tests.test_native_operator_verbs | FAILED, 1 of 22. Every owner-starting case passed (the uncertain-outcome pair and the capacity cases). The failure is `test_peer_list_is_a_query_and_the_host_asks_acl2_which`, a source-text assertion that `fn-native-admin-query-report` calls `fn-native-admin-peer-report`. Since a50312ef (PKT-391) the book calls `fn-native-admin-peer-budget-report`. Classification: harness, a stale source-shape expectation on dev, not this fixture. It is left to its owner (PKT-504 (e)); the expected answer was not changed here | `7cf84cf4...` |

**PKT-490, the optional items.**

- **(2) done.** tools/native_env.py `reads` follows the tests/ modules a
  module imports, transitively, for image variables. An image read only
  through a helper is set when its image is built, and when it is not built
  it is noted, never refused: a helper may read it at import without the
  module starting that image. Opt-ins and fixed paths still count from the
  module's own file. tests/test_hbox_native.py
  `test_an_image_read_through_an_imported_helper_is_set_and_never_refused`
  covers it. bounds_join now gets `FN_NATIVE_HOST` without the hand-set
  variable exposure-reply-size needed. Across the 93 native modules, 20 now
  read at least one more variable. Those are the module lists that
  `plan --images developer,production` sets more of.
- **(3)** was done by tooling-velocity-2: options may follow REV.
- **(4)** is already true in BRIEF-COMMON, whose hbox paragraph describes
  OK/FAILED/SKIPPED and status 4.
- **(1) not taken.** Each of its opt-ins needs a native run of its own.
