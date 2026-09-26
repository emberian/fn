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
