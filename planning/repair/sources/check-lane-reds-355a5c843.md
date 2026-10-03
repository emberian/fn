# check-lane reds at dev 355a5c843 (make check-lane on persvati, runner BM, 2026-10-02/03)

Full log: persvati:/tmp/bm-checklane.log and build/lanes/batch-bm/build/remote-check/persvati-check-lane.log.
Owner: SWEEP-GATES (first deliverable: check-lane green on dev). 33 red steps.

## Handled by runner BM (not SWEEP-GATES)
- host_check (world) + tests.test_host_check_world: host/native/owner-control-turn.lisp names 'fn-ats-uncertain-internal (books/allocation-turn-slots), not in the DTN world since BM 1 loads that file in build-dtn. Fix: one include in build-dtn.lisp + regen image-world-dtn, in BM's next host batch (with HOST-LIFECYCLE).
- main_last_check, test_roots_check, clock_unit_check: trivial, batch BM 3.
- evidence_size_check (commit map 13428 lines) and tests.test_build_lists_check (old-sha fixtures): t39 / reasoned exemption, rechecked after batch BM 2.

## REAL DEFECTS FIRST (as far as BM read them)
- resource_contract: M4 heap-open-nursery, M7 connection-budget, M9 cold-read-reservation, W3 owner-served-bound, W10 public-exposure, W11 consumer-wait: "RED at its digest" from certify-20261001T100041Z-2748639. NB the whole-tree run at 4aa332295 (certify-20261002T215642Z-961794) INSTALLED all six from the hbox cache at these digests, so they certify; what is missing is a committed manifest that certifies them at this digest. Probably a cite (farm --recertify-uncited on those six), not a proof repair -- confirm.
- native_source_check: tests.test_native_account_adoption_transport exits 5 under the source check (the account-adoption host chain is unwired by stage 0 / D46; the module may need to skip by name or be parked with its producer).
- owner_globals_check: host/recovery-source-host.lisp writes 3 owner globals (fn-owner-recovery-source, -next-ticket, -sized-pending) not in the baseline. STAGE-5B's carrier move needs to know.
- host_check tables: host/native/extent.lisp:56 *fnn-extent-cache-tokens* is an unsynchronized global hash table. BM read: every reader/writer (fnn-extent-cache-forget/-store, the reset at 76-84) says "Extent lock held", like its siblings that carry `; guarded-by: *fnn-extent-lock*`. Likely a missing declaration, not a race -- verify the reset path holds the lock.

## The rest (first error line each)
- check_scaffold (exit 1): WARN: ledger: export hygiene: books/owner-log.lisp:773: fn-olog-served-refusal-line-says-refused: accessor-equality: an enabled equality between two different o
- host_check (exit 2): host_check: NOT RUN host/native/build-dtn.lisp (its include-books and host lds, in order)
- host_loaded_check (exit 1): host_loaded_check: host/store-checkpoint-context-host.lisp: no build loads it (reach_check IMAGE_BUILDS/TEST_IMAGE_BUILDS): wire it into a build, move a test ha
- tests.test_host_loaded_check (exit 1): FAIL: test_the_tree_is_clean (tests.test_host_loaded_check.HostLoadedTests.test_the_tree_is_clean)
- witness_check (exit 1): witness_check: tests/test_native_payload_lifecycle_raw.sh: no scenario-catalog row cites it or a tests/*.lisp it drives
- tests.test_witness_check (exit 1): FAIL: test_the_tree_is_clean (tests.test_witness_check.WitnessTests.test_the_tree_is_clean)
- harness_check (exit 1): harness_check acl2-arity: 10 findings (22964 definitions, 5818 applications, 192 host_files, 735 python_strings, 423 undecidable_strings, 3 declared_fixtures)
- must_fail_check (exit 1): bare tests/acl2/bp-native-app-replay-bridge-tests.lisp:40: must-fail: its body's translation is not checked; use must-fail-checked (tools/must_fail_check.py --c
- payload_kind_check (exit 1): payload-kind: 12 findings; definitions reading payload 63, accepted sites 36, wire definitions 11, handle definitions 7, handle sinks 28
- depth_check (exit 1): depth_check: fn-native-operator-host-self-signed-refused (host/native-operator-host.lisp:389): a :program host-called entry (nothing the host establishes is che
- raw_depth_check (exit 1): raw_depth_check: fnn-mux-request-handshake (host/native/mux.lisp:807): a non-tail recursion in the raw host code (calls fnn-mux-handshake-refused fnn-mux-start-
- tests.test_raw_depth_check (exit 1): FAIL: test_the_tree_is_clean (tests.test_raw_depth_check.RawBaselineTests.test_the_tree_is_clean)
- list_codec_check (exit 1): list_codec_check: 93 host-called octet-list codec sites in 14 files (baseline 92)
- tests.test_list_codec_check (exit 1): FAIL: test_the_classes_name_the_row_and_the_baseline_only_shrinks (tests.test_list_codec_check.ClassTests.test_the_classes_name_the_row_and_the_baseline_only_sh
- host_defun_check (exit 1): defined twice: fnn-snapshot-job-source: host/native/snapshot-producer.lisp:7 and host/native/snapshot-producer.lisp:7
- tests.test_host_check_tables (exit 1): FAIL tests/fixtures/host-tables/refused.lisp:7 *fx-shared*: a global hash table that is neither :synchronized t nor declared `;; thread-confined: <reason>` or `
- spec_cite_check (exit 1): UNDEFINED fn-bs-view-is-an-admissible-image: specs/recovery-refinement.md:352 (no book, test book or host file defines it)
- keystone_emit (exit 1): tests/acl2/feed-connection-teeth-tests.lisp:269: fct-refused-login -> PRF-051 fn-fc-refused-login-closes-without-an-offer; subject fn-fc-step (host/owner-host.l
- coverage (exit 1): planning/families.json: HST-045 is filed under no family
- alphabet_check (exit 1): alphabet_check: books/config.lisp defines no fn-cfg-kind-code
- premise_audit (exit 1): premise_audit: NEW unestablished premise adt-pg-pokp (established off the host path): assumed by adt-pg-put-tree-is-put-field
- hot_path_check (exit 1): hot_path_check: 185 traversals of retained state on paths from 146 host entries (167 unexpected, 11 cold, 3 resumable, 0 output-proportional, 0 unresolved, 4 un
