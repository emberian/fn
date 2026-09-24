# Native test modules on the 1a9dd747 image pair

Every image-gated native test module that had not run on `1a9dd747`, run one
module at a time on hbox on 2026-09-24 between 14:48Z and 15:25Z. Source is the
gate's own tree (`1a9dd747855c2e23ddfd4d8357270ef8f75cebb8`), so the tests are
the ones the image was built with, not dev's. Logs, the runner and the
diagnostic scripts are in [`native-subsets-1a9dd747/`](native-subsets-1a9dd747/)
with [`SHA256SUMS`](native-subsets-1a9dd747/SHA256SUMS).

## Images and environment

The gate `/tank/fn/gates/qual-1a9dd747-20260924` was not written. Its source
tree was copied to `/tank/fn/scratch/native-subsets-1a9dd747/tree` (rsync,
excluding `build/fn-host*`), and that copy's `build/fn-host{,.core}` and
`build/fn-host-developer{,.core}` are symlinks to the gate's files. Tests ran
in the copy. `sha256sum -c build/freeze/image-pair.sha256` in the gate passed
after the runs:

| artifact | SHA-256 |
| --- | --- |
| `build/fn-host` | `60e14e2afe8703574a9d74d89dc632a6c030a668fa261a74d92dd7589bb686d9` |
| `build/fn-host.core` | `12ece6cc95f3c4bed7a5d0a1abcfa0e5ea25257855e3f5caed22007c9a7b2bdd` |
| `build/fn-host-developer` | `5d42db2d8929ba256677ecb3bdfe957edc54176e0f5a1492b24376aa21ae1d9d` |
| `build/fn-host-developer.core` | `9b38ba45ed4ce31ca1997e3e4165873203e09d8e41fa176eb3fedbfee95741d0` |
| runtime `/tank/fn/sbcl/bin/sbcl` (SBCL 2.6.8) | `b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` |

The runner is [`run.sh`](native-subsets-1a9dd747/run.sh). It exports:
`FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g`, `FN_CERT_CACHE=/tank/fn/certcache`,
`FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, `LD_LIBRARY_PATH=$FN_OPENSSL_PREFIX/lib`,
`FN_NATIVE_SOURCE_ROOT=<copy>`, `FN_NATIVE_HOST=<gate>/build/fn-host`,
`FN_NATIVE_DEVELOPER_HOST` and `FN_NATIVE_CRASH_HOST=<gate>/build/fn-host-developer`,
`FN_NATIVE_IMAGE_SOURCE_SHA=1a9dd747…`, the four launcher/core SHA-256 values
above as `FN_NATIVE_{,DEVELOPER_}{LAUNCHER,CORE}_SHA256`, and
`FN_NATIVE_RUNTIME_SHA256` from the runtime. Each module runs as
`timeout 3600 python3 -m unittest -v tests.<module>`, logged with its env
header and `# rc= wall=` footer. Most end-to-end modules also need an opt-in
flag, so a second pass (`.optin` logs) added `FN_RUN_TOPIC_LOCAL_E2E`,
`FN_RUN_TOPIC_METADATA_E2E`, `FN_RUN_HYBRID_E2E`, `FN_RUN_NATIVE_READER_INDEX`,
`FN_RUN_CONSUMER_INSPECT`, `FN_RUN_CONSUMER_PROJECT_BOUNDS`,
`FN_RUN_NATIVE_CLONE`, `FN_RUN_CONSUMER_E2E` and `FN_RUN_CONSUMER_POLL_E2E`, all set to `1`.
Every store the tests create is under `tempfile` (`/tmp/fn-native-*`), none of it in the tree.

**Correction to the image record.** [`native-cut-1a9dd747`](native-cut-1a9dd747-2026-09-24.md)
lists `tests.test_native_consumer_e2` as "PASS, 2 tests". The gate log
`build/freeze/consumer-e2.log` says `Ran 4 tests in 0.000s / OK (skipped=4)`:
all four skipped because `FN_RUN_CONSUMER_E2E` was unset. That run established
nothing. This record's `.optin` run is the first real one on this image.

## Results

The seconds column is wall time for the whole unittest process. For the static
structure tests the image does not matter; they run against the tree.

| module (log) | tests | passed | failed+err | skipped | seconds | log SHA-256 (first 16) |
| --- | --- | --- | --- | --- | --- | --- |
| test_native_admin | 9 | 9 | 0 | 0 | 3.6 | `0f07d3ea5ccc2094` |
| test_native_auth | 3 | 3 | 0 | 0 | 4.0 | `5dd40dca5c8e5424` |
| test_native_starttls | 2 | 2 | 0 | 0 | 0.6 | `2372d6788904f75d` |
| test_native_auth_admin_fidelity | 3 | 3 | 0 | 0 | 11.3 | `1e0d83f10e189018` |
| test_native_owner | 17 | 15 | 2 | 0 | 19.8 | `699884c25664ce67` |
| test_native_owner.NativeOwnerHandlerStructureTests (`.image-sbcl`) | 5 | 5 | 0 | 0 | 2.2 | `2cf76bba792b81cb` |
| test_native_raw_scripts (`.image-sbcl`) | 9 | 9 | 0 | 0 | 0.5 | `f84af0f18ac9e945` |
| test_native_live_reconfiguration | 11 | 11 | 0 | 0 | 1.4 | `68320024f00f4952` |
| test_native_control | 14 | 13 | 1 | 0 | 20.4 | `1631097b95f12d35` |
| test_native_operator_cli | 6 | 5 | 1 | 0 | 3.9 | `6561f487357c19ea` |
| test_native_operator_verbs | 13 | 11 | 2 | 0 | 2.1 | `fff95a8845b5a8db` |
| test_native_profile | 3 | 3 | 0 | 0 | 0.8 | `c4978601306802dc` |
| test_native_initializer_fidelity | 11 | 11 | 0 | 0 | 1.4 | `6785870cd22880c4` |
| test_native_recovery | 13 | 13 | 0 | 0 | 12.0 | `d52fda9672bc136f` |
| test_native_image_profiles | 12 | 9 | 0 | 3 | 0.8 | `890fe93860dce643` |
| test_native_storage_codec | 11 | 10 | 1 | 0 | 52.6 | `ad31193024a66ecb` |
| test_native_served_differential | 7 | 7 | 0 | 0 | 0.9 | `8f1854393182be3b` |
| test_native_reader_index (`.optin`) | 4 | 4 | 0 | 0 | 5.2 | `d3f502ed73193905` |
| test_native_newnews_migration | 1 | 0 | 0 | 1 | 0.0 | `0f173e5f9546b873` |
| test_native_stamp_migration | 1 | 0 | 0 | 1 | 0.0 | `24153fbe57f47328` |
| test_native_hybrid_author (`.optin`) | 4 | 3 | 1 | 0 | 51.8 | `89adf1a6ac7f8baf` |
| test_native_topic_local (`.optin`) | 4 | 2 | 0 | 2 | 2.6 | `b8a732d56945260d` |
| test_native_topic_metadata (`.optin`) | 2 | 2 | 0 | 0 | 1.2 | `b342a679ab76fd71` |
| test_native_consumer_inspect (`.optin`) | 4 | 4 | 0 | 0 | 0.5 | `d7066123e1aaf6f7` |
| test_native_consumer_project_bounds (`.optin`) | 2 | 2 | 0 | 0 | 0.2 | `c642218378c5038b` |
| test_native_consumer_e2 (`.optin`) | 4 | 2 | 1 | 1 | 3.1 | `c323c004e632cad7` |
| test_native_consumer_e2 signed poll (`.dated-source`) | 1 | 1 | 0 | 0 | 10.9 | `7e47e4ed60c58040` |
| test_native_checkpoint (`.optin`) | 23 | 23 | 0 | 0 | 40.1 | `a3404381e8fe0305` |
| test_checkpoint | 7 | 7 | 0 | 0 | 466.3 | `ae336149fcc9857f` |
| test_native_peering | 4 | 4 | 0 | 0 | 7.5 | `aff70cbd7c321184` |
| test_native_protected_peering | 5 | 5 | 0 | 0 | 26.4 | `d1725ad68eac8394` |
| test_native_crash_model | 6 | 6 | 0 | 0 | 41.2 | `02508ef9fb637a94` |
| test_native_served_crash_model | 2 | 2 | 0 | 0 | 58.4 | `2e3711d31bd403d2` |
| test_native_tls_transport | 2 | 2 | 0 | 0 | 0.8 | `b39497243d56264c` |
| test_native_frozen_relocation | 2 | 0 | 0 | 2 | 0.0 | `4b94098fae1897b6` |
| test_fn_web_native | 2 | 2 | 0 | 0 | 3.0 | `cb59d4ce586e9076` |
| test_bp_node_native (all 16, N03 again) | 16 | 12 | 4 | 0 | 298.4 | `be1172b594514ee0` |
| test_bp_app_native | 4 | 1 | 3 | 0 | 559.7 | `681082c79f0b5ad6` |
| test_bp_obligation_native | 4 | 4 | 0 | 0 | 1.0 | `daf3d508c2be2c00` |
| test_bp_service_native | class | 0 | 0 | class | 0.0 | `42d1cc686e89718b` |
| test_bp_contact_native | class | 0 | 0 | class | 0.0 | `ed14086c68d379d6` |
| test_bp_contact_relay_native | class | 0 | 0 | class | 0.0 | `224595902d581e98` |
| test_bp_receive_integrity_native | class | 0 | 0 | class | 0.0 | `86af26a596ec4842` |
| test_native_app_journal | class | 0 | 0 | class | 0.0 | `bb1ebf9cfef0b639` |

Full hashes, including the first-pass logs where the opt-in modules skipped
everything, are in `SHA256SUMS`.

**Skips, and what each one needs:**
- **No DTN image on this gate.** The stage-2 script built `fn-host` and
  `fn-host-developer` only, so there is no `build/fn-host-dtn` and no
  `fn-host-dtn-developer`. That skips `test_bp_service_native`,
  `test_bp_contact_native`, `test_bp_contact_relay_native`,
  `test_bp_receive_integrity_native`, `test_native_app_journal` and three
  `test_native_image_profiles` cases. P11's service-level outage, restart and
  duplicate cases (`test_outage_restart_duplicate_and_conflict`, the
  interrupted-contact cases the audit names) therefore have no evidence on
  1a9dd747.
- **Frozen pre-T2 developer images** (`test_native_newnews_migration`,
  `test_native_stamp_migration`) and the **exact pre-v2 topic image**
  (`test_native_topic_local` v1-history cases). None was available.
- **`test_native_frozen_relocation`** needs a relocated copy of a frozen
  image with `image.sha256` beside it and `FN_RUN_RELOCATION_E2E=1`. Not done.
- **`test_different_local_uid_is_refused_by_owner`** needs root and `setpriv`.

**Not run:** the campaign/matrix modules (`tests.campaign.*`,
`test_native_operator_campaign`, `test_native_v0_matrix`, `test_v0_matrix`)
and `test_native_shared_owner_bench`. `test_bp_fragment_node_native` was
already recorded. Static modules with no image gate were also left out
(`test_native_compaction_crash_map`, `_crash_correspondence`, `_cut_map`,
`_served_cost`, `_block_fault_ownership`, `_peering_matrix_slice`,
`_two_host_protected_gate`, and the `test_native_bp_*` raw wrappers). They
check source, not the image.

## Failures

Classes: (a) fn defect, (b) fixture/env, (c) the test is out of date with the machine or is itself wrong.

1. **test_native_owner:** `test_developer_selectors_gate_arm_the_owner_and_stop_synchronously`
   and `test_the_chunk_loop_keeps_its_suffix_and_reads_a_clock_per_step`
   fail with `1 != 0 : Unhandled SB-INT:SIMPLE-READER-PACKAGE-ERROR … Symbol
   "SOCKOPT-ERROR" not found in the SB-BSD-SOCKETS package` at
   `host/native/io.lisp:2251`. **(b)** The raw scripts run `sbcl` from
   `PATH`, which on hbox is Debian SBCL 2.2.9 (`/usr/bin/sbcl`). That
   version lacks the symbol; the image's runtime, SBCL 2.6.8, has it. With
   `PATH=/tank/fn/sbcl/bin:$PATH SBCL_HOME=/tank/fn/sbcl/lib/sbcl/`, all 5
   structure tests and all 9 `test_native_raw_scripts` cases pass
   (`.image-sbcl` logs).
2. **test_native_control:** `test_the_reply_is_the_owners_status` expects the
   text `(member (first status) '(:consumer-reply :consumer-poll-reply))`.
   The source is `host/native/control.lisp:344-345`, and its list now starts
   with `:topic-reply`. **(c)**
3. **test_native_operator_cli:** `test_operator_calls_existing_acl2_credential_plan_and_executor`
   expects `(fn-native-auth-admin-parse-argv (cdr argv))`. The book says
   `(fn-ncfg-rest argv)` (`books/native-operator.lisp:167`). **(c)**
4. **test_native_operator_verbs:** `test_init_creates_the_configured_store_and_then_refuses_it`
   asserts `b"refused operator init STORE-EXISTS" in stderr.upper()`. That
   can never hold, because the literal is lower case and the stderr has been
   upper-cased. The actual stderr, `refused operator init STORE-EXISTS`, is
   the right refusal. **(c)**, a test defect.
5. **test_native_operator_verbs:** `test_init_without_a_group_is_usage_and_writes_nothing`
   fails with `0 != 5 : accepted operator init`. **`operator CONFIG init "Not A
   Group"` is accepted.** **(a)** The owner is ACL2:
   `fn-record-group-namep` (`books/records-shape.lisp:100`) accepts any
   non-empty ASCII string within the length bound, and
   `fn-nop-parse-init-groups` (`books/native-operator.lisp:110-123`) plans on
   it. A newsgroup name with spaces is outside RFC 5536 §3.1.4's
   `newsgroup-name` grammar, so init stores a group that NNTP cannot name.
   The bare-`init` sub-case passed; the duplicate-group sub-case was not
   reached.
6. **test_native_storage_codec:** `test_native_and_python_cross_open_identical_acl2_frames`
   fails at line 134: transaction 0 differs between the native-written and
   Python-written stores. **(c)** The diagnostic
   [`codec_diag.py`](native-subsets-1a9dd747/codec_diag.py) shows two
   356-octet frames that first differ at octet 323. At that point each has a
   CBOR `1a` uint32 (`3247f5ba` versus `3247f5b7`, three seconds apart),
   followed by a different 32-octet trailer. The frame now carries an
   acceptance stamp, and two posts made seconds apart cannot be byte-identical.
   The cross-open halves of the test (each runtime reads the other's store)
   passed before that assertion.
7. **test_native_consumer_e2 (`.optin`):** `test_signed_composite_poll_and_lost_positive_ack_reply`
   fails at line 298: `hybrid-author` exits 1 with **empty stderr**. **(c)**
   The test's default source article has no `Date:` header. With
   `FN_CONSUMER_POLL_SOURCE_FILE` pointing at the same article plus a Date
   ([`poll-source-dated.eml`](native-subsets-1a9dd747/poll-source-dated.eml)),
   the case passes (`.dated-source` log, 10.9 s): signed composite poll,
   lost positive ACK reply, cold reopen. Separately, a refusal with exit 1
   and no reason on stderr is the P2 W3 pattern at the control surface.
8. **test_native_hybrid_author (`.optin`):** `test_authored_carrier_survives_native_peering_and_receiver_restart`
   fails with `native feed did not deliver authored article` after 45 s.
   **(a), unisolated.** In the diagnostic
   ([`hyb_diag.py`](native-subsets-1a9dd747/hyb_diag.py), receiver stderr
   [`hyb_diag-receiver.stderr`](native-subsets-1a9dd747/hyb_diag-receiver.stderr)),
   the source node opened **437 peer connections in 45 s** to the receiver
   (`accepted peer connection=0` to `=436`, about 10 per second). The article
   never arrived, and neither owner wrote any other stderr line. The
   unauthored feed works on this image (`test_native_peering`,
   `test_native_protected_peering`), so the problem is specific to the
   authored carrier. There are two faults: the feed retries with no backoff,
   and it never says why the transfer failed. No host line is named. The
   next step is the source's feed journal.
9. **test_bp_node_native:** `test_ambiguous_fnrj_decision_fences_until_cold_replay`,
   `test_death_after_fnrj_receipt_decision_replays_one_article` and
   `test_request_retry_queues_distinct_receipt_carriers_and_releases_pin`
   fail on restart with `4 != 0 : b'store: ACL2 returned a non-natural'`.
   **(a)**, inferred from source and not traced. Each case restarts after
   FNRJ has already committed or decided the request.
   `fn-owner-app-plan-install`'s `(:committed :context :pending-receipt)`
   branch (`host/bp-native-app-host.lisp:122-127`) sets
   `fn-owner-app-generation` but not `fn-owner-app-txid`, and returns
   `:ready`. `fnn-bpapp-accept-locked` then does
   `(fnn-nat (fnn-global 'fn-owner-app-txid))` (`host/native/bp-app.lisp:97`).
   In a fresh process that value is `nil`, which faults at
   `host/native/io.lisp:623`. dev `24aa1b9c` has the same code at both sites.
   These cases are P11's restart-after-receipt-decision rows, and they exit 4
   instead of replaying.
10. **test_bp_node_native:** `test_older_mru_wait_allows_younger_forward_and_replays`
    fails with `6 != 7` at line 382. **(c), probable.** The test expects
    dispatch to add four lifecycle records ("two kind-6, then kind-8 and
    kind-9"); dispatch added three. [`mru_diag.out`](native-subsets-1a9dd747/mru_diag.out)
    lists the receiver's `lifecycle/` directory. Before dispatch it holds
    kinds 5, 6, 5 (`1-0`, `1-1`, `1-2`); dispatch adds kinds 6, 8, 9. One
    kind-6 was already durable from the receive phase. Forwarding itself
    completed ("BP forwarding attempt durable", segments sent). The BP lane
    decides whether receive-time kind-6 is intended.
11. **test_bp_app_native:** three cases fail.
    - `test_application_receipt_releases_forward_pin_only_after_durable_record`
      and `test_visible_decision_namespace_eio_fences_before_receipt` error
      with `TimeoutExpired` on `bp send` after 180 s.
    - `test_lost_receipt_restart_replays_without_second_acceptance` never
      sees `BP APP DECISION DURABLE`.

    **(c), probable, plus one behaviour finding.** In the diagnostic
    ([`bpapp_diag.out`](native-subsets-1a9dd747/bpapp_diag.out)) the
    receiver logs `BP application refused xfer=0` and `TCPCL bp-app refused
    inbound xfer=0 reason=REFUSED`, with no refusal reason. The fixture adds
    no `bp-boundary` trust entry and no path identity, which the fragment
    fixture had to gain for the same image line. The sender then logs
    `TCPCL active refused outbound xfer=0 reason=4`, **stays in the session
    sending KEEPALIVE and never exits**. A one-shot `bp send` whose only
    transfer was refused does not terminate. That is a finding for P11's
    retry policy (ember's open decision), not a test defect.

## P1 to P11: modules that observe each property on 1a9dd747

| P | modules and result |
| --- | --- |
| P1 | `test_native_auth` 3/3, `test_native_starttls` 2/2, `test_native_auth_admin_fidelity` 3/3, `test_native_protected_peering` 5/5 (reciprocal STARTTLS+AUTHINFO, bad password gives an authenticated 430, untrusted certificate gives 430 with feed-journal evidence), `test_native_tls_transport` 2/2 |
| P2 | `test_native_crash_model` 6/6, `test_native_served_crash_model` 2/2, `test_native_owner` post/uncertain/fence cases pass; `test_native_storage_codec` 10/11 (failure 6, (c)) |
| P3 | `test_native_reader_index` 4/4 (historical pin across restart, OVER/XOVER, LISTGROUP), `test_native_served_differential` 7/7; NEWNEWS/stamp migration skipped (no pre-T2 image) |
| P4 | `test_native_peering` duplicate offer 435 both ways; `test_native_owner` `empty_v1_feed_namespace_is_preserved_as_conflicting_evidence` pass; `test_native_checkpoint` `surviving_covered_transaction_conflict_fails_closed` pass; no native module separates duplicate from conflict for POST on the wire |
| P5 | `test_native_owner` `local_handler_fault_uses_core_fault_and_preserves_other_clients`, `client_disconnect_is_not_a_global_owner_fault`, `reset_peer_does_not_stop_concurrent_writer_or_reader` pass; `test_native_control` `control_worker_ceiling_returns_busy` pass |
| P6 | `test_native_live_reconfiguration` 11/11, `test_native_admin` 9/9, `test_native_initializer_fidelity` 11/11, `test_native_profile` 3/3, `test_native_operator_verbs` 11/13 (failure 4 (c); failure 5 (a): init accepts `Not A Group`), `test_native_control` 13/14 (c), `test_native_operator_cli` 5/6 (c) |
| P7 | `test_native_peering` 4/4 (both ways, requeue after source death, reset during transit), `test_native_protected_peering` 5/5; `test_native_hybrid_author` authored-carrier peering FAILS (failure 8: 437 reconnects, no delivery) |
| P8 | `test_native_hybrid_author` 3/4 (enroll/refuse-tamper/restart query, portable verification, local revocation pass; peering fails); `test_native_consumer_e2` signed composite poll passes only with a dated source (failure 7) |
| P9 | `test_native_admin` `create_capacity_retire_reopen_preserves_history` pass; `test_bp_obligation_native` 4/4 incl. `shared_owner_capacity_refusal_publishes_nothing`; `test_native_app_journal` forwarding-capacity case skipped (no DTN image) |
| P10 | `test_native_crash_model` 6/6, `test_native_served_crash_model` 2/2, `test_native_checkpoint` 23/23 (process death at every checkpoint and selection cut), `test_checkpoint` 7/7, `test_native_recovery` 13/13 |
| P11 | `test_bp_node_native` 12/16 (failure 9 (a) ×3: restart after FNRJ commit exits 4; failure 10 (c)); `test_bp_app_native` 1/4 (failure 11); `test_bp_obligation_native` 4/4; service/contact/relay/receive-integrity skipped (no DTN image) |

Capabilities:
- **Topic v2:** `test_native_topic_local` 2 pass, 2 skipped (pre-v2 image); `test_native_topic_metadata` 2/2.
- **Author lifecycle:** `test_native_hybrid_author` enroll/revoke 3/4.
- **Pack retirement and active reader:** `test_native_checkpoint` 23/23, including `retiring_old_pack_generations_keeps_exact_retained_sources`, `pack_generation_retirement_death_reopens_and_retries` and the three clone cases.
- **Checkpoint:** `test_checkpoint` 7/7.
- **Consumer:** `test_native_consumer_inspect` 4/4, `test_native_consumer_project_bounds` 2/2, `test_native_consumer_e2` 2 pass + dated-source 1 pass.
- **ION observer:** not covered by any module run here.

## What this does not establish

These are selected tests on one developer/production image pair, not a suite
and not the deployed node (`da5fd8cb`). Three kinds of case have no evidence
on 1a9dd747:
- the DTN-image cases;
- the migration cases that need older frozen images;
- relocation.

The classifications in failures 8 to 11 rest on the diagnostics named. Nothing
was traced inside the image, so failure 9's cause is a source reading, and
failure 8 has no named cause.
