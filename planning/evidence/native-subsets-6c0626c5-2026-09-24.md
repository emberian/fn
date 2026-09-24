# Native test modules on the 6c0626c5 images

Every image-gated native module, run one module at a time on hbox on
2026-09-24 between 15:46Z and 16:05Z against the four `6c0626c5` images,
including the DTN pair that the `1a9dd747` gate did not have. Every opt-in flag
was set from the start, and the image's SBCL was first on `PATH`. The previous
run is [native-subsets-1a9dd747](native-subsets-1a9dd747-2026-09-24.md). Logs,
the runner and the diagnostics are in
[`native-subsets-6c0626c5/`](native-subsets-6c0626c5/), with
[`SHA256SUMS`](native-subsets-6c0626c5/SHA256SUMS).

## Images and environment

- **Gate:** `/tank/fn/gates/qual-6c0626c5-20260924` was only read, not written.
  Its tree was rsynced without `build/` to
  `/tank/fn/scratch/native-subsets-6c0626c5/tree`. That copy's `build/` holds
  symlinks to the frozen image directory
  `<gate>/build/images/6c0626c5/`: all four launchers and cores, plus
  `runtime`, `lib`, `openssl` and `image.sha256`.
- **Checksums:** `sha256sum -c image.sha256` in the image directory passed
  before and after the runs. `sha256sum -c build-source.sha256` passed on the
  gate and on the copy. The copy's `tests/`, `tools/` and `host/` match
  `git archive 6c0626c5` file by file (652 files), and dev `c60bb371` has no
  diff under `tests/ host/ books/` against `6c0626c5`.

| image | launcher SHA-256 | core SHA-256 |
| --- | --- | --- |
| `fn-host` | `432622d29a28d594…` | `99cee8c066aec7ad…` |
| `fn-host-developer` | `e4eeefd290450e74…` | `f9ba0c633b5e3fe6…` |
| `fn-host-dtn` | `095382bae2b3ff37…` | `10d22ba7550d5cfd…` |
| `fn-host-dtn-developer` | `4986f14bf4ebc34f…` | `400c1d78c0c4ea74…` |
| `runtime/sbcl` (SBCL 2.6.8) | `b115fe956aadee60…` | |

The runner is [`run.sh`](native-subsets-6c0626c5/run.sh). It exports the
same variables as the 1a9dd747 runner, with these changes:
- `FN_NATIVE_{HOST,DEVELOPER_HOST,CRASH_HOST}` point at the frozen
  launchers. The four SHA-256 variables are read from `image.sha256`, and
  `FN_NATIVE_IMAGE_SOURCE_SHA` is the full `6c0626c5ad56…`.
- **DTN variables.** `FN_NATIVE_DTN_HOST` and `FN_NATIVE_DTN_DEVELOPER_HOST`
  are read by `test_native_image_profiles` and `test_native_app_journal`.
  `FN_NATIVE_BP_HOST` is read by `test_bp_service_native`,
  `test_bp_contact_native` and `test_bp_receive_integrity_native`, and
  defaults to `fn-host-dtn`; `NS_BP_IMAGE` overrides it.
  `FN_NATIVE_CONTACT_SENDER` and `FN_NATIVE_CONTACT_RECEIVER` are read by
  `test_bp_contact_relay_native`.
- **The image's SBCL.** `PATH` starts with `$S/bin`, where `sbcl` links to
  `<image>/runtime/sbcl`, and `SBCL_HOME=<image>/runtime/sbcl-home/`. This
  removes the 1a9dd747 Debian-SBCL-2.2.9 trap.
- **Opt-in flags.** These are all set to `1`: `FN_RUN_TOPIC_LOCAL_E2E`,
  `_TOPIC_METADATA_E2E`, `_HYBRID_E2E`, `_NATIVE_READER_INDEX`,
  `_CONSUMER_INSPECT`, `_CONSUMER_PROJECT_BOUNDS`, `_NATIVE_CLONE`,
  `_CONSUMER_E2E` and `_CONSUMER_POLL_E2E`.

Each module runs as `timeout 3600 python3 -m unittest -v tests.<module>` in
two sequential chains, one for BP/DTN modules and one for everything else.
Every port is ephemeral, and every store lives under `/tmp`.
`FN_RUN_RELOCATION_E2E` ran separately; see below.

**Runner incident.** `run.sh` was edited in place (the `NS_BP_IMAGE` line)
while both chains were reading it. After each chain's loop finished, `sh`
re-read the file at a stale offset. That printed one duplicate summary line
and a `Syntax error: "done" unexpected`, but ran nothing. All module logs are
complete; each has its `# rc= wall=` footer.

## Results

Wall seconds cover the whole unittest process. The last column compares with
the 1a9dd747 run.

| module (log) | tests | pass | fail+err | skip | s | log SHA-256 (16) | vs 1a9dd747 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| test_native_auth | 4 | 4 | 0 | 0 | 6.9 | `6587fb4bd61dffeb` | +1: P1 480-before-login case, new, passes |
| test_native_profile | 3 | 3 | 0 | 0 | 0.9 | `b5ba4d1a6a5eae0f` | same |
| test_native_admin | 9 | 9 | 0 | 0 | 7.7 | `7c178d2bdf95b373` | same |
| test_native_starttls | 2 | 2 | 0 | 0 | 1.5 | `316d1548dd39e5e3` | same |
| test_native_auth_admin_fidelity | 3 | 3 | 0 | 0 | 18.1 | `6220abc04b2eb3ea` | same |
| test_native_owner | 18 | 18 | 0 | 0 | 28.7 | `32229fb266ca3c06` | **newly all pass** (was 15/17; the image's SBCL is on PATH; one new case) |
| test_native_raw_scripts | 9 | 8 | 1 | 0 | 0.8 | `6646769678dfc678` | **newly fails** 1 (failure 3, (c)) |
| test_native_live_reconfiguration | 11 | 11 | 0 | 0 | 1.9 | `2d735b1c3365d96d` | same count; first image carrying `fn-ocl-publish` |
| test_native_control | 14 | 13 | 1 | 0 | 22.3 | `489c44e644f481c6` | same (c) |
| test_native_operator_cli | 6 | 5 | 1 | 0 | 4.2 | `981d86b298440444` | same (c) |
| test_native_operator_verbs | 13 | 11 | 2 | 0 | 2.5 | `8abe6adbf81d7064` | same: (c) and the (a) `Not A Group` init |
| test_native_initializer_fidelity | 11 | 11 | 0 | 0 | 1.7 | `35a7032a70e76c35` | same |
| test_native_recovery | 13 | 13 | 0 | 0 | 15.4 | `87b57a45ea01d4c3` | same |
| test_native_storage_codec | 11 | 10 | 1 | 0 | 69.1 | `59275058499bc3d6` | same (c) acceptance stamp |
| test_native_served_differential | 7 | 7 | 0 | 0 | 1.2 | `716e20ad4c870cb4` | same |
| test_native_reader_index | 4 | 4 | 0 | 0 | 7.2 | `cd54517e87fad06c` | same |
| test_native_newnews_migration | 1 | 0 | 0 | 1 | 0.1 | `b4f81b44a1bd1141` | same (no pre-T2 image) |
| test_native_stamp_migration | 1 | 0 | 0 | 1 | 0.1 | `a66916e2e141adb9` | same |
| test_native_hybrid_author | 4 | 3 | 1 | 0 | 53.5 | `37398478ec599749` | same failure; reclassified (c)+(a) (failure 8), fixed on dev after this image |
| test_native_topic_local | 4 | 2 | 0 | 2 | 3.0 | `7b09500a51759897` | same (no pre-v2 image) |
| test_native_topic_metadata | 2 | 2 | 0 | 0 | 1.5 | `b32567063f5edd0c` | same |
| test_native_consumer_inspect | 4 | 4 | 0 | 0 | 0.6 | `85e5bb09a7024ebb` | same |
| test_native_consumer_project_bounds | 2 | 2 | 0 | 0 | 0.3 | `c751f1d9cac7c031` | same |
| test_native_consumer_e2 | 4 | 2 | 1 | 1 | 3.5 | `49d6d62b036dce6c` | same (c) undated source; uid case needs root |
| consumer_e2 signed poll, dated source ×3 | 3 | 2 | 1 | 0 | 4.4 / 11.2 / 11.1 | `48c360a5…` `e918c66a…` `7b8e58be…` | first run errored (failure 4); two reruns pass |
| test_native_checkpoint | 23 | 23 | 0 | 0 | 43.7 | `f29aae45d1d23cdc` | same |
| test_checkpoint | 7 | 7 | 0 | 0 | 449.2 | `91860ffb0ab3ecb7` | same |
| test_native_peering | 4 | 4 | 0 | 0 | 10.0 | `056093fb4acf0787` | same |
| test_native_protected_peering | 5 | 5 | 0 | 0 | 30.5 | `d0106567117a21f9` | same |
| test_native_crash_model | 6 | 6 | 0 | 0 | 59.5 | `de3c32d79cd09ed0` | same |
| test_native_served_crash_model | 2 | 2 | 0 | 0 | 76.7 | `b3c97c6232873a99` | same |
| test_native_tls_transport | 2 | 2 | 0 | 0 | 1.1 | `e59746ff81cce68d` | same |
| test_native_frozen_relocation | 2 | 2 | 0 | 0 | 7.5 | `1e3dcf7199213e56` | **newly run and pass** (was skipped) |
| test_fn_web_native | 2 | 2 | 0 | 0 | 3.1 | `d6912a7ac032e42b` | same |
| test_bp_node_native | 16 | 6 | 10 | 0 | 228.9 | `b9d21fc69db50d2a` | **regression**: was 12/16 (failure 1, (a)) |
| test_bp_app_native | 4 | 1 | 3 | 0 | 562.5 | `6ecbbb4de6e22306` | same (failure 7) |
| test_bp_obligation_native | 4 | 4 | 0 | 0 | 1.3 | `bca121924ad03efa` | same |
| test_bp_service_native (`fn-host-dtn`) | 16 | 9 | 7 | 0 | 6.9 | `e7a4cc9e37c586ab` | first run; failure 5 |
| test_bp_service_native (`.dtn-developer`) | 16 | 16 | 0 | 0 | 14.9 | `a1ed72e254fda32f` | **first run: all pass** |
| test_bp_contact_native | 2 | 2 | 0 | 0 | 0.6 | `aa3a01fab02d3ad7` | **first run: pass** |
| test_bp_contact_relay_native | 1 | 0 | 1 | 0 | 0.6 | `11df21c154088c57` | first run; failure 6, (c) |
| test_bp_receive_integrity_native (`fn-host-dtn`) | 4 | 2 | 2 | 0 | 0.6 | `83607dad692b9021` | first run; failure 5 |
| test_bp_receive_integrity_native (`.dtn-developer`) | 4 | 4 | 0 | 0 | 1.4 | `1df53c403c193f6d` | **first run: all pass** |
| test_native_app_journal | 10 | 0 | 10 | 0 | 4.1 | `c84b21705bfd3473` | first run; **failure 2, (a): DTN images cannot init a Store** |
| test_native_image_profiles | 12 | 10 | 2 subtests | 0 | 1.3 | `942de383206d6b99` | was 9 + 3 skipped; the DTN raw-post cases fail on failure 2 |

**Relocation.** The frozen image directory was copied with `cp -a` to
`/tank/fn/scratch/native-subsets-6c0626c5/reloc/fn-image`, and
`sha256sum -c image.sha256` passed in the copy before and after the run. The
module was then run as:

```
env -u LD_LIBRARY_PATH -u FN_OPENSSL_PREFIX -u SBCL_HOME \
  FN_RUN_RELOCATION_E2E=1 FN_NATIVE_HOST=<copy>/fn-host \
  FN_TEST_OPENSSL=<3.5.8 CLI wrapper> python3 -m unittest -v tests.test_native_frozen_relocation
```

The environment no longer names the build OpenSSL. The build prefix
`/tank/fn/toolchains/openssl-3.5.8` still exists on hbox, though.
Unprivileged user namespaces are disabled, so it could not be hidden, and
`FN_BUILD_OPENSSL_PREFIX` was left unset. The test's "build path absent"
assertion therefore checked `/nonexistent`. The relocated image used its
bundled TLS and ML-DSA, and it refused to start without its bundled OpenSSL.

**Not run:** the campaign/matrix modules, `test_native_shared_owner_bench`,
`test_bp_fragment_node_native`, and the static source-only modules. The
1a9dd747 record gives the same reasons.

## Failures

Classes: (a) fn defect, (b) environment/fixture, (c) test out of date or wrong.

1. **test_bp_node_native: 9 of 10 failures are one new regression. (a)**
   The affected cases:
   - `absent_bp_trust_refuses_receipt_release`
   - `ambiguous_outbox_publication_is_uncertain_not_refused`
   - `conflicting_return_job_fences_after_request_commit`
   - `death_after_durable_outbox_does_not_allocate_second_sequence`
   - `death_after_fnrj_receipt_decision_replays_one_article`
   - `death_after_kind_seven_replays_owed_outbox`
   - `exact_receipt_with_wrong_carrier_peer_fences`
   - `older_unrouted_transit_does_not_block_younger_local_request`
   - `request_retry_queues_distinct_receipt_carriers_and_releases_pin`

   In each, the receiver accepts the bundle and then logs `BP node
   application uncertain: owner BP transit Store outcome is uncertain`. It
   exits 3 with `store: bp-service: application handoff uncertain`, so the
   kind-7, outbox or decision marker the case waits for never appears. The
   line is raised at `host/native/owner.lisp:1289`, where
   `fnn-owner-attempt-transit` answered `:uncertain`. No `unclassified OS
   error` line appears, so the `fnn-os-error` branch of the new
   `fnn-owner-attempt-handlers` is not the cause.

   **The cause is inferred from source, not traced.** The p2-wire merge
   (`4d1f6c79`) made `fnn-owner-attempt` install `fnn-owner-finish-submission`
   as the completion callback (`host/native/owner.lisp:767`). That callback is
   `fn-own-finish`, and it answers `:durable` only if
   `fn-own-completion-names-submission-p` holds. That predicate
   (`books/owner-served-invariants.lisp:56`) requires the stored record's
   payload to equal `fn-own-sub-octets` of the in-flight submission.

   For a BP transit submission, the two sides differ:
   - `fn-own-sub-octets` is `fn-peer-submission-octets`, the raw request.
     The host compares it with the raw bytes at owner.lisp:1267, through
     `fn-owner-bp-transit-raw`, owner-host.lisp:604.
   - The stored payload is `fn-owner-transit-payload`, the relayed octets
     with this node's Path (owner-host.lisp:837).

   So `fn-own-finish` returns `:fault`. `io.lisp:1650` turns that into
   `fnn-indeterminate "ACL2 rejected durable completion after publication"`,
   and the handler maps it to `:uncertain`.

   **This is the matrix's transit finding.**
   `planning/evidence/matrix-6c0626c5-2026-09-24.md` (merged to dev as `fc2e1941`)
   found that NNTP `IHAVE` and `TAKETHIS` into a node with a Path identity
   are stored, answered `436 … uncertain`, and followed by a service exit,
   with no diagnostic. It left the cause as a hypothesis ("the
   Path-prepended payload now differs from the offered octets"). The
   predicate above is where that difference becomes `:fault`: the record
   holds `fn-peer-relayed-octets` (Path prepended), and the in-flight
   submission holds the offered octets. `test_native_peering` and
   `test_native_protected_peering` pass because their nodes set no Path
   identity, so relayed equals offered. The BP node fixture sets
   `path-identity`, so every BP-delivered article hits the mismatch.

   **Fix direction, for the fix lane:** compare the record's payload with the
   relayed octets that the transit sub stages
   (`fn-peer-injection-arguments`), not with `fn-own-sub-octets`, or have
   `fn-own-sub-octets` of a transit sub return the relayed octets. Then
   re-prove `fn-own-240-follows-consumed-completion`, whose statement uses
   the same comparison (owner-served-invariants.lisp:118).

   The article is durable when this fires, and the node stops for recovery on
   every BP-delivered article. P11 therefore has no working application
   handoff on this image. The txid defect of 1a9dd747 (failure 9 there:
   `host/bp-native-app-host.lisp:122` leaves `fn-owner-app-txid` unset) is
   still in this image: that file's last change, `2c8450e0`, predates
   `6c0626c5`. Two of its three cases now fail earlier, on this regression.
   The third, `ambiguous_fnrj_decision_fences_until_cold_replay`, now passes.
   The tenth failure, `older_mru_wait_allows_younger_forward_and_replays`
   (`6 != 7`), is unchanged from 1a9dd747: (c), probable.
2. **DTN images cannot initialize a Store. (a)**
   - **Effect:** `store init` exits 4 on both `fn-host-dtn` and
     `fn-host-dtn-developer`. The error is `ACL2 error in
     fn-store-checkpoint-clone-fence-name: ACL2 executable counterpart
     missing`.
   - **Cases that fail:** all 10 `test_native_app_journal` cases fail in
     `setUp` at line 41, and the two DTN subtests of
     `test_native_image_profiles` fail at lines 187 and 210.
   - **Cause:** `host/native/io.lisp:1062-1066` (`fnn-clone-fence-path`) calls
     that function when a store opens (io.lisp:1332 and 1388). Since
     `be7397c8` (2026-09-23) the function has been defined in
     `host/checkpoint-host.lisp:21`. `host/native/build.lisp:109` loads that
     file, but `host/native/build-dtn.lisp` does not: its `ld` list at lines
     85-106 has `store-host` and `store-node-host` and no `checkpoint-host`.
   - **Fix:** add `(ld "host/checkpoint-host.lisp" :ld-error-action :error)`
     after `build-dtn.lisp:86`. It includes `books/checkpoint-publish`,
     `-compaction`, `-pack-retire` and `-auxiliary`, so the DTN image grows by
     those books. Then rebuild the DTN pair. This lane did neither: the fix
     needs an image build to verify.
   - **Scope:** the BP service, contact and receive paths do not open the
     Store this way, which is why their modules pass.
3. **test_native_raw_scripts: `test_native_owner_group_codes_raw`. (c)**
   The script `eval`s only the `defun fnn-owner-attempt` it reads from
   `host/native/owner.lisp`. Since p2-wire that body is wrapped in the new
   macro `fnn-owner-attempt-handlers` (owner.lisp:722), and it can signal the
   new condition `fnn-store-io-refusal`, which the script does not define.
   Without the macro, the stubbed `fnn-refuse`'s `fnn-store-error` escapes
   unhandled. The script must also load the `defmacro` and define the
   condition.
4. **test_native_consumer_e2:**
   - **Undated default source, (c), unchanged:**
     `test_signed_composite_poll_and_lost_positive_ack_reply` fails at line
     298: `hybrid-author` exits 1 with empty stderr.
   - **Dated source, flaky, cause not isolated:** with
     `FN_CONSUMER_POLL_SOURCE_FILE` set to the dated article, the first run
     errored at line 326 in 4.4 s. The Python ACL2 bridge answer was neither
     `T` nor `NIL`, and that answer was not captured. Three further runs
     pass in about 11 s:
     [`consumer_bool_diag.py`](native-subsets-6c0626c5/consumer_bool_diag.py),
     which prints the raw answer on failure, and `dated-source-2` and `-3`.
     [`bridge_diag.out`](native-subsets-6c0626c5/bridge_diag.out) shows the
     bridge answering `NIL` for each predicate in that form. The raw
     answer of the failing run is unknown, so the flake is recorded, not
     explained.
   - **Skipped:** `test_different_local_uid_is_refused_by_owner` needs root
     and `setpriv`.
5. **DTN production image rejects the selector cases. (c)**
   `test_bp_service_native` (7) and `test_bp_receive_integrity_native` (2)
   fail on `fn-host-dtn` with `FN_*_TEST_* is a developer-image selector;
   this production image does not start with it`: exit 5, the intended
   refusal. The test default `FN_NATIVE_BP_HOST=build/fn-host-dtn` predates
   the production/developer split. On `fn-host-dtn-developer` (`NS_BP_IMAGE`)
   both modules pass 16/16 and 4/4, including
   `transport_uncertain_dominates_refused_article`. That case failed on
   production only because its refused-article leg needs a selector.
6. **test_bp_contact_relay_native:
   `interrupted_contact_receiver_restart_then_expiry`. (c)** The
   [diagnostic](native-subsets-6c0626c5/relay_diag.out) steps through the
   run:
   - The interrupted service run retains the work with `reason=uncertain`.
   - The closed-window tick sends nothing.
   - The open tick delivers the bundle, but the restarted receiver refuses
     it: `BP refused xfer=0 reason=receive-boundary` and `TCPCL passive
     refused inbound … reason=RECEIVE-BOUNDARY`. It writes
     `receive-evidence/…refused`.
   - The sender exits 1 with `BP forwarding retained reason=refused`.

   The fixture configures no `bp-boundary` trust entry and no path identity,
   the same gap the fragment fixture closed (`test_bp_fragment_node_native.py:51-57`).
   Unlike bp-app (failure 7), this path names its refusal reason on both
   sides, and the sender terminates.
7. **test_bp_app_native: 1/4, unchanged from 1a9dd747. (c), probable, plus
   the behaviour finding.** The
   [diagnostic](native-subsets-6c0626c5/bpapp_diag.out) shows the same
   refusal:
   - The receiver logs `BP application refused xfer=0` and `reason=REFUSED`,
     still with no refusal reason.
   - The sender logs `refused outbound xfer=0 reason=4` and then sends
     KEEPALIVE until killed.
   - A one-shot `bp send` still does not exit after its only transfer was
     refused (two cases time out at 180 s).
8. **test_native_hybrid_author: the authored-carrier feed still does not
   deliver on this image.** The 1a9dd747 classification, (a) unisolated, is
   withdrawn. [`hyb_diag-owner1.stderr`](native-subsets-6c0626c5/hyb_diag-owner1.stderr)
   again shows 445 `accepted peer connection` lines in 45 s. The
   hybrid-feed-storm lane (merged `a90e8327` on dev, after `6c0626c5`) showed
   that those are the test's own ARTICLE polls, not a feed storm. The sender
   made one connection and got `439`, because the receiver had not enrolled
   the author, and neither side logged the refusal.
   - **(c):** the fixture lacks the receiver enrollment.
   - **(a):** the refusal was never logged.

   Both are fixed on dev, not in this image.
9. **Unchanged (c) and (a) from 1a9dd747:**
   - (c) `test_native_control`: `control.lisp:344` list.
   - (c) `test_native_operator_cli`: `fn-ncfg-rest`.
   - (c) `test_native_operator_verbs`: upper-cased stderr.
   - (c) `test_native_storage_codec`: the acceptance stamp makes two frames
     differ.
   - (a) `operator init "Not A Group"` is still accepted:
     `books/records-shape.lisp:100`, `books/native-operator.lisp:110-123`.

## P1 to P11: modules that observe each property on 6c0626c5

| P | modules and result |
| --- | --- |
| P1 | `test_native_auth` 4/4, including `test_restricted_command_before_login_is_480_and_leaves_no_article` (new, passes); `test_native_starttls` 2/2, `test_native_auth_admin_fidelity` 3/3, `test_native_protected_peering` 5/5, `test_native_tls_transport` 2/2, `test_native_frozen_relocation` 2/2 (bundled TLS) |
| P2 | `test_native_crash_model` 6/6, `test_native_served_crash_model` 2/2, `test_native_owner` 18/18; `test_native_storage_codec` 10/11 (c). BP transit completion is **uncertain on every article** (failure 1), a P2 regression on the BP path. |
| P3 | `test_native_reader_index` 4/4, `test_native_served_differential` 7/7; migrations skipped (no pre-T2 image) |
| P4 | `test_native_peering` 435 both ways; `test_native_owner` conflicting-evidence case; `test_native_checkpoint` covered-conflict case; `test_bp_service_native` `outage_restart_duplicate_and_conflict` passes on both DTN images |
| P5 | `test_native_owner` local-fault, disconnect and reset cases (18/18); `test_native_control` busy ceiling |
| P6 | `test_native_live_reconfiguration` 11/11 on the first image with `fn-ocl-publish`, including `a_live_peer_add_leaves_a_pinned_reader_unchanged_and_is_durable` and `a_group_created_live_is_served_before_restart`; `test_native_admin` 9/9, `test_native_initializer_fidelity` 11/11, `test_native_profile` 3/3; `test_native_operator_verbs` 11/13 (the (a) `Not A Group` defect remains) |
| P7 | `test_native_peering` 4/4 and `test_native_protected_peering` 5/5, both with no Path identity; with a Path identity transit is answered uncertain (failure 1, the matrix finding); `test_native_hybrid_author` authored-carrier feed fails (439 on an unenrolled author, fixed on dev) |
| P8 | `test_native_hybrid_author` 3/4; `test_native_consumer_e2` signed poll passes with a dated source (2 of 3 runs, one unexplained bridge error) |
| P9 | `test_native_admin` capacity/retire/reopen; `test_bp_obligation_native` 4/4; `test_native_app_journal` forwarding-capacity case **fails in setUp** (failure 2: DTN Store init) |
| P10 | `test_native_crash_model` 6/6, `test_native_served_crash_model` 2/2, `test_native_checkpoint` 23/23, `test_checkpoint` 7/7, `test_native_recovery` 13/13 |
| P11 | `test_bp_service_native` 16/16 and `test_bp_receive_integrity_native` 4/4 on `fn-host-dtn-developer`, including `outage_restart_duplicate_and_conflict`, `wall_jump_after_interrupted_contact_retains_anchored_work` and `monotonic_age_expires_interrupted_work`; `test_bp_contact_native` 2/2; `test_bp_contact_relay_native` 0/1 (fixture lacks boundary trust); `test_bp_node_native` 6/16 (failure 1 regression plus MRU (c)); `test_bp_app_native` 1/4; `test_bp_obligation_native` 4/4 |

## Diff against 1a9dd747

- **Newly pass:**
  - `test_native_owner` 18/18: the image's SBCL is on PATH.
  - `test_native_auth` P1 480 case.
  - `test_bp_service_native` 16/16 and `test_bp_receive_integrity_native`
    4/4 on the DTN developer image, and `test_bp_contact_native` 2/2: first
    DTN evidence.
  - `test_native_frozen_relocation` 2/2.
  - `test_bp_node_native` `ambiguous_fnrj_decision_fences_until_cold_replay`.
  - `test_native_live_reconfiguration` 11/11, now on an image that carries
    `fn-ocl-publish`.
- **Newly fail:**
  - `test_bp_node_native`: 7 cases that passed on 1a9dd747 (failure 1, (a),
    p2-wire finish callback over a Path-updated transit payload; the same
    defect as the matrix's transit finding).
  - `test_native_raw_scripts` `owner_group_codes_raw` (c).
  - `test_native_app_journal` 0/10 and 2 `test_native_image_profiles` DTN
    subtests: failure 2, (a), a DTN build-script omission, first run.
  - `test_bp_contact_relay_native` (c), first run.
- **Unchanged failures:**
  - `test_bp_app_native` 1/4.
  - `test_native_hybrid_author`, now explained by the hybrid-feed-storm lane.
  - Control, operator_cli, operator_verbs, storage_codec and consumer_e2
    (undated).

## What this does not establish

These are selected tests on one image set, not a suite, and not the deployed
node (`da5fd8cb`). Failure 1's cause is a source reading. The only direct
evidence is that the uncertainty arrives without an OS-error line, and
fn-own-finish's `:fault` is the one new path to `fnn-indeterminate` in the
transit attempt since 1a9dd747. Failure 2's fix is proposed and unbuilt. The
relocation run did not hide the build OpenSSL from the filesystem.
