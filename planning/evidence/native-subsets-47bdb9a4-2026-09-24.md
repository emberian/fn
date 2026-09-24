# Native test modules on the 47bdb9a4 images

Every image-gated native module, run one module at a time on hbox on
2026-09-24 between 16:53Z and 17:24Z against the four `47bdb9a4` images. Every
opt-in flag was set from the start, the image's SBCL was first on `PATH`, and
the DTN variables were set. The previous run is
[native-subsets-6c0626c5](native-subsets-6c0626c5-2026-09-24.md). Logs, the
runners and the diagnostics are in
[`native-subsets-47bdb9a4/`](native-subsets-47bdb9a4/), with
[`SHA256SUMS`](native-subsets-47bdb9a4/SHA256SUMS).

## Images and environment

- **Gate:** `/tank/fn/gates/qual-47bdb9a4-20260924` was only read. Its tree
  was rsynced without `build/` and `.git` to
  `/tank/fn/scratch/native-subsets-47bdb9a4/tree`. The copy's `build/` holds
  symlinks into the frozen image directory `<gate>/build/images/47bdb9a4/`
  (four launchers and cores, `runtime`, `lib`, `openssl`, `image.sha256`).
- **Checksums:** `sha256sum -c image.sha256` in the image directory passed
  before the runs and after the last one. `build-source.sha256` passed on the
  gate and on the copy. The copy's `tests/`, `tools/` and `host/` match
  `git archive 47bdb9a4` file by file (944 files); the only extra files are
  certificates, `.port` files and `__pycache__`.
- **Two test trees.** The six stale-test fixes (`514459d9`) and the kind-8
  native case (`bd497bd2`) merged after the `47bdb9a4` cut, so the image tree
  does not carry them. `tree-dev` is the same copy with `tests/` replaced by
  dev `552c763e`'s `tests/`. Its host and books are the image's, so its
  source-text tests read the image's source. Rows marked *dev tests* ran there.

| image | launcher SHA-256 | core SHA-256 |
| --- | --- | --- |
| `fn-host` | `432622d29a28d594…` | `73ad25bc207a3b35…` |
| `fn-host-developer` | `e4eeefd290450e74…` | `b81bdaf69dca347a…` |
| `fn-host-dtn` | `095382bae2b3ff37…` | `3c829019aeebaad0…` |
| `fn-host-dtn-developer` | `4986f14bf4ebc34f…` | `65da00ed01b8e1b4…` |
| `runtime/sbcl` (SBCL 2.6.8) | `b115fe956aadee60…` | |

The launchers are byte-identical to 6c0626c5's; the cores differ.

The runner is [`run.sh`](native-subsets-47bdb9a4/run.sh). It is the 6c0626c5
runner with the gate and image paths and `FN_NATIVE_IMAGE_SOURCE_SHA`
(`47bdb9a40742…`) changed, plus `NS_TREE` (`tree` or `tree-dev`). These are
unchanged:
- the `FN_NATIVE_*` launcher and SHA-256 variables, read from `image.sha256`;
- the DTN variables: `FN_NATIVE_DTN_HOST`, `FN_NATIVE_DTN_DEVELOPER_HOST`,
  `FN_NATIVE_BP_HOST` (default `fn-host-dtn`, overridden by
  `NS_BP_IMAGE=fn-host-dtn-developer`), `FN_NATIVE_CONTACT_SENDER` and
  `FN_NATIVE_CONTACT_RECEIVER`;
- `PATH=$S/bin:…`, where `sbcl` links to `<image>/runtime/sbcl`, and
  `SBCL_HOME=<image>/runtime/sbcl-home/`;
- `FN_RUN_{TOPIC_LOCAL_E2E,TOPIC_METADATA_E2E,HYBRID_E2E,NATIVE_READER_INDEX,
  CONSUMER_INSPECT,CONSUMER_PROJECT_BOUNDS,NATIVE_CLONE,CONSUMER_E2E,
  CONSUMER_POLL_E2E}=1`.

Each module ran as `timeout 3600 python3 -m unittest -v tests.<module>`.
[`chainA.sh`](native-subsets-47bdb9a4/chainA.sh) (BP/DTN) and
[`chainB.sh`](native-subsets-47bdb9a4/chainB.sh) (everything else) ran
side by side, each under `nohup … < /dev/null`. Every port was ephemeral and
every store was under `/tmp`. `FN_RUN_RELOCATION_E2E` ran through
[`reloc.sh`](native-subsets-47bdb9a4/reloc.sh), which uses the 6c0626c5
relocation form. [`diag.sh`](native-subsets-47bdb9a4/diag.sh) runs a
diagnostic script with `run.sh`'s environment. After the runs, no process from
this scratch directory or image was left.

## Results

Wall is the whole unittest process in seconds. The last column compares with
6c0626c5.

| module (log) | tests | pass | fail+err | skip | s | log SHA-256 (16) | vs 6c0626c5 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| test_native_auth | 4 | 4 | 0 | 0 | 9.1 | `5caf0854338c5d1e` | same |
| test_native_profile | 3 | 3 | 0 | 0 | 0.8 | `0913ae372089eb82` | same |
| test_native_admin | 9 | 9 | 0 | 0 | 3.4 | `73f212906ecf889f` | same |
| test_native_starttls | 2 | 2 | 0 | 0 | 0.6 | `8415424b96c737c9` | same |
| test_native_auth_admin_fidelity | 3 | 3 | 0 | 0 | 12.2 | `80c8b3d84b70bd66` | same |
| test_native_owner | 18 | 18 | 0 | 0 | 21.8 | `c8d17e46c480e461` | same |
| test_native_raw_scripts | 9 | 6 | 3 | 0 | 0.4 | `9fa5bc13b422260d` | **+2 newly fail** (failure 3, (c)) |
| test_native_raw_scripts, *dev tests* | 9 | 7 | 2 | 0 | 0.4 | `0969902e7043d157` | `owner_group_codes_raw` passes; the other 2 remain (failure 3) |
| test_native_live_reconfiguration | 11 | 11 | 0 | 0 | 1.5 | `da7b9c3368462eee` | same |
| test_native_control | 14 | 13 | 1 | 0 | 20.2 | `46247d5d2ab2f05c` | same (c) |
| test_native_control, *dev tests* | 14 | 14 | 0 | 0 | 20.8 | `d3910cc782d2e181` | **passes** |
| test_native_operator_cli | 6 | 5 | 1 | 0 | 3.9 | `80f748ec1de9ac6a` | same (c) |
| test_native_operator_cli, *dev tests* | 6 | 6 | 0 | 0 | 4.0 | `860dea478cdb67f1` | **passes** |
| test_native_operator_verbs | 18 | 18 | 0 | 0 | 6.3 | `a2505b25c27995b0` | **newly all pass** (was 11/13) |
| test_native_operator_verbs, *dev tests* | 18 | 18 | 0 | 0 | 6.3 | `98939f4647f4d368` | all pass |
| test_native_initializer_fidelity | 11 | 11 | 0 | 0 | 1.4 | `b907e9385b37d59d` | same |
| test_native_recovery | 13 | 13 | 0 | 0 | 12.3 | `d2c52469951157b5` | same |
| test_native_storage_codec | 11 | 10 | 1 | 0 | 54.5 | `0443a331bd4ca822` | same (c) |
| test_native_storage_codec, *dev tests* | 11 | 11 | 0 | 0 | 61.1 | `bcfd74574f353ef1` | **passes** |
| test_native_served_differential | 7 | 7 | 0 | 0 | 1.0 | `ea5e67406bcf7e4a` | same |
| test_native_reader_index | 4 | 4 | 0 | 0 | 5.4 | `a1692a89bdccfa4c` | same |
| test_native_newnews_migration | 1 | 0 | 0 | 1 | 0.0 | `37f797810209f82d` | same (no pre-T2 image) |
| test_native_stamp_migration | 1 | 0 | 0 | 1 | 0.0 | `b7e2b43e50ab008f` | same |
| test_native_hybrid_author | 5 | 5 | 0 | 0 | 12.9 | `69c129639598ed34` | **newly all pass** (was 3/4; one new case) |
| test_native_topic_local | 4 | 2 | 0 | 2 | 2.5 | `08430fac5267074b` | same (no pre-v2 image) |
| test_native_topic_metadata | 2 | 2 | 0 | 0 | 1.1 | `fc56a0078160d2c8` | same |
| test_native_consumer_inspect | 4 | 4 | 0 | 0 | 0.5 | `e5aa01c3755d3201` | same |
| test_native_consumer_project_bounds | 2 | 2 | 0 | 0 | 0.2 | `dd9ac7b0fb41ef5e` | same |
| test_native_consumer_e2 | 4 | 2 | 1 | 1 | 3.2 | `4859a90019d78d41` | same (c) undated source; uid case needs root |
| consumer_e2 signed poll, dated source | 1 | 1 | 0 | 0 | 11.3 | `55d9f52f41fb6fa0` | passes on its first run (6c0626c5: first run errored) |
| test_native_checkpoint | 23 | 23 | 0 | 0 | 41.5 | `368f0375c8f94042` | same |
| test_checkpoint | 7 | 7 | 0 | 0 | 461.3 | `fa15b5e620c941d0` | same |
| test_native_peering | 5 | 5 | 0 | 0 | 7.3 | `9386f2dfd4ff1a29` | **+1: Path-identity transit case, new, passes** |
| test_native_protected_peering | 5 | 5 | 0 | 0 | 26.9 | `116ee36b8454113c` | same |
| test_native_crash_model | 7 | 7 | 0 | 0 | 68.6 | `ca28ea379c7ea0e2` | +1 new case, passes |
| test_native_served_crash_model | 2 (18 subtests) | 0 | 18 subtest errors | 0 | 77.4 | `138e3616fd67f363` | **newly fails** (failure 1, (c)) |
| served_crash_model with the 6c0626c5 helper (diagnostic) | 2 | 2 | 0 | 0 | 76.4 | `f48519ec7e0038ab` | the image passes every served cut |
| test_native_tls_transport | 2 | 2 | 0 | 0 | 0.7 | `bcbb2489ec95068f` | same |
| test_native_frozen_relocation (stdin closed) | 2 | 2 | 0 | 0 | 1.2 | `677ef1c245411f06` | same |
| test_native_frozen_relocation (stdin open) | 2 | 1 | 1 | 0 | 121.6 | `00c0dd26158e1274` | failure 5: (b) run, (a) finding on both images |
| test_fn_web_native | 4 | 4 | 0 | 0 | 6.7 | `4413015a52c48a5a` | +2 new cases, pass |
| test_bp_node_native | 16 | 15 | 1 | 0 | 298.8 | `7ff3b0e9dc2eb277` | **9 newly pass** (was 6/16): transit-436 fix; the one left is the MRU (c) |
| test_bp_node_native, *dev tests* | 17 | 16 | 1 | 0 | 333.2 | `a69852fb87e70167` | MRU passes; the kind-8 case **fails** (failure 2) |
| test_bp_app_native | 4 | 1 | 3 | 0 | 561.3 | `9844bf7f52150ddf` | same (failure 4, (a)) |
| test_bp_app_native, *dev tests* | 4 | 1 | 3 | 0 | 560.0 | `6564ce5b7e5e1bbd` | same; the enrolled fixture does not help (arity defect) |
| test_bp_obligation_native | 4 | 4 | 0 | 0 | 1.1 | `60812578212532fc` | same |
| test_bp_fragment_node_native | 1 | 1 | 0 | 0 | 28.0 | `f6d4a2628e99509e` | first run in these subsets (developer image) |
| test_bp_service_native (`fn-host-dtn`) | 16 | 9 | 7 | 0 | 4.1 | `74acc1d2dc9758d0` | same (c): selectors on production |
| test_bp_service_native (`.dtn-developer`) | 16 | 16 | 0 | 0 | 14.2 | `d8ba35fc11230537` | same, all pass |
| test_bp_contact_native | 2 | 2 | 0 | 0 | 0.5 | `4f153e58d6a09250` | same |
| test_bp_contact_relay_native | 1 | 0 | 1 | 0 | 0.5 | `2ac7a410b855dda3` | same (c), receive-boundary refusal |
| test_bp_receive_integrity_native (`fn-host-dtn`) | 4 | 2 | 2 | 0 | 0.5 | `c8f8126070d4318c` | same (c): selectors on production |
| test_bp_receive_integrity_native (`.dtn-developer`) | 4 | 4 | 0 | 0 | 0.9 | `ea5ce4cbfe787cd4` | same, all pass |
| test_native_app_journal | 10 | 10 | 0 | 0 | 8.1 | `b8ef7476e57c7158` | **newly all pass** (was 0/10): the DTN store-init fix |
| test_native_image_profiles | 12 | 12 | 0 | 0 | 1.4 | `08de070046714d32` | **newly all pass** (DTN raw-post subtests) |

**Capacity lane (m5-capacity).** It added no module. Its two native cases are
in `test_native_operator_verbs`, and both pass on the developer image:
- `test_the_default_profile_budget_is_reported_and_refused_by_name`: `operator
  status` headroom, and the refusal at the budget;
- `test_the_scale_profile_is_reachable_from_init`: `init --profile scale`.

**Group names.** These `test_native_operator_verbs` cases pass:
`test_init_without_a_group_is_usage_and_writes_nothing` (the `Not A Group`
case), `test_reserved_names_are_refused_by_acl2_at_init_and_create`,
`test_init_of_a_reserved_name_is_refused_and_writes_nothing` and
`test_group_create_poster_is_refused_and_publishes_nothing`. The module needs
no later image.

**Not run:**
- the campaign and matrix modules (`tests.campaign.*`,
  `test_native_operator_campaign`, `test_native_v0_matrix`,
  `test_native_nntp_post_probe`), which other lanes run on this image;
- `test_native_shared_owner_bench` (bench);
- the static source-only modules (`test_native_served_cost`,
  `_compaction_crash_map`, `_crash_correspondence`, `_cut_map`,
  `_block_fault_ownership`, `_peering_matrix_slice`,
  `_two_host_protected_gate`, `test_build_lists_check` and the
  `test_native_bp_*` raw wrappers).

## Failures

Classes: (a) fn defect, (b) environment/fixture, (c) test out of date or wrong.

1. **test_native_served_crash_model: 18 of 18 cut subtests error. (c)**
   - **Error:** `TypeError: cannot unpack non-iterable NoneType object` at
     `tests/test_native_crash_model.py:103` (`intended_frames`). Each owner is
     killed at its cut first, as intended.
   - **Cause:** probe-tables commit `9e76b236` made the shared helper
     `assert_observed_scan_is_program_image` derive the intended frames from
     `sent=(message_id, payload, groups, (t0, t1))`, `before_frontier` and
     `prior_frame`. It updated the caller in `test_native_crash_model.py:309`,
     but not the one in `test_native_served_crash_model.py:96`. That caller
     passes none of the three, and `sent` defaults to `None`. Dev `552c763e`
     has the same code.
   - **The image is not at fault.** The same run with 6c0626c5's
     `test_native_crash_model.py`
     ([`crash_model_6c0626c5.py`](native-subsets-47bdb9a4/crash_model_6c0626c5.py),
     tree `tree-diag`) passes 2/2 in 76.4 s: every served cut, then recovery,
     the prior article's bytes kept, and the candidate absent or present as
     the cut says.
   - **Fix:** the served caller must pass what it sent: the candidate
     Message-ID, the payload the owner stores for an NNTP POST, `fn.test`,
     the clock bracket, the pre-post frontier and the prior frame. That
     payload is not the file bytes, so this needs care, and this lane did not
     make the fix.
2. **test_bp_node_native, *dev tests*,
   `test_death_after_kind_eight_retries_once_and_peer_holds_one_copy`: fails,
   and does not skip. (b), the image predates it.**
   - It waits 240 s for `BP NODE KIND8 SENT` and gets `BP FNBS recovered
     held=1 … TCPCL bp-node-forward event …` without the marker.
   - `FN_BP_NODE_TEST_PAUSE_AFTER_KIND_EIGHT_SENT` and the retry policy
     arrived in `bd497bd2`, after the cut. This image ignores the selector
     and does not pause.
   - The docstring says "the class skips without an image". It does, but an
     image without the selector fails instead of skipping. A new image must
     carry the merge.
3. **test_native_raw_scripts. (c)** The scripts `eval` host `defun`s read
   from `host/` and stub the rest. Two images' worth of host change broke
   three stubs:
   - `test_native_owner_group_codes_raw`: failure 3 of 6c0626c5. It is fixed
     in the dev tests and passes there.
   - `test_native_owner_bound_commit_raw` (new): `The function ACL2::FNN-ERR
     is undefined`. Transit-436's `000c6b6e` ("Log the reason when a bound
     Store commit raises indeterminate") added an `fnn-err` call to the path
     that the script evaluates, and the script does not define `fnn-err`
     ([`raw_scripts_diag.out`](native-subsets-47bdb9a4/raw_scripts_diag.out)).
   - `test_native_owner_consumer_raw` (new): `capacity refusal advanced the
     frontier`. The script drives the refusal through a stub
     `fnn-config-max-transactions` (it returns 2). m5-capacity (`ce27b18d`)
     moved the decision into ACL2 (`fn-sbud-prepare`, installed at
     `host/owner-host.lisp:375`) and removed every host capacity comparison,
     so the stub no longer decides anything.
   - Both new failures are inferred from source. They fail the same way under
     the dev tests. The script must now take the refusal from the installed
     ACL2 prepare, not from a host stub.
4. **test_bp_app_native 1/4, both trees. (a)** This is the bp-app receive
   arity defect (`host/native/bp-app.lisp:213-215` passes 8 arguments to the
   9-parameter `fnn-bpapp-accept-locked`) from
   [stale-native-tests](stale-native-tests-2026-09-24.md). It is still in this
   image, and the bp-app-receive lane is fixing it.
   - `lost_receipt_restart` fails with the receiver's refusal.
   - Two cases time out after 180 s in a one-shot `bp send` that never exits
     after the refusal.
   - The dev fixture's enrollment does not change the outcome.
5. **test_native_frozen_relocation with an open stdin: (b) for the run, (a)
   for the finding.**
   - **The run:** `reloc.sh` was first launched from an ssh session whose
     stdin was an open pipe. `test_missing_bundled_openssl_refuses_startup`
     then timed out after 120 s. With `< /dev/null`, as 6c0626c5 ran it, the
     module passes 2/2 in 1.2 s. The copy's `image.sha256` passed before and
     after.
   - **The finding:** with the bundled OpenSSL absent, `fn-host --fn store …
     init` raises `FNN-TLS-UNAVAILABLE` ("no complete OpenSSL
     libcrypto/libssl pair exists") from `fnn-tls-initialize` under
     `fn-native-entry`. It prints `unhandled condition in --disable-debugger
     mode, quitting`, then an ACL2 `*` prompt on stdout, and then it waits on
     stdin. It exits 1 only at EOF
     ([`missing-openssl-stdin-closed.stderr`](native-subsets-47bdb9a4/missing-openssl-stdin-closed.stderr)).
   - **Both images do this.** The same pair, rebuilt from the 6c0626c5 and
     47bdb9a4 images and run with a stdin held open, still runs after 15 s
     on each. Under a supervisor or an interactive shell, a refused start
     hangs instead of exiting.
   - No store is written.
6. **Unchanged, (c):**
   - `test_bp_service_native` (7) and `test_bp_receive_integrity_native` (2)
     on `fn-host-dtn`: the production image refuses developer selectors, and
     both modules pass on `fn-host-dtn-developer`.
   - `test_bp_contact_relay_native`: the restarted receiver answers `BP
     refused xfer=0 reason=receive-boundary`, and the sender exits 1 with
     `BP forwarding retained reason=refused`. The fixture configures no
     boundary trust
     ([`relay_diag.out`](native-subsets-47bdb9a4/relay_diag.out)).
   - `test_native_consumer_e2`, undated source: `hybrid-author` exits 1 with
     empty stderr (line 59, from 298).
   - `test_bp_node_native` MRU `6 != 7`, fixed in the dev tests.
   - control, operator_cli and storage_codec at 47bdb9a4's tests, all fixed
     in the dev tests.

## P1 to P11: modules that observe each property on 47bdb9a4

| P | modules and result |
| --- | --- |
| P1 | test_native_auth 4/4 (480 before login), starttls 2/2, auth_admin_fidelity 3/3, protected_peering 5/5, tls_transport 2/2, frozen_relocation 2/2 (bundled TLS; stdin closed), fn_web_native login over TLS |
| P2 | crash_model 7/7, owner 18/18, storage_codec 11/11 (dev tests); served_crash_model passes every served cut only with the 6c0626c5 helper (failure 1); BP transit completion is durable again (bp_node 15/16), and a Path-identity peering transit is accepted with the owner up (peering 5/5) |
| P3 | reader_index 4/4, served_differential 7/7; migrations skipped (no pre-T2 image) |
| P4 | peering 435 both ways; owner and checkpoint conflicting-evidence cases; bp_service `outage_restart_duplicate_and_conflict` on `fn-host-dtn-developer` |
| P5 | owner 18/18 local-fault, disconnect and reset cases; control 14/14 (dev tests) busy ceiling |
| P6 | live_reconfiguration 11/11, admin 9/9, initializer_fidelity 11/11, profile 3/3, operator_verbs 18/18 (group-name and reserved-name refusals) |
| P7 | peering 5/5 incl. `test_transit_into_a_node_with_a_path_identity_is_accepted_and_owner_stays`, protected_peering 5/5, hybrid_author authored-carrier feed passes (5/5) |
| P8 | hybrid_author 5/5 incl. the unenrolled-receiver refusal; consumer_e2 signed poll with a dated source, 1/1 on its first run |
| P9 | admin capacity/retire/reopen; operator_verbs default-profile budget reported in `operator status` and refused by name, and `init --profile scale`; bp_obligation 4/4; app_journal 10/10 incl. `forwarding_capacity_exhaustion_refuses_without_durable_record` |
| P10 | crash_model 7/7, checkpoint 23/23, test_checkpoint 7/7, recovery 13/13; served_crash_model 18 cuts error as run (failure 1) and pass with the old helper |
| P11 | bp_node 15/16 (16/17 dev tests; kind-8 case needs a later image), bp_service 16/16 and receive_integrity 4/4 on `fn-host-dtn-developer`, bp_contact 2/2, bp_fragment_node 1/1, bp_obligation 4/4, app_journal 10/10; bp_app 1/4 (arity defect), contact_relay 0/1 (fixture) |

## Diff against 6c0626c5

- **Newly pass:**
  - `test_bp_node_native`: 9 cases, 6/16 → 15/16, from the transit-436 fix.
    With the dev tests the MRU case also passes.
  - `test_native_peering`: the new Path-identity transit case.
  - `test_native_app_journal`: 0/10 → 10/10. `test_native_image_profiles`:
    the two DTN subtests now pass, 12/12. Both come from the DTN store-init
    fix.
  - `test_native_operator_verbs`: 11/13 → 18/18, covering `Not A Group`, the
    reserved names and the two capacity cases.
  - `test_native_hybrid_author`: 3/4 → 5/5.
  - `test_native_crash_model` +1 and `test_fn_web_native` +2, both new cases.
  - `test_bp_fragment_node_native`: 1/1, the first run in these subsets.
  - With the dev tests: control 14/14, operator_cli 6/6, storage_codec 11/11
    and raw `owner_group_codes_raw`.
- **Newly fail:**
  - `test_native_served_crash_model`: 18 subtest errors (failure 1, (c)).
  - `test_native_raw_scripts`: `owner_bound_commit_raw` and
    `owner_consumer_raw` (failure 3, (c)).
  - The dev tests' kind-8 case (failure 2): the image predates it.
  - Relocation with an open stdin (failure 5). This is not a regression: both
    images behave the same.
- **Unchanged failures:**
  - bp_app 1/4.
  - contact_relay.
  - bp_service and receive_integrity on the production DTN image.
  - consumer_e2 with an undated source.

## What this does not establish

These are selected tests on one image set, not a suite, and not the deployed
node (`da5fd8cb`). The raw-script causes in failure 3 are read from source.
The served-crash diagnostic replaces a test file. It shows only that the
image passes the 6c0626c5 form of the check, not the newer frame derivation
over served posts. The kind-8 retry has no native evidence until an image
carries `bd497bd2`.
