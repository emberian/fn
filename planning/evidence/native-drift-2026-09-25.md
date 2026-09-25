# native-drift, 2026-09-25 (night deputy fix lane)

Branch `lane/native-drift` from dev `ac70f38d`. No PRF, no book changed.
Commits: `d1902191` (tests), `32842f50` (host), the record commit.

## The known reds and what each was

| Red | Cause | Fix |
| --- | --- | --- |
| `test_peer_list_is_a_query...` (operator_verbs) | `fn-native-admin-peer-report` moved to books/native-admin-peer.lisp | test: asserts the defun there, that native-admin includes that book, and that `fn-native-admin-query-report` still calls it |
| `test_native_observation_wrapper_calls_composed_subject` | host/store-node-host.lisp `fn-store-sn-io` calls the concrete twin `fn-rcon-sn-io` | test: asserts that call and the statement of `fn-rcon-sn-io-is-sn-io` (books/records-concrete) equating it to `fn-sn-io` |
| `test_the_uncertain_word_is_acl2s_control_vocabulary` (non-ASCII) | already fixed on dev: books/native-control.lisp has no byte above 0x7f at `ac70f38d` | none needed; passes |
| two raw-stub runs (`SOCKOPT-ERROR`) | tests ran `sbcl` from PATH; hbox's /usr/bin/sbcl is 2.2.9 and does not export `sb-bsd-sockets:sockopt-error`; the images run /tank/fn/sbcl 2.6.8 | `tests/native_process.runtime_sbcl`: the raw-stub tests run on the image's own runtime (FN_SBCL, the frozen `runtime/sbcl`, or the wrapper's `exec` line and SBCL_HOME; PATH last) |
| raw selectors, behind the reader error | `fnn-recovery-test-fault` now asks `fn-hm-marker-cut-names`; `fnn-owner-run-normalized` calls `fnn-state-checkpoint-test-fault`; the harness had neither | harness: `fnn-core` stub answers the book's own quoted table (read from books/store-history-marker.lisp); loads the deployed `fnn-state-checkpoint-test-fault`; new checks: each marker cut is selectable, each state-checkpoint cut arms the served owner, a posting-entry fault takes the slot first |
| two owner runs "acl2 not found" | `tools/run_store.py peer add` needs `FN_ACL2` | invocation: `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g` |
| `test_article_over_the_body_limit...` wording | code: the served POST bound was set to A only by `fnn-control-start`'s `fn-owner-posting-configure`; `owner run` (no control start) kept recovery's codec ceiling, so a 40 960-octet article under the development profile's A = 32 768 was read whole and refused at `fn-owner-post-boundary` with the generic `441 ... the article was refused` | host/owner-host.lisp `fn-owner-install-profile` (called at host/native/owner.lisp `fnn-owner-install`) also sets max-octets to `fn-owner-served-post-bound`, keeping allow/agent/groups; the wire now closes at A with the size line |

The test changes keep every assertion; they repoint source-text checks to the
current definitions and add checks.

## Certification and images (hbox)

- Farm `run-20260925T100637Z-1430`, `--remote-root /tank/fn/gates/native-drift-r1`,
  roots = default + dtn image roots (142), 2 jobs, 300 s: exit 0; 195
  certified, 142 from cache. Manifest
  `planning/evidence/manifests/certify-20260925T100705Z-3116225.json`.
- `tools/runbooks/hbox-image-build.sh /tank/fn/scratch/native-drift/src2 32842f50…`:
  production and developer built. fn-host.core `b7048de9…5be0`,
  fn-host-developer.core `2e09b662…0f6f`. The DTN image did NOT build (below).

## Native run (developer + production, `32842f50`)

`tests.test_native_owner test_native_operator_verbs test_native_crash_correspondence
test_native_profile_upgrade test_native_control test_native_bounds_join.LargeArticleTests
test_native_cut_map test_native_state_checkpoint test_native_profile`, under
`systemd-run --user --scope -p MemoryMax=24G`, TMPDIR in the scratch dir,
FN_ACL2 set: 85 run, 3 failed, 4 skipped. Every red in the brief is green.

| Log (planning/evidence/native-drift-2026-09-25/) | sha256 |
| --- | --- |
| native-modules.log | `8e220a99776f010a1dd250fe52d1dea8fe7a58b5cfa13625d9704a5f2e2c329f` |
| capacity-old-image.log | `b2d866f94fdb2b30e63977559198b04f0dd1046275a14823043d0ff41640845d` |
| image-build-2.log | `cbae0b0c244fcf1d5c40ebceabf6de3fdca394e36a6a71b503f14538b5d81bde` |

## Open: three new reds, not this lane's to hide

1. **Status reads H = 0 for any H at or above 2^34 on the `ac70f38d` images.**
   `operator status` prints `max-history-octets=0 ... history-bound=0` for the
   default H = 2^40 and for any explicit H from 17 179 869 183 up; 8 589 934 592
   prints correctly. The persisted config.json carries 2^40 correctly, and the
   certified `fn-bs-config-decode` + `fn-bs-profile-report` in a plain ACL2
   session over those exact octets answers 1099511627776. So the image's
   executable path differs from the logical definition above ~2^33: a
   compiled/concrete-twin decode defect (a D27 correspondence failure) or a
   host path I did not find. Fails `NativeOperatorCapacityTests.test_init_writes...`
   and, likely by the same cause (a 0 history bound makes publication
   unaffordable), `test_the_development_profile_budget_is_reported_and_refused_by_name`
   (POST gets no 340). Both PASS on the bounds-blob image `d9203155`
   (capacity-old-image.log), so this entered with a merge between
   `d9203155` and `ac70f38d`. Needs a lane with the image REPL.
2. `OperatorFieldsTests.test_a_raise_of_any_field_and_a_shrink_refused_by_name`
   fails on both images: on `d9203155` a digest mismatch
   (`e8ec6e0c…` vs `a725e81e…`), on `ac70f38d` the H = 0 above.
3. **The DTN image does not build** at `32842f50` (and so at `ac70f38d`:
   no DTN input changed here): host/native/build-dtn.lisp has no
   `(include-book "books/octets-stobj")`, so `fn-owner-prepare-buffer`'s
   `:stobjs (fn-octets state)` fails, then `fn-native-live-status-host-reply`
   and `fn-owner-workflow-install-replay` fail on names after it
   (native-build-dtn.log sha256 `ec9422e0…9c260`, on hbox only).

Other: `tests/test_native_raw_scripts.py` and the BP raw tests still pick
`sbcl` from PATH; if they read host/native/io.lisp they need `runtime_sbcl`
too. `make check` in this worktree reports 5 errors (STO-014/SCN-048 status,
stale ledger), all in registry files this lane did not touch.
