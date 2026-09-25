# Test iteration time (lane test-latency, 2026-09-25, PKT-163, PKT-162)

Base: dev ed7866d2. Laptop: darwin, Homebrew ACL2 8.7_6 on SBCL 2.6.8,
Python 3.14.7, bridges through the slot pool. hbox: ACL2 w28
`acl2-literal-4g`, the bp-n16-prod lane tree at a4d95797 copied to
`/tank/fn/scratch/test-latency/tree` with this lane's four Python tools
overlaid, native images unchanged (`fn-host-dtn-developer.core`
`06f027514325e39d…`), under `systemd-run --user --scope -p MemoryMax=24G`.
No book changed; no farm run; no PRF.

## Where the time went (from the code, then one boot, one call, one test)

Every test starts `tools/run_store.py` / `tools/checkpoint.py` as a
subprocess per operation, and every such process started ACL2 **twice**:
`Store.acquire()` decoded the metadata on a process-wide framing session it
opened itself (`frame_bridge.session()` with no bridge), then
`open_live_store` started the recovery bridge, which replaced it. Each start
replayed the whole boot, `include-book "books/replay"` and three attachment
books then `ld` of five host files: 176 files, and on the laptop no compiled
file for any of them (the certificate cache's `.fasl`s are Linux SBCL's), so
every definition was compiled again at every start.

| cost | measurement |
|---|---|
| 1. bridge boots per module | 124 (test_checkpoint), 136 (test_store), 150 (test_store_corruption); 9 in the single test `test_no_marker_is_a_distinct_outcome` |
| 2. seconds per boot | 4.3 s quiet laptop (replay 1.5 s, host `ld`s 1.8 s, rest the other includes); about 15 s under the swarm's contention (1,857 s / 124); 6.6 s store, 7.5 s BP ingress on hbox with fasls |
| 3. ACL2 processes outside the pool | every bridge: bare `acl2`, SBCL's 32,000 MB dynamic space, no slot (PKT-162), so six lanes' tests shared 12 cores without bound |

Boots times seconds per boot is the whole module: 124 × 4.3 s = 533 s
against 520.6 s measured for test_checkpoint on the quiet laptop, and the
single test ran 39.6 s of which the nine boots were 39 s. Work per call and
harness waits were under 10 % of any store module. Native: test_bp_node_native
started the Python BP ingress bridge 120 times to author its requests
(120 × 7 s ≈ 840 s of the 870 s the bp-n16-prod lane measured for 27 tests on
this tree); its 497 native image invocations and its fixed sleeps (the busy
backoff, 5.5 s × 3 + 2 s + 1.8 s × 2, about 22 s) are the rest.

## The fix

- `tools/bridge_image.py`: the boot forms are named once (`STORE_FORMS`,
  `OWNER_FORMS`, `BP_INGRESS_FORMS`); the image is those forms sent through
  `Acl2Store`'s own call path (an ACL2 error in any form fails the build as it
  failed the boot) and `save-exec`ed to
  `build/bridge-image/<kind>-<digest>/fn-bridge`. The digest covers the forms,
  the source, `.cert` and `.port` bytes of every file the forms reach through
  `include-book` and `ld` (176 for the store), and the launcher chain (scripts
  by content, core and runtime by path, size and mtime). A changed input is a
  new directory; two images per kind are kept. Built under a lock, once per
  closure digest: 6.2 s laptop, 9.7 s hbox. Boot from it: 0.15 s laptop,
  0.23 s hbox. `FN_BRIDGE_IMAGE=0` boots from the sources. A failed build
  raises; there is no silent slow fallback.
- `Acl2Store` (tools/run_store.py) boots the image for its `BRIDGE_KIND`;
  `Acl2Owner` and `Acl2BpIngress` name theirs and no longer replay their
  includes. The environment is `acl2_environment()`: the certification
  settings and `acl2_slots.apply_heap_cap` (8,000 MB on darwin).
- Pool (PKT-162): a bridge takes an `acl2_slots` slot. One slot per process
  tree: the holder publishes its pid in `FN_ACL2_SLOT_HOLDER`, and a child it
  starts while holding (the tests run the CLI under a live bridge) shares the
  slot rather than waiting, which would deadlock a pool full of parents.
- One ACL2 per CLI process: `open_live_store` and `command_anchor` start the
  bridge first and `Store.acquire(bridge)` decodes the metadata on it;
  `durable_records` uses the recovery bridge. 124/136/150 boots became
  79/115/142. `command_post` still opens the framing session to bound its
  payload read before the store (the owner path needs it); not changed.
- Two dev regressions found booting the bridge, fixed because no store test
  could run without them: `host/store-node-host.lisp` calls
  `fn-rcl-existing-action` (books/store-reclaim) without including it (the
  bridge failed at `fn-store-sn-prepare`), and `tools/run_store.py` used
  `json` without importing it (five `test_anchor` command tests).
- The rule: `tools/test_budget.py` runs each module in its own process with
  per-test timing, reports every module's seconds and slowest tests, and
  terminates a module still running at its budget (default 300 s;
  `tests/test_budgets.json` may lower, never raise; `--budget` over 300 is
  refused). Exit 0 all passed within budget, 1 test failures, 2 over budget,
  3 both. `make test` runs every module through it; `make test-modules
  MODULES=...` runs a chosen set. Its teeth are `tests/test_test_budget.py`
  (a sleeping module is terminated and reported over, failure and budget
  exit codes stay apart); `tests/test_bridge_image.py` covers the closure,
  the digest moving with a closure file, and the shared slot (a child of the
  holder gets the only slot; a stranger waits). Both are in `make
  tooling-test`.

## Before and after

| module | before | after (`tools/test_budget.py`) |
|---|---|---|
| test_checkpoint (7) | 1,857 to 1,901 s contended; 520.6 s quiet laptop | 23.2 s, slowest test 9.7 s |
| test_store (21) | 2,006 to 2,088 s contended | 26.4 s, slowest 2.6 s |
| test_store_corruption (7) | 2,280 s contended | 31.6 s, slowest 14.1 s |
| single test cold (`test_no_marker…`) | 39.6 s quiet | 1.9 s (plus a one-time 6 s image build after a closure change) |
| test_bp_node_native (27, hbox) | 870 s (bp-n16-prod, same tree) | 113.9 s, slowest 21.4 s (18.5 s of it the busy-backoff sleeps) |

All pass. The before contended numbers are the python-store-f8 runs; the
quiet test_checkpoint and single-test numbers are this lane's, same laptop,
same tree, before the change. The after laptop runs shared the laptop with
the other lanes of the night. Neighbour modules on the laptop after the
change (`after-laptop-neighbours/`): test_store_config 14.2 s (was 1,356 s),
test_media 20.3 s (574 s), test_bp_receive_faults 40.5 s (1,438 s),
test_store_fault_matrix 47.2 s, test_acl2_bridge, test_index_cache,
test_host_boundary, test_store_node_host all OK.

Logs and SHA-256s: `test-latency-2026-09-25/SHA256SUMS`; hbox module log
`hbox/test_bp_node_native-after.log` `bce7493741e23b7d…`, run by
`hbox/hbox-native.sh`, boots by `hbox/hbox-boot.sh`.

## Not done, and why

- The Python owner bridge (`Acl2Owner`) does not boot on dev:
  `host/owner-host.lisp` now needs the native build's closure
  (`fn-rcon-ocfg-io` from books/records-concrete-owner, the `fn-octets`
  stobj for `fn-owner-prepare-buffer`). Its image fails where its boot
  failed; the owner test modules (test_owner, test_post, test_feed, ...) are
  red on dev for that reason, not measured here.
- `test_anchor`: one failure remains, `test_no_other_module_imports_cryptography`
  (tools/fn_verify.py and tools/v0_matrix.py import `cryptography`); not
  this lane's.
- `tests/test_feed_journal_live.BookBridge` still starts a bare ACL2 outside
  the pool; `make check`'s `tools/host_check.py` boots one ACL2 per host
  file; neither was measured.
- The native busy-backoff sleeps are the protocol's wall-clock backoff; a
  shorter configured backoff for the tests is a product change, left.
- `make check` in the worktree: only `planning/ledger.*` stale (generated; the
  deputy regenerates on merge).
