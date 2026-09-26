# Harness repair 2 (lane harness-repair-2, 2026-09-26, PKT-248)

Base: dev 5203d5aa. Continuation of harness-repair
(planning/evidence/harness-repair-2026-09-25.md, its "Not done" list is this
lane's task). No book changed: no farm run, no PRF, no requirement, no SCN.
Laptop: every test module through `tools/test_budget.py` (ACL2 only through
the pool). hbox: the deployed images of qual-bbf52159
(`/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159...`), this
lane's tree at `/tank/fn/scratch/harness-repair-2/tree`, under
`systemd-run --user -p MemoryMax=24G`; `/tank/fn/node` was not touched.
Evidence: `harness-repair-2-2026-09-26/` (SHA256SUMS).

## Result

| module | where | before (dev 5203d5aa tests) | after (lane) |
|---|---|---|---|
| test_bp_service_native | hbox, fn-host-dtn-developer | 16 tests, 12 FAILED (`0 != 3`), 15.4 s | 17 tests, ok, 17.0 s |
| test_bp_contact_native | hbox, fn-host-dtn-developer | 2 tests, 1 FAILED, 0.3 s | 2 tests, ok, 0.7 s |
| test_bp_service_native | hbox, fn-host-dtn (production) | 16 tests, 16 FAILED, 6.1 s | 17 tests, 7 FAILED (all C10 selector refusals), 6.2 s |
| test_bp_contact_native | hbox, fn-host-dtn (production) | 2 tests, 1 FAILED, 0.3 s | 2 tests, ok, 0.9 s |
| 60 native modules, forward vs reverse | hbox, bbf52159 images | not run reversed | 416 tests each order, identical: same 13 failing tests, same 7 over budget; 1,140 s / 1,131 s |
| test_deploy_gate | laptop | ok, but the dry run's verdict was `violated` (owner fell back to the reader) and the test accepted exit 0 or 1; 28.9 s | ok both orders, exit 0 required, verdict `held`; 28.1 s |
| test_twonode_gate, test_scale_gate | laptop | ok | ok (unchanged; they keep their pinned fallback) |
| test_ledger | laptop | 84 tests ok | 88 tests ok both orders, 10.2 s |
| make check | laptop | 90.5 s (cache off: dev's computation) | 82.2 s cold cache, 72.5 s warm; `make check` green |

Logs (SHA-256): C1 runs `c1-logs.tgz` `25315a01...`, inside it
`test_budget.c1-base-fn-host-dtn-developer.log` `c37bb476...`,
`c1-tree-fn-host-dtn-developer.log` `46440c5e...`,
`c1-base-fn-host-dtn.log` `43d75c3b...`, `c1-tree-fn-host-dtn.log`
`532240d8...`; sweep `sweep-logs.tgz` `1002f9be...`, inside it
`test_budget.fwd.log` `7080c61a...` and `test_budget.rev.log` `8e6c3ac9...`.
Image: bbf52159's `image.sha256` (the qual record).

## 1. C1: the outage is an outage again (harness)

The outage cases ran `bp-service run 127.0.0.1 1 ...` and expected exit 3 and
`BP forwarding retained reason=uncertain`. Since 78992f89 a connect that never
produced a socket is `:failed` (host/native/bp-service.lisp, the transfer's socket-error handler:
`(setq outcome (if socket :uncertain :failed))`;
specs/bp-node-machine.md "A connect that never produced a socket reads
`:failed` (no octet left; ACL2 requeues the job); any failure after the
connection exists stays `:uncertain`"), so twelve service tests and one contact
test stopped at `0 != 3` before reaching what they test (recovery fences,
clock domains, namespace corruption, expiry, duplicate and conflict).
Classified harness: the expectation is older than the contract; no behaviour
changed.

Repair (b416370e): `tests/native_process.AcceptThenClosePeer`, a loopback
listener that accepts each connection and closes it before any transfer
completes, lives for each test (the route is durable in the journal, so
resume and the contact tick reach it too). A socket exists, the transfer is
`:uncertain`, exit 3 and reason=uncertain, exactly the regression the tests
were written against; each outage test asserts the peer counted a connection,
so a return to the refused-port shape fails. No expected answer changed. The
new contract has its own test,
`test_connect_without_socket_is_failed_and_requeued`: a bound, never-listening
port (`refused_port`) gives exit 0, `BP queue accepted`, no reason=uncertain,
three lifecycle records, and on resume `BP queue recovered jobs=1` (still
queued), exit 0, with no connection reaching the peer.

On the production image the seven remaining failures are all
`... is a developer-image selector; this production image does not start with
it` (exit 5): the four qual-bbf52159 classified as C10 (prelink, send core
fault, transport-uncertain cut, visible clock domain) and three that C1 had
hidden (append frontier, cleanup barrier, visible final: they set
FN_BP_SERVICE_TEST_FAIL_SECOND_LIFECYCLE_ENUMERATION or
FN_IMMUTABLE_PUBLISH_TEST_FAIL). Not touched, per the brief; the production
image refusing them is the intended behaviour.

## 2. Reverse-order sweep of the native modules (no leftover found)

The 58 modules of qual-bbf52159's module table plus harness-repair's eight
hbox modules (60), forward then `--order reverse` in one `systemd-run` unit
(`sweep.sh`), BP modules on the DTN developer image. Both orders: 416 tests,
13 failing, 10 skipped, and per module the same failing test names, the same
pass and over-budget verdicts (compared by module from the two JSON reports;
reverse order checked in the logs). No test depends on an earlier one's
leftovers, so nothing was changed. test_proof_repl's SessionTests (laptop)
stays a declared sequence.

The 13 failures, the same in both orders, are not order effects and not this
lane's: C10 production-image selector refusals (peer_invite's crash case,
control's selector sweep), the qual's C3/C4 (live_reconfiguration's live
`peer` answer, control's `operator post`), and tests newer than the bbf52159
image (dev is 85 commits past it: peer_invite's peering vocabulary,
control_filing's `423 withdrawn`, fn_web_native's reply outcomes,
consumer_project_bounds' `limit` word, bp_obligation's open reason,
hybrid_author, peer_pull's cursor cuts). Seven modules are over the 20 s
per-test budget on hbox (bp_node 21.4 s, native_checkpoint 36.7 s,
control 125.5 s, history_required 30.4 s, peer_pull 121.7 s,
served_crash_model 131.8 s, state_checkpoint 78.8 s): PKT-248.

## 3. The deploy gate's rehearsal runs the owner it claims (harness)

bin/fn's `run` takes no --store, so the gate selects `tools/run_owner.py`.
The dry run's overlay replaced run_store.py with a fake lacking the owner's
imports; the real owner died on `ImportError: ACL2_RECOVER_BASE_SECONDS`,
the gate fell back to the reader and recorded `entry-point-listening
violated`, and test_deploy_gate accepted exit 0 or 1. Now (590d9fce,
e669c063) `tests/deploy_gate_owner_fake/tools/run_owner.py` serves the fake
store (only the one in the gate's temporary HOME) with POST on and the
greeting `201 fn-nntp fake owner ready`; test_deploy_gate merges it over
`tests/deploy_gate_fake` in its temporary directory. It is the deploy gate's
alone: twonode_gate and scale_gate share deploy_gate_fake and drive feeds and
peering the fake does not have (with it shared, their fallback turned into a
false feed-arrival violation), so they keep their pinned, honest fallback. The
new test requires exit 0, the owner row at rc 0, no reader start at main, the
fake owner's greeting in the transcript and entry-point-listening held; on
dev's overlay it fails (`violated`, reproduced).

## 4. One ledger tree for every checker (PKT-179)

`ledger.load_tree` (1b49bbdc) keeps its in-process cache and adds
`build/cache/ledger-tree/<digest>.pickle`. The digest covers the analyser's
source (tools/ledger.py), the Python version, the module name (a pickle names
its classes by module), the tree root, every input's path and bytes, and the
root list: an entry is valid exactly when its name matches; nothing expires by
time; the directory keeps four entries. A caller that substitutes any analysis
function (a test's mock) or another ROOT neither reads nor writes it;
`FN_LEDGER_TREE_CACHE=0` turns it off. The load runs with the collector
paused (1.25 s to 0.2 s). make check step by step (`check-off.tsv`,
`check-cold.tsv`, `check-warm.tsv`): 90.5 s, 82.2 s, 72.5 s; every step's
stdout and stderr byte-identical to the cache-off run except unittest's own
`Ran N tests in X s` lines. Tests: `TreeCacheTests` in tests/test_ledger.py.

## Not done (PKT-248)

- Seven native modules have a test over 20 s on hbox (listed above); each is
  a campaign of cuts in one test and should be split or examined, not
  budget-raised.
- The native sweep ran against bbf52159 images with a tree 85 commits newer;
  a sweep on an image of the tree would separate skew from behaviour.
- The production-image C10 selector cases in test_bp_service_native and
  test_native_peer_invite fail rather than skip on a production image; the
  qualification classifies them. A module-level rule (developer image only)
  would make the classification structural.
- make check's remaining cost is outside the tree analysis
  (session_depth 8 s, harness_check 9 s, teeth_check 8 s, cite_check 6 s).
