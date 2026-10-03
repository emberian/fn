# SWEEP-PEER continuation (wind-down 2026-10-03)

Branch lane/sweep-peer, head 5536e2f08 (pushed). Worktree /Users/ember/dev/fn/build/lanes/sweep-peer.
Sent to runner a8c1198f67920c411 for merge into dev.

## Done (commits)
- 07d21aaaf S005: fnn-ldf-huffman-lengths pads a 0/1-symbol tree to exactly two codes. Before the fix, 38 of 40 crafted payloads came out invalid (zlib "invalid distances set"); after, 0. Raw witness tests/test_native_deflater_raw.sh (old encoder: 353 failures). ACL2 pin in tests/acl2/payload-lz-append-tests.lisp.
- bf0d882c2 S005 follow-up (coordinator ruling): an ACL2-refused encoder candidate is stored uncompressed and the refusal line is printed with a count (io.lisp fnn-log-compress, store-write-host fn-xw-compress). The keystone was strengthened. New entry fn-lzr-append-octets. Developer selector FN_NATIVE_LZ_CANDIDATE_CORRUPT. New native test test_a_refused_candidate_is_stored_uncompressed_and_counted, NOT YET RUN.
  - Answer owed to the coordinator: before the fix, a bad stream was never stored. ACL2's decoder refused it, fnn-fault signalled fnn-store-fault, and fnn-owner-shared-action-locked fenced the store and stopped the owner with exit 4. So a served POST of such an article stopped the node.
- f48cf6e12 S027: the forward session closes ACL2's session exactly once. This also fixes a double close when the socket shut fails. Raw witness tests/test_native_bp_forward_session_raw.sh.
- 9b7508ccb S024 + S052: outbound TCPCL sessions use :refuse-inbound, so an inbound transfer gets XFER_REFUSE No Resources. Transit deferrals map to :busy via the new fn-own-bp-transit-kind-word plus a keystone. :clock-unusable is now deferred. The refuse reason maps to No Resources. New native test test_inbound_offer_on_the_outbound_session_is_refused_not_spooled, NOT YET RUN.
- 32cb8f8a9 S035 + S036: the feed send uses ACL2's per-quantum bound (fn-owner-feed-send-quantum). Loss paths use fnn-feed-loss-backoff. A removed peer's dial plan is empty. Raw harness tests/native_feed_service_raw.lisp passes, and the old code fails it.
- 8ab3cd051 regen (interfaces/ledger/current view) at 32cb8f8a9; checks 0.
- 206623f29 S053: fn-feed-lost applies the retry bound, the delay grows, and the drop gets its own :feed-drop record. The carried twins were updated. All feed books and both test books are admitted in REPL on hbox.
- 5536e2f08 S008 WIP, UNVERIFIED: fn-bpfj-candidate is gated on held payload octets >= declared total. The REPL run never started: the session refused (no cached certificate for books/bp-ingress at these bytes). Restart with `--ld books/bp-ingress` or `--certify-missing`.

## Verified
- certify run-20261003T020247Z-62bf (hbox): 23 passed, 0 failed. Covers payload-lz-append, owner, owner-log, tcpcl-delivery, transit-header-limits and their tests.
- REPL (hbox): every book listed above, except bp-node-fragment-step.

## In flight (harvest)
- natives: `tools/hbox_native.sh status 206623f298d6` (images developer, production, dtn-developer; modules test_native_compression, test_bp_service_native, test_native_raw_scripts, test_native_peering). The earlier native-bf0d882c2a68 run failed at interfaces-check (pre-regen); ignore it.
- farm: feed closure (--affected-by books/peer-feed) is run-20261003T023017Z-cfe4: `python3 tools/farm.py wait hbox run-20261003T023017Z-cfe4` from the sweep-peer worktree.

## Ledger (owner sweep-peer)
- In progress or sent: S005, S027, S024, S052, S035, S036, S053, S008 (WIP).
- Open: S025, S054/S067 (the coordinator approved interim bounds (a)-(c); see the proposal in the S005 message), S026, S051, S068, and the lows S092-S101 and S106-S112.
- Not mine: S006, S007, S023, S037.

## Next steps, in order
1. Harvest the natives and the feed-closure cert. Fix forward on dev anything red: the new native tests are unrun.
2. S008: finish the REPL of books/bp-node-fragment-step and bp-node-fragment-guards (guards may need fn-bpfj-family-coveredp in the theory). Add a test in tests/acl2/bp-node-fragment-step-job-tests.lisp: an incomplete family is not a candidate, a complete one is. Then S026: run fnn-bps-fragment-progress after the ACK flush, and yield between fn-bpfj-step quanta.
3. S052 leftover: the bp-app tally still counts a deferral under refused.
4. Interim bounds (a) pull round deadline, (b) feed dial cap and pump order, (c) bp-node passive session max duration. Each bound is an ACL2 decision, each needs a native, and each spec row must say that fairness is not bounded.
5. S051 (NEWNEWS listing set and quanta), S068, then the lows as a batch.
