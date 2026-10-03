# RECLAIM-RETENTION continuation (2026-10-03 wind-down)

Branch lane/reclaim-retention, head 2f27ae7292dd (base origin/dev 4aa332295). Sent to runner a8c1198f67920c411.
Worktree build/lanes/reclaim-retention. Ledger: X01, S050 (ready), X11, X12 (in-progress, code done).

## Done (REPL-admitted on hbox; NOT certified as a set)
- X01: fn-rcl-store-holders BP slot = live non-archive (:forward) pins of the Store ledger mapped subject->msgid via
  archive bindings (fn-rcl-bp-holders, fast alist, one probe per candidate). Keystones
  fn-rcl-store-holders-never-reclaim-a-forward-pinned-article, fn-rclp-ctx-never-releases-a-forward-pinned-article.
  Teeth in tests/acl2/store-reclaim-holders-tests (positive via the Store's own retention step, :release removal,
  archive/other-subject/other-article removals, labelled mutation dropping slot, expiry, status held count).
  Feeds/BP slots are now Message-ID keyed alists (books/store-reclaim.lisp; test literals updated in
  store-reclaim-tests, expiry-tests, store-reclaim-pack-tests, store-reclaim-stream-tests). Header rewritten,
  reader-pin slot empty by stated reason. PRF-088 note updated.
- S050: fn-rclp-ctx-free + host entry fn-owner-orc-ctx-free; status tally frees via fn-rcl-holders-free.
- X11: books/store-reclaim-owner-holders (fn-rcl-owner-feed-holders, fn-rclp-ctx-with-feeds, keystones
  fn-rclp-owner-ctx-never-releases-a-queued-article/-forward-pinned-article); fn-owner-orc-capture returns 13 values
  (13th = feeds), fn-owner-orc-ctx takes feeds; fn-owner-feed-octets refuses a tombstone (fn-ofa-reclaimed-publication,
  books/owner-feed-article).
- X12: books/bp-payload-gate (PRF-1247 claimed + registered): fn-owner-workflow-request-plan (bp-obligation request)
  and ION attempt/ADU gated: :forward-pin-not-durable / :article-reclaimed. Replay deliberately ungated. Specs/docs updated.
- Measurement filed: planning/evidence/reclaim-retention-holders-2026-10-03.md (index committed).

## In flight (harvest)
- cert HARVESTED: run-20261003T020256Z-76e2 (certify-20261003T020756Z-2981857) PASSED 64/0 at ce8cf421d-era head; cite with evidence_manifests.py add. Was: `farm.py wait hbox run-20261003T020256Z-76e2` (affected-by store-reclaim, -owner-holders,
  bp-payload-gate, owner-feed-article, native-status-columns). Prior run run-20261002T231213Z-2c7f was 551/552
  (the red store-reclaim-stream-tests is fixed in ce8cf421d).
- fast checks: hbox /tank/fn/scratch/reclaim-retention-check.log (iface, host_check --books/--load, ledger, reach, check-fast).

## Next, in order
1. Harvest both; fix reds forward; cite manifest (evidence_manifests.py add RUN).
2. Confirm arena-forget's driver edits (capture length 13, ctx feeds arg, orc-ctx-free after the walk in dry-run and pass).
3. Natives: (a) reclaim with expiry over an article with a live :forward pin keeps it; after receipt or
   `carry drop --abandon` the next reclaim takes it; (b) workflow retry after an unrelated reclaim sends original bytes;
   (c) request after pin release+reclaim refused reason=forward-pin-not-durable. RSS across 50 native reclaim passes.
4. ION: SWEEP-GATES (a96735a319567bfca) restored tests/test_native_ion_workflow.py + ion_ltp on lane/sweep-gates 257c7e9af;
   extend them for the canonical-pin requirement (undertake via `bp-obligation undertake`, FNWF-only undertake refused).
   X10A/X10B filed to this lane by SWEEP-GATES (explicit-route submit refused before send; bad lifetime answers 3 not 1).
5. Open: offline `store reclaim` reads no feed journal (no owner), stated in PRF-088.
