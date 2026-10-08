# Group commit phase 1c — source trace at 7895556b8; draft updated 2026-10-08
The ordinary committer barrier is already off the owner mutex; the inline path is not.
There is also an owner-held `:full` fallback inside the committer's drain.
No host/book changes, certification, network, commits or pushes. O = `host/native/owner.lisp`,
I = `host/native/io.lisp`; book names refer to `books/`.
## Current committer path
- `fnn-owner-committer-loop` (O:5236,5266) calls `fnn-owner-commit-pipeline`.
  Its commit-lock scope ends at O:5261, before that call.
- START is a `:commit` quantum (O:`fnn-owner-commit-pipeline`:4926–4950).
  `fnn-section-envelope` (O:2658) holds `fnn-owner-service-lock` (owner O).
  `fnn-owner-commit-start-locked` (O:4408,4448) drains at most BMAX submissions;
  `fnn-log-seal-capture` (I:9372,9396) captures the append, resets the open batch,
  and sets syncing without writing. The model append precedes physical write.
- After START releases O, `fnn-owner-start-syncer` (O:4831,4848; called O:4970)
  executes `fnn-owner-batch-job` (O:4652). No scheduler quantum is held by it.
  `fn-oqw-phases` (owner-queued-work:57) orders intents/extend/append/fence/resolutions.
  `fnn-owner-batch-effect` (O:4612–4618) realizes that order off O.
- `fnn-log-sync-sealed-batch` (I:9446,9455) calls `fnn-log-fence` (I:8046).
  At fdatasync (I:8064), neither O, gate mutex, commit-lock, nor log kernel lock
  is held by the syncer. The kernel lock is acquired AFTER return (I:8072).
  Thus even the old comment “SYNC under the log lock” is stale for the syscall.
- START-NEXT is a separate `:commit` quantum (O:5048), captures :next (O:5066),
  then drains with `:seal nil` (O:5068). It prepares ONE next batch, no append.
  `fn-ocp-wake` (owner-commit-pipeline:150) requires staged/not returned/queued/
  no next/not blocked. The pass-bound is 4 (same book:70,187); excluded waiters
  inhibit further preparation once that budget is spent, not immediately.
- The one-sync limit is real: `fn-lgk-append` (store-log-kernel:103) refuses
  any nonempty in-flight batch. COMPLETE seals next only at O:5171–5177.
- Exception: `fnn-log-take` (I:9144,9170–9176), reached by the drain's Store
  attempt (O:`fnn-owner-drain-one`:4291–4295), handles `:full` by waiting for
  the old sync then `fnn-log-commit-open-batch` (I:9217,9235), still holding O
  in START/START-NEXT's `:commit` quantum. `fnn-log-await-sync` (I:9364) releases
  only the log mutex while waiting. The fallback fdatasync holds O, not the
  log kernel mutex. An octet-full batch can take this branch before BMAX drain
  iterations end; this is a traced conditional path, not a measured frequency.

## Inline path, admission and visibility
- `fnn-owner-commit-queued-locked` (O:4756,4770) runs START/job/COMPLETE in the
  caller's SAME quantum under O. It does not publish an OCP in-flight phase.
  Callers: bound submission (O:5360), BP transit submission (O:5431).
  Actual classes include control/operator `:poster` (O:5624,5666), hybrid
  control (`host/native/hybrid-control.lisp`:166), and BP `:transit` (O:2766;
  `host/native/bp-app.lisp`:135,143,242). O:4747's control-only shorthand is stale.
  Here the note's owner-held barrier claim IS true. All other quanta wait
  for O/the busy gate, including readers, inspect and the committer.
- Off-owner barrier admission: `fn-ocs-next` (owner-commit-steps:164–175)
  admits inspect (alternating), commit, reader; blocks control, poster, transit.
  `fn-ocp-next` delegates (owner-commit-pipeline:160); host uses fn-otm-next /
  fn-otm-commit-event (O:2334,4802), equated to OCP (owner-time-model:826,832).
- There is NO `:post` scheduler class. Served NNTP POST uses `:reader`
  (`fnn-owner-handle-chunk`, O:5691; read entry O:6527). It can queue during
  a barrier (O:6650–6665), subject to `fn-otm-admit-post` (owner-time-model:606)
  shedding slow/stalled/full disks. Control `:poster` is blocked, not NNTP POST.
  BP/normal peer traffic is `:transit` (O:`fnn-owner-serialized`:3071–3080).
  Peer reads switch to reader only while shedding (owner-time-admission:
  `fn-otm-peer-read-class`:188, `fn-otm-peer-read-proceeds-p`:195; O:6566).
- Reader capture precedes drain (O:4939,5066); `fn-ocv-reader-view`
  (owner-reader-view:79) selects the completed prefix. Actual read/capture
  uses `fn-ocfg-at-reader-view` (host/owner-host.lisp:403,4583).
  Reader view advances at COMPLETE (O:5168), after sync AND feed resolutions;
  the lag is deliberate safety, not readers waiting for fdatasync.
- POST returns :await (O:5715,6661); batch job resolutions follow fence
  (O:4614–4618). COMPLETE acknowledges via `fnn-log-batch-finish` (O:4728;
  I:9347), emits deferred log lines then releases replies (O:4735–4740,
  `fnn-owner-commit-release-member`:4669). `fn-ocs-told-at-drain-p`
  (owner-commit-steps:480) permits early non-record-dependent refusals only;
  duplicate/conflict/generic refused stay held (same book:469–493).
- Failure: O:5187–5193 passes BOTH batches to :stop; complete-locked fences
  the store (O:4709), releases uncertain (O:4724), exits 3 (O:4726).
  Today's second batch is prepared, NOT appended. Raw phase theorems alone
  do not link a :fenced report to durable bytes; that composition is essential.

## Lever and implementation plan
1. Retire inline jobs and the hidden :full flush, preserving R2: bound/BP
   operations become ACL2 continuations across commit-then-submit quanta.
   Change complete-bound-submission, complete-bp-transit-submission, their
   callers and commit-queued-locked; preflight drain capacity before taking
   a submission. Full means seal/yield/resume, never I/O under O.
2. Extend the existing kernel/route, not a second commit model: keep ONE sync
   request and ONE frozen next batch. Add append-behind with a captured end
   offset/chain head and separate written versus durable frontiers. Preserve
   fn-olr-linkp's committed/inflight/next partition and fn-ocv's two captures.
   Change log seal/capture/append/fence/collection and batch-job/pipeline;
   execute next intents then its append off O while current fdatasync runs.
   A return covers only its issue-time prefix; never infer coverage of racing
   appends. Serialize positioned writes, isolate aligned ranges, pre-extend
   safely; retain per-generation buffer custody and failure of both batches.
   Failure is sticky: a late successful sync cannot erase an append failure.
3. Preserve OCP next-opens/start-next/in-flight-admission/complete-only-after-
   barrier and OCS release theorems unchanged. Keep one OUTSTANDING SYNC:
   fn-ocp-sync-only-when-none-in-flight does not need weakening for append-
   behind. Add new append-behind/fence-prefix refinement and multi-write crash
   relation, reducing to existing fn-lgk-relp for one pending write. Existing
   append/fence theorems remain about their original primitives; the new
   operations need stronger composition proofs, not edits making old claims false.
4. Membership means an ordered interval at a captured issue cut, not “all
   records since a barrier returned”: k+1 may already be written at that return.
   Today's fn-olr-take (store-log-route:125) exempts count=0 from caps; OMAX
   counts packed 4+record bytes (same book:81), not whole padded log bytes.
   Draft requires a profile-consistent single-record fit and encoded-length
   preflight. Validate profile consistency; do not truncate an oversized record.
5. Phase 1c replaces the premise-shifted contract. The KEYSTONE is now
   fn-ocp-gc-linkedp-initially / fn-ocp-gc-linkedp-preserved; reveals is a
   step-output COROLLARY. Neither successor-linkedp nor reveals-okp guards STEP.
   fn-lgk-append-behind extends the existing kernel by a frozen-appended-next
   bit and a codec-derived write plan; committed/inflight/batch still partition H.
   Its new statements preserve that partition, monotone D and ACK <= D.
   fn-ocp-gc-host-step composes existing OCP, OCVM, OQW, OLR and kernel calls.
   Next append waits for current :fence; that fence commits only A. COMPLETE
   ACKs A, advances fn-ocv, promotes B and resumes its saved job phase. The
   native fnn-owner-run-job must not restart B's already completed append.
6. All 9 positive witnesses and 8 ground-negation/must-fail teeth passed on
   persvati (gc-pipeline-1c); 325 reached-state/event combinations also passed.
   Every hypothesis has a positive witness. The phase-removal tooth retains
   linkedp and both member lists in a reached :done state. Profile removal
   demonstrates packed 5 bytes fitting OMAX=5 while its log encoding is 512.
   See RESULTS.md for commands, per-witness results, vacuity audit and fixes.
   No keystone was loaded/proved, no certification or production code changes.
   Still owed: native dispatcher/generation/custody wiring, multi-write crash
   refinement and actual renderer provenance; this is a proposed core contract.
