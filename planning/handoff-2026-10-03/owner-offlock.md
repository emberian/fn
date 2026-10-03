# owner-offlock (Opus) — wind-down 2026-10-03

## State
- Branch lane/owner-offlock @ d7fe7f5c8474c518ea48bfd9e309b1eab72c423a (base 4aa332295), pushed; sent to runner a8c1198f67920c411 for merge (all-onto-dev).
- READY 1 content: the commit's blocking effects (FNFD intents, log extension, append pwrite, barrier, FNFD resolutions) are ONE off-owner batch job run by the syncer; START/COMPLETE only decide (fnn-log-seal-capture). ACL2 helper books/owner-queued-work.lisp (fn-oqw-start/step/receipt/outcome-of-final; :batch and :frames kinds); books/feed-journal-order.lisp (old/new FNFD orders replay alike). PRF-1245, PRF-1246, HST-033 extended, specs/host.md, docs/operator-internals.md selectors FN_NATIVE_TEST_FEED_FSYNC_MS / _STALL_FILE. A phase's OS errno = :uncertain.
- Checks ran: REPL-admitted (persvati); interface_emit/ledger/reach --strict/host_check --books/secrets 0 on persvati at 151f8bbb9-ish head (last commit d7fe7f5c8 adds only the :frames job); native_cuts verify_post_log_cut_map + native_program_check PASS.
- Repair ledger: r71-F6, r72-F4 = ready sha d7fe7f5c8 (natives pending). S014 open (fsyncs off owner, but still 2/member/peer: coalescing needs a feed-journal.lisp phase-machine change).

## Native runs NOT harvested (hbox)
- AFTER: /tank/fn/scratch/owner-offlock/native-d7fe7f5c8474 (tools/hbox_native.sh status d7fe7f5c8474) — owner_offlock, log, recovery, crash_model, checkpoint (FN_RUN_NATIVE_CLONE=1), owner, slow_disk, owner_scheduler, peering, feed_temporary, state_checkpoint, crash_correspondence; images developer,production,dtn-developer.
- BEFORE baseline: /tank/fn/scratch/owner-offlock-before/native-0ae98328db34 (branch lane/owner-offlock-before 0ae98328d = dev + selectors + measure label ONLY; NEVER merge; worktree build/lanes/owner-offlock-before — remove after harvest).
- Measurement = OWNER-OFFLOCK-HOLD-WITNESS lines (fn-owner-measure `commit` max-us/mean-us vs FN_OFFLOCK_FEED_FSYNC_MS=100) in both test logs; stall witness OWNER-OFFLOCK-STALL-WITNESS.

## NEXT
1. After the runner merges: base on origin/dev; resolve the t45 conflict if the runner did not (committer loop: take t45's, keep `*fnn-owner-measure-label* :commit` binding); drop the inner fnn-owner-shared-action-locked in COMPLETE (t45's gated boundary fences). Harvest the natives above; fix forward reds; report before/after hold numbers.
2. Item 2 F8: accept/SIGTERM loop must not enter a gate — maintenance (cold-reap/maybe-publish/reopen-log/maybe-retire) moves to a maintenance actor using the same job+receipt shape.
3. F7 cold-await (mux stores the dependency, returns to poll; settlement class admissible in flight).
4. F4 / S022: release-extents fresh pread and synchronous realizer under *fnn-extent-lock* -> lease, pread off-lock.
5. Statement barrier (owner.lisp fnn-owner-statement-barrier) + inline commit's job (HOST-LIFECYCLE keeps fnn-owner-commit-queued-locked).
6. S014 coalescing (feed-journal phase machine write,write,sync).

## Taken by SERVED-LIVE (2026-10-03, lane/served-live)
- NEXT item 2 (r71-F8) and item 3 (r71-F7) are done as bridges on lane/served-live (ledger owner served-live): the maintenance worker, and the mux cold poll. The settlement's :control class (F7's second half) and the worker->loop wake are not done.
