# feed-idle-wake continuation
- Read feed-service.lisp worker loop (fnn-feed-worker-loop) and pull-service.lisp worker: both already wait on commit signal (fnn-feed-idle-wait/poll-wait, fnn-pull-idle-wait/ready-wait) with ACL2 bounds >=10-50ms. No spin found by reading yet.
- gate pick (owner.lisp fnn-owner-gate-pick) runs once per enter-with-turn-null and once per leave; 35k picks/s = ~17k quanta/s, so a thread enters quanta in a tight loop.
- Existing idle harness: tests/test_native_feed_idle.py (holds counted by FN_OWNER_MEASURE=1).
- Asked E4 (abb504c768bcbc597) for call stacks. Awaiting.
