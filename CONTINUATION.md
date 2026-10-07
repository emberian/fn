# lock-owner-class continuation (2026-10-07)

Branch lane/lock-owner-class, pushed; gate `python3 tools/lock_discipline_check.py --check --json` vs origin/dev a49a8eb09: 15 keys gone, 0 added. tests.test_lock_discipline_check: 271 tests pass.

Ready (see each item's sha and notes): LOCK-R2-LIMIT-HISTORY-REOBSERVE, LOCK-R7-REOPEN-LOG-ERROR-SWALLOW, LOCK-R1B-RESPONSE-WINDOW-CLOSE-DIRECT-O, LOCK-R7-CUSTODY-TRACE-SELECTOR-SWALLOW, LOCK-R7-ESCALATION-FAILURE-SWALLOWED, LOCK-R1-REOPEN-LOG-GLOBAL-READ, LOCK-R7-STOP-HOOK-FAILURE-FENCE, LOCK-R2-FD-TEARDOWN-UNDER-LOCK.
Checker model changes (tools/lock_discipline_check.py, each with unit tests): binding_only_specials, escalation_wrappers + dolist escalation tail, close_hook_fences, nonblocking_leaves, nonblocking_close_sites.
Left alone by instruction: LOCK-R2-LIVE-RECONFIGURE-IO and LOCK-R2-COMMIT-INLINE-LOG-IO (Deputy P, ACL2 phase models).
Owed to the coordinator: baseline row R1b|fnn-owner-log|*fnn-owner-deferred*:unlocked-write is stale (--lower-stale, not run here); natives_owed are in the item JSONs.
