# lock-owner-class continuation (2026-10-07)

Branch lane/lock-owner-class, pushed. Gate: `python3 tools/lock_discipline_check.py --check --json`, base = origin/dev a49a8eb09.

Ready (fix commit, keys gone from --check on this branch, none added):
- LOCK-R2-LIMIT-HISTORY-REOBSERVE: 1073cdd61 (admin.lisp; 3 R2 fnn-list-directory-bounded|E keys)
- LOCK-R7-REOPEN-LOG-ERROR-SWALLOW: a73f78a5e (owner.lisp)
- LOCK-R1B-RESPONSE-WINDOW-CLOSE-DIRECT-O: see item sha (owner.lisp, mux.lisp; R5 direct-O key)
- LOCK-R7-CUSTODY-TRACE-SELECTOR-SWALLOW: see item sha (owner.lisp)
In-progress: LOCK-R7-ESCALATION-FAILURE-SWALLOWED (4 of 5 keys gone; R7|fnn-mux-close-wake remains, checker cannot see the deferred escalation).
Verified, no code change: LOCK-R7-STOP-HOOK-FAILURE-FENCE (fenced as exit 3; blocked_on a checker row).
Blocked, with questions in the item `blocked_on`: LOCK-R2-LIVE-RECONFIGURE-IO, LOCK-R2-COMMIT-INLINE-LOG-IO (design: ACL2 phase models), LOCK-R2-FD-TEARDOWN-UNDER-LOCK (exception rows), LOCK-R1-REOPEN-LOG-GLOBAL-READ (fix works but moves R1b|fnn-owner-log to R1b|fnn-owner-line-after-barrier; uncommitted patch idea: return the rendered line from the serialized thunk in fnn-owner-maybe-reopen-log, then fnn-log-line it after fnn-log-swap-fd).
Natives cannot run here; natives_owed is in each ready item.
