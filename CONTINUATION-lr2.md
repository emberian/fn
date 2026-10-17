lock-triage-r2 verdict table (origin/dev d3b392c32)
REAL: LIVE-RECONFIGURE-IO(20 keys) LIMIT-HISTORY-REOBSERVE(3+shared lstat E) COMMIT-INLINE-LOG-IO(5) LISTENER-RECONFIG-STDOUT(2) OFFLINE-ONESHOT-HOLD(4) BUDGET-INSTALL-STAT(1) FD-TEARDOWN-UNDER-LOCK(4) TLS-PROBE-UNDER-INIT-LOCKS(4)
MODEL-GAP: executor condition-wait E(2), R9 mux-loop await(2), R3 naked csp pread(1), unresolved binding(1), fnn-log-durable-lock "?"(4)
UNSURE: cold extent realizer pread/read-stall/read-entry O+E (8), fn-pgs-fill-realize O+E (2)
r2b: checker commits done (condition-wait wrapper 653f4f49d, owned-fd R3 394ef83fb, XDURABLE third). Remaining: part 1 settle UNSURE (a) payload realizer reachability, (b) fn-pgs-fill-realize O/E.
r2b: lane closed (all checker commits, feed-reply item and pgs-fill-reentry item pushed).
