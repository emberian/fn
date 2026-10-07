# lock-io-class continuation (2026-10-07)

Branch lane/lock-io-class (base 8e73e32fe, the tip of lane/lock-owner-class), pushed. Gate `python3 tools/lock_discipline_check.py --check --json` against the base: 6 keys gone, 0 added. tests.test_lock_discipline_check: 280 pass. host_check --read and --load exit 0.

Items (sha, state; each item JSON carries its notes and natives_owed):
- LOCK-R2-PGS-FILL-REALIZE-REENTRY 05c318793, partial: the recursive-lock fault is fixed (fn-pgs-fill-frame reads its tables directly when it holds the extent lock; the limit quantum reads fn-owner-limit-use before taking it; install runs fnn-owner-history-sync-first). The R2 keys on fn-pgs-fill-frame stay: E through fnn-owner-live-reconfigure-locked (Deputy P), O by path-insensitive reachability.
- LOCK-R1B-LOG-SPARE-SLOT-DUAL-ACTOR 217af5ba7, ready: leaf lock SL on the spare slot and its close debt.
- LOCK-R1B-IMMUTABLE-CLOSE-DEBT-UNLOCKED cb032de77, ready: both close-debt lists under *fnn-close-debts-lock* (XCLOSEDEBT).
- LOCK-R5-MUX-SLOT-LOCK-ACCESSOR cedf7f26c, ready: locks[*].struct_slot, verified by verify_struct_slot_locks (unit tests R5StructSlotLock).
- LOCK-R1B-MUX-NEXT-MIXED-LOCKS 7aec511c7, ready: depends on the struct_slot lock above.
- LOCK-R7-MUX-DEFERRAL-LOG-SWALLOW 5d2ed7234, ready: only fnn-mux-reserve; the I/O-loop sinks stay baselined.

Owed to the coordinator: baseline rows now stale (--lower-stale, not run here): R5|fnn-mux-reserve|unresolved:lock object (fnn-owner-service-mux-slot-lock), R5|fnn-mux-reserve|?(fnn-owner-service-mux-slot-lock)->M, R5|fnn-mux-slot-signal|unresolved:..., R5|fnn-mux-unreserve|unresolved:..., R1b|fnn-mux-reserve|fnn-owner-service-mux-next:mixed-locks, R1b|fnn-log-discard-spare|fnn-log-spare:unlocked-write.
Natives cannot run here: natives_owed are in each item JSON.
