# W15 native recovery handoff

Head: `f2e6545 proof: admit staging observation bound`, following
`300b984 native: recover staging through ACL2 policy`.

The host anchor is `fnn-acquire` and `fnn-recover` in `host/native/io.lisp`:
missing `staging/` now has a source-pinned exit-4 witness, and writable recovery
passes a 64-entry-bounded directory observation to ACL2
`fn-sn-sweep-staging` through `fn-store-sn-sweep-staging-list`.  Raw Lisp only
marshals and executes ACL2-selected names.  Cleanup starts after replay and the
five established recovery barriers; read-only status reports without deletion.

`run-20260921T085524Z-890a` certified the 32-root owned closure.  A hbox native
image then passed 20 targeted storage/initializer tests; the evidence packet is
`planning/evidence/native-recovery-w15-2026-09-21.md`.

Remaining integration gap: the current differential has one finding because
Python reports `checkpoint=none` and this frozen native image does not yet load
the checkpoint module.  Rebuild after the checkpoint owner lands its post-replay
callback and rerun the differential.  No fresh-init, EEXIST/retry, broad
physical-durability, or all-opening-path claim is made here.
