# W15 native existing-store recovery

Scope: the existing-store recovery path in `fnn-acquire` and `fnn-recover`.
Fresh initialization is intentionally outside this packet.

The previous native differential record says that removing `staging/` made
Python fault and native `status` succeed.  At the integrated source revision,
`fnn-acquire` calls `fnn-safe-directory` for `staging/` before it opens the
lock, so that result is stale-image or stale-harness evidence.  The packet
must reproduce the current image result and preserve the older record as a
historical finding rather than treating it as a current behavior claim.

The remaining implementation gap is current: native recovery enumerates and
reports staging entries, while Python calls the already-certified
`fn-sn-sweep-staging` decision.  Native recovery will enumerate at a limit
supplied by the ACL2 store-sweep interface, give the complete bounded
observation to that interface after replay and its five barriers are ready,
and unlink only names the interface returns.  A `.stage-` name is removable;
an unknown name remains reported.  A directory above the modeled observation
limit faults before an unbounded host list is built.  An unlink error after a
selected decision is uncertain and fences the store.  Read-only opens report
their bounded observation but do not mutate it.

`fn-sn-sweep-staging` already is the logical transition for this action: it
returns the removal list and preserves the logical store.  The host will call
that exact subject through `fn-store-sn-sweep-staging-list`; it will not copy
the prefix, held-name, or phase decision in raw Lisp.  The list form avoids
using LF as a filename delimiter at the native boundary.

Runtime evidence will exercise: a current-image missing-`staging/` fault; a
recoverable `.stage-` orphan with an unknown neighbor retained; over-limit
staging observation; a post-unlink injected EIO, named as a post-success test
observation; and SIGKILL at that source-pinned cut followed by a separate
process recovery.  These are process observations, not a general physical
crash or adapter-equivalence proof.
