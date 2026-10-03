# Decision: move as much of the host as possible into ACL2 (ember, 2026-10-03)

ember: "I would like to move as much of the host back into ACL2 as possible! There's no reason to have
THAT much code outside the TCB. I think that was just a design/planning mistake we made going into it."

The founding rule "ACL2 owns every decision; host code performs I/O and calls it" is AMENDED:
ACL2 owns decisions AND coordination (sections, handoffs, lifecycle, failure scopes, receipts, retries,
deadlines, scheduling). The host keeps only thin, named primitives (syscalls, sockets, file descriptors,
thread/mutex/condition primitives, the clock, crypto/compression FFI), each specified as an oracle step
of the host model with a named assumption. Today: ~67k lines of SBCL host (host/*.lisp ~26k,
host/native/*.lisp ~41k) with ~290 lock/thread sites, covered by no theorem.

Consequences for live work:
- Generated protocols (FAILURE-SCOPE, DEF-ENTRY, DEF-COMMAND, DEF-HOLDER) generate executable ACL2
  (logic mode, guard-verified), not host Lisp, wherever the primitive interface allows.
- The host model (COMPOSITION's HM book) is the specification of those primitives; the code that runs is
  the code that is proved, and "the host is the model" shrinks to "the primitives behave as specified".
- LOCK-CHECK polices what remains hand-written; its enclave grows as code moves.
- Hand fixes in flight (HOST-LIFECYCLE, OWNER-OFFLOCK, sweep lanes) continue: they fix live defects now;
  where a fix is coordination logic, write it in ACL2 if that is not much more work.
To record in planning/decisions.md as a D-number when the architecture plan (TCB-SHRINK) is agreed.
