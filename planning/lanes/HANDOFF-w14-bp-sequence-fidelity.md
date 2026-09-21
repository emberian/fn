# Handoff: W14 BP sequence observed-file fidelity

Commit `e022a70` replaces the restart-phase-bit checkpoint in
`books/bp-sequence-fidelity.lisp` with an observed-final model and proves
`fn-bpn-sf-admissible-trace-returned-sequences-unique`.

The theorem tracks values returned by `fnn-bp-reserve-sequence`, including a
return lost with the process, rather than only later authored bundles.  The
model calls `fn-bpn-sequence-recover` and `fn-bpn-sequence-reserve` through
named bridge functions and records the native return accessor as the
`:return` transition.  It retains no rename or directory-barrier phase bit
after restart.  Before confirmation an old final may be retried or a new final
may burn a value; after confirmation, a continuing recovery is conditional on
the explicit confirmed-frontier admissibility predicate.

Both final ACL2 roots certify in
`certify-20260921T091031Z-26507`.  See
`planning/evidence/bp-sequence-fidelity-2026-09-21.md` for exact per-book
results, digests, native build, SIGKILL restart result, and the remaining
raw-I/O correspondence assumption.

Integration should cherry-pick `7dd156d` and `e022a70`, retain the
fidelity book/test roots in `Makefile`, and let root update PRF-045 and the
shared assurance registry.  No host runtime file or shared registry was
changed in this lane.
