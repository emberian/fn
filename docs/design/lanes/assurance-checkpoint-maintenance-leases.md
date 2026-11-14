# Actual maintenance lease consumers — source milestone

Maintenance allocation and final-member staging now use future role0 admitted
before the held source cut. `fn2-checkpoint-staging-claim` binds the exact retained
candidate/token/master owner, checks capacity, resets the existing workspace and
marks its actual future borrowed bit with the same master borrower tuple. There
is no HAND-to-self or fresh pool reservation. Allocation begin derives candidate
identity from that carrier; final begin checks its candidate before acquisition.
The shared one-flight control retains the exact workspace/candidate identity.
Pack, planner admission and actual persisted lifecycle dispatch recheck the loan.

Exact settlement or an actual empty terminal scan returns the same staging
identity and clears its borrowed marker, retaining the master-owned pool lease
for reuse. Central future cleanup therefore observes staging as busy before
handback. Ordinary retirement staging still uses its existing fresh reservation
and pool release; its ACK/settlement path is unchanged.

The actual frozen role6 commit-start path now borrows future roles1..4 atomically
and binds the existing three commit I/O rows and scratch slot. Foreground uses the
existing reservation path. If the bounded ticket scan yields, admission returns
all four exact leases directly and clears those bindings before retry; it does
not invoke the generic reverse-order free loop. A partial ownership transfer
stops with uncertainty and retains its actual prefix.

Normal maintenance drain defers its first three releases. At its fourth stage,
`fn2-checkpoint-commit-return-pools` requires actual pending/fence counts zero,
free admission-unwind or draining phase, exact borrower generation, and all four
actual I/O/scratch bindings. It hands all four back to the retained master, then
clears the existing bindings. Another maintenance batch backpressures until that
handback. Parent publication additionally requires journal roles1..4 unborrowed.
Commit arm bodies, ACK ordering and foreground pool-release behavior are unchanged;
only the affected operation footprints are widened in commit-arms.lisp.

Prepared source controls reserve the actual future bundle, exercise same-owner
staging loan/busy cleanup/empty handback, check all-four journal retention and
return, and reject stale generation or pending/fence handback. Their freeze and
empty-scan premises are explicitly synthetic, not durability or ACK witnesses.
Existing coordinator controls now acquire the actual future bundle first.

Source-only: form balance, diff whitespace and named-file secrets checks run
before commit. No ACL2 admission, guard/preservation proof, certification, simulator,
native or remote computation was run. Composed real writer/drain, mutation and
resource-exhaustion controls remain pending qualification. This change activates
no checkpoint phase2, publication, serving, FREE or allocator reconstruction.
