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

## Source followup: generation, phase and operation dependencies

For a reused FREE commit row with generation g, `fn2-commit-start` computes
`owner-gen = g+1` before acquiring any lease. The future journal borrower is
exactly `(commit-kind, id, g+1)`. `fn2-checkpoint-commit-bind-pools` reads that
explicit borrower tuple and stores its pool handles; neither it nor
`fn2-commit-resource` compares borrower generation with machine generation.
`fn2-commit-bind-extent` later changes only extent/epoch/counter, retaining those
pool bindings.

A ticket scan yield changes only the construction scan cursor and returns
:exhausted while the machine remains FREE/g. The direct unwind passes g+1 to
`fn2-checkpoint-commit-return-pools`; its FREE case intentionally accepts that
exact loan generation. All four leases return to the retained master, pool
bindings clear, and machine generation/batch stay unchanged. Retrying therefore
uses the same would-be g+1, not another increment. The new actual COMMIT-START
fixture exercises this source path with an explicit synthetic prior-batch marker.
It has not been executed.

On ticket success, commit-start writes COLLECT and generation=owner-gen together.
Accepted NOTIFY exhausts ACKs then moves to DRAINING; refused DROPPING likewise
moves to DRAINING after settlement. The drain passes the actual row generation,
which now equals the borrower generation. Its pending/fence tests precede the
four release stages. UNCERTAIN never hands back the bundle. No generation/phase
mismatch was found in this source trace; no runtime qualification is implied.

The footprint review found and repaired missing future/future-windows tables on
both maintenance submit operations, whose shared planner seam can bind/borrow the
future bundle. The public `fn2-commit-admit-txn` declaration now includes those
read dependencies because ordinary failure cleanup consults the loan cookie;
its frozen gate still excludes future mutations. Begin, step, empty completion,
poll, lifecycle dispatch and release-pool already declared them. Internal
commit-start/reserve helpers are not separately registered defcost operations;
the two submit operations are their maintenance arm entrypoints. The existing
seal operation's `(:layers :b)` declaration already includes the registered
future children. C master arms invoke these B operations directly, so this
followup adds no hidden C carrier or wrapper state.

All four isolated coordinator/recovery fixtures and both new consumer macro
books now import B* directly. The existing structural rewrite tool's four text
fixtures pass, and its six-file explicit-import check reports zero missing
imports. These are Python source-tool controls, not ACL2/runtime execution.

## HELD consumer admission, 2026-11-14

The exact 30368c191 HELD32 attempt stopped with exit 75 in dependency
`books/checkpoint`; no `checkpoint-future-resources-unit` forms were sent.
All 17 unchanged qualified dependencies installed with zero misses. Fourteen
changed parents were explicitly source-loaded; no certification was launched.
The refused event was `FN2-CHECKPOINT-REF-CLEAR-BUILD-PRESERVES-TYPE`, 347
prover steps. Its arbitrary logical row argument reached four raw setters
without the index check required to preserve concrete column shape.

Source repair 7628b96e1 preserves the original generated TYPE/WFP/ROWS claims
and valid-index behavior: invalid indices return the unchanged carrier.
`tests/checkpoint-clear-build-unit` adds actual upper-bound/negative-index
unchanged-view and valid four-field clearing controls. These controls and the
repaired admission remain unrun. The original HELD controls are unchanged.

Total source-loading cost was 120.71 seconds / 14,122,367 prover steps; this
is dependency proof cost, not the 347-step refusal. Cost reduction remains
open before repeating that prefix. The detached attempt stopped its own
server; outer 540924, server 540998 and ACL2 process group 540999 were all
absent on the exact PID audit. Its named 2 GiB reservation was released.
