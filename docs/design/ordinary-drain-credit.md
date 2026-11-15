# Ordinary B drain credits

Configured ordinary admission binds group `1 + actual B row` to the actual next
batch number and the generation that START will assign. Non-image/unconfigured
profiles retain the existing generic reservation and release path. The group
schedule comes from `fn2-checkpoint-working-credit-configure` using initialized
B table and I/O-row counts and the actual root/future window declarations.

START begins redemption, reserves the existing three journal windows and one
scratch window, and reserves its actual allocator extent before END. All these
steps are unsubmitted and perform no IO. END must succeed before COLLECT,
proposal publication, member admission or any issue. A partial pool failure
returns only retained exact handles, then aborts the fully restored group using
the bound arguments even when no lease was acquired. Extent refusal does the
same. ABORTED-EMPTY permits only an exact same-owner/same-nonce no-IO retry;
completed IDLE remains monotonic and ambiguity does not rearm a nonce.

Unexpected END refusal retains the extent and all credits and stops with
uncertainty. The current producer lacks an end-to-end classification that
would justify empty abort after that refusal. The checkpoint role6
reservation/loan path is unchanged.

Ordinary return checks the actual row, batch and owner generation. A FREE row
can unwind only the current next-batch claim; DRAINING requires the current
batch, zero pending operations and no live fence. The pool API checks immutable
original group/nonce/owner provenance and the current holder. HAND/ACCEPT must
restore the original owner before return, and outstanding loans/references
refuse. A generation-limit retirement depletes the group without inventing
replacement capacity.

`ordinary-drain-credit-unit` prepares a real C successor through stage/emit and
calls actual B admission after generic sector allocation reaches the protected
floor. Its extent-refusal case exhausts actual allocator reservations, compares
full ops/root/C transaction snapshots before and after refusal, cancels one
exact fixture reservation and retries the same batch. Return controls use
actual START, then an explicit no-IO DRAINING premise, and compare complete pool
and commit-I/O projections for stale owner, handed-away and retired-handle
refusals. `ordinary-drain-credit-live-unit` continues that same producer through
the existing public-turn/simulated-adapter driver and requires accepted
settlement, FREE B row, and fully restored drain quotas with working protection
unchanged. These are prepared source controls, not executed assertions or
physical IO evidence.

Source controls remain unexecuted. Current initialization configures the same
profile before genesis; the ordinary producer connection and its actual
stage/admission/return controls still require a composed qualification gate.
Static service fit does not reserve an entire foreground transaction or prove
physical maintenance capacity.

The JOIN control first obtains an actual open collector from successful public
admission. Its over-room negative input calls the actual join primitive; a
stale workspace generation calls public admission while that same row is
selected for JOIN. Both compare unchanged queued operations, directory and C
transaction state, pool/commit-I/O metadata and member count. The OPEN extent
refusal additionally requires no retained journal generation, no pending
operation, no issued write and no live fence before exact retry.

`ordinary-drain-credit-canonical-unit` is the narrow B-only entry: the existing
canonical R2 world, actual pool-credit configuration with initialized B
row/I/O geometry, generic exhaustion, actual allocator exhaustion, START
refusal, exact fixture-reservation cancellation and SAME-batch START success.
Its explicit configured antecedent protects the declaration-derived B future8
bundle plus each B row's journal/scratch demand; it does not represent full C
working29 or service admission. It creates no alternate core or arm
implementation and does not claim C stage,
executor initialization or physical IO. On the cold donor its inherited R2
closure still includes checkpoint workers; projection onto the current root's
existing R2 assembly must preserve that root's callback composition rather
than import cold boot to exercise this fixture.

`checkpoint-configured-borrow-unit` uses the actual configured working producer.
It checks stale-owner zero-acquisition abort refusal, actual empty abort, exact
same-HELD-token retry, all declared working leases, and the same extracted
journal/anchor consumers used by `checkpoint-anchor-future-unit`. Extraction
preserves the consumer transition tail; only fixture free-count assertions
are generalized to the complete declared class vector. Journal and writer
handback preserve immutable credit provenance, free counts and the two
ordinary B quotas. Installed eligibility, allocator phase2 and validated
WAIT-FENCE callback remain explicitly synthetic; COMPLETE comes from actual
publication harvest. Final central freeing and physical persistence are outside
this control. The source-only inventory records actual include closures and
root differences, not cache qualification or an executable PASS.
