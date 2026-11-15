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

Unexpected END refusal first cancels the exact unsubmitted extent reservation.
Only successful cancellation permits returning the leases and empty abort.
Failure stops with uncertainty and retains the resources. The checkpoint
role6 reservation/loan path is unchanged.

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

Source gates: structural Lisp parsing, direct B* imports, diff/secrets checks,
and local closure resolution. The unit and simulated-composition closures are
282 and 365 local books respectively. ACL2 admission, guard/cost/footprint
qualification and runtime initialization of the configured schedule remain
pending; the B consumer alone does not activate credit configuration.

## Root d7 projection

The separate `assurance-drain-credit-root-slice` keeps root
`d7f9c00e0`'s existing canonical C/B assembly and applies only the pool credit
prerequisites, ordinary B consumer, shared geometry/configuration and staged
unit. It does not import cold boot/checkpoint workers or change root's directory
representation. After the qualified API source cohort and atomic stage preflight,
the staged/refusal closure is167 local books, stage-only164, union168. Thirteen
books have direct form changes and152 closure keys are new or invalidated.
Sixteen closures remain unchanged from that root; eight have candidates in the
author's local cache. These are
source-key/candidate facts, not an installed warm prefix or ACL2 admission.
The exact inventory and plain closure keys are recorded in the adjacent JSON.
The higher simulated-adapter entry stays in the owning cold donor lane; it is
not registered in this compact root projection. Credit schedule initialization
and actual C working loans still require the capacity owner's final integration.

The actual commit arm's nineteen direct `:do` operations all have defcost
declarations. The only changed direct operation is the existing
`fn2-commit-release-pool`, whose table declaration adds the commit root needed
for exact FREE-row unwind binding. The new reserve/return helpers are internal
DEFUN calls under existing admission/release operations, never new arm operands.
Root's lifecycle cursor predicate declaration is preserved. New capacity arm
operations must receive their own declaration/face audit when their source lands.

The compact projection still uses the earlier protected-quota-only configure
ABI. It is an intermediate B-consumer control, not the final profile-service
admission target. The current cold donor imports the profile-aware configure
and passes the same profile used by actual core initialization. Projecting that
ABI requires the actual shared source-manifest geometry leaf and its preceding
three-unit payload/physical-stride separation, which this older root lacks.
Copying the later formula into the older representation would hide that genuine
semantic dependency. No warm gate is requested for the incomplete admission cut.
