# Provisional BPv7 workflow journal

This specification defines the first executable fn workflow for disconnected
BPv7 transfer.  It is a local laboratory profile.  It does not define the
portable D01 exchange grammar, choose D09 signing, prove a BPA durable, or turn
a BP status report into fn application acceptance.

The executable decisions are in `books/bp-workflow.lisp`.  They start from an
already committed `fn-node` article/archive binding.  Local posting therefore
continues to acknowledge the local archive guarantee only.  Creating onward
work is a separate journal transaction and receives its own enqueue
acknowledgment after that transaction is durable.

## State and identity

A fixed schema-1 configuration records the local and peer EIDs, local policy
identifier, receipt authority, BP lifetime, node incarnation, and authorization
context.  Work records copy the peer, policy, incarnation, authorization
context, and terms identifier that governed their creation.  A work record is
bound to the immutable subject and archive obligation obtained from the actual
committed node binding; callers cannot supply replacements for those fields.
Local NNTP article numbers and BPA bundle identifiers are never part of portable
work identity.

Each storage intent uses a natural-number `(transaction-id,
transaction-generation)` pair.  A successful prepare reserves that pair before
its outcome is known.  The reservation remains in durable workflow history
through success, known abort, uncertainty, recovery, and restart.  A later
prepare can never reuse it.  This prevents an old completion for an aborted or
completed operation from authorizing a different enqueue, submission, or
receipt transaction.

The host journal must persist the prepare intent itself before invoking the ACL2
prepare transition.  An outcome is a separate append-only record:

- ordinary `durable` and `aborted` outcomes feed `fn-bp-complete`;
- recovery `committed` and `absent` outcomes reconstruct an indeterminate fence
  and then feed `fn-bp-recover`;
- a durable prepare with no outcome is fenced on restart and remains blocked
  until storage inspection supplies a recovery result.

A live ambiguous filesystem result feeds `:indeterminate`.  Ordinary completion
cannot resolve a fenced intent.  For an attempt found committed during recovery,
the model installs transport status `:unknown` and emits no submit effect.  A
host may call the BPA only after a known durable attempt outcome emits `:submit`.

The provisional journal therefore needs versioned records for configuration,
prepare intents for enqueue/attempt/receipt, ordinary or recovery outcomes, and
transport observations.  The prepare record contains the full semantic fields
needed to replay and validate the intent, including the transaction pair.  A
receipt prepare contains the full receipt identity, source/issuer and observed
peer EIDs, work and immutable subject, policy, incarnation, authorization
context, and terms.  Article-only storage schema 0 cannot reconstruct this
workflow; the workflow journal is an explicit storage-format addition tied to
an already durable archive binding.

## Transport boundary

An attempt has a stable attempt identifier, monotone per-work generation, BP
lifetime, and one of the executable transport statuses.  The model distinguishes
local durable intent from an API reply, BPA inventory acceptance, attempted
transmission, forwarding, BP delivery, deletion, expiry, no contact, restart,
inbound persistence, dequeue, and unknown state.

The pinned dtn7-rs experiment showed that the `/insert` response follows an
asynchronously spawned store/transmit operation.  The adapter therefore maps it
to `:bpa-submit-replied`, never to a durable acceptance claim.  Inventory that
survives restart is still a transport observation.  Inbound handling must use a
non-destructive download followed by a durable fn inbox barrier before any BPA
dequeue because the tested endpoint pop operation is destructive.

BP lifetime expiration, deletion, loss, no contact, and uncertain restart make
outstanding work retryable.  BP delivery alone does not close the fn obligation.
An explicit policy-matched retry event can make a delivered bundle eligible for
another attempt when the application receipt was lost.  Attempt ID and
generation checks make observations from older attempts no-ops.

These distinctions follow the BP lifetime, forwarding, delivery, deletion, and
status-report concepts in RFC 9171 sections 4.3.1, 5.2, 5.5, 5.10, 5.11, and
6.1.1.  fn adds the stronger rule that every transport outcome preserves the
accepted article/archive state and the outstanding application obligation.

## Application receipt

Transport status never releases work.  A receipt is separate application
evidence with nine fields: receipt ID, work ID, immutable subject, issuer EID,
peer EID, policy ID, node incarnation, authorization context, and terms ID.
`fn-bp-prepare-receipt` requires an exact match to the durable work and fixed
configuration plus an explicit true A-POLICY authorization input.  The boolean
is an environmental premise at this layer; it is not a signature proof or a
hidden trust claim.  The checked receipt then follows the same durable
intent/outcome/fence/recovery protocol before it closes the work and enters
receipt history.

Arbitrary, stale, wrong-context, or policy-unauthorized receipts are no-ops.
Receipt recovery emits its acknowledgment only after the checked receipt record
is known committed.  A future D09 decision must bind real verification and key
handling to the explicit authority, incarnation, authorization-context, and
terms fields; this experiment makes no cryptographic assurance claim.

## Executable guarantees and limits

`books/bp-workflow-invariants.lisp` proves state preservation for each production
transition and arbitrary finite event traces, and exact preservation of the
underlying node state. `books/bp-workflow-transport-invariants.lisp` proves
stale-event refusal and receipt preservation across transport-only traces.
Executable scenarios cover known abort and transaction
pair reuse, indeterminate completion and recovery, restart fencing, stale
attempt generations, delivery-without-receipt retry, exact checked receipt
recovery, and mixed finite traces.

The proof preserves the abstract accepted article/archive state.  Correspondence
to POSIX durability depends on the workflow journal adapter's create/link/fsync
barriers, exclusive ownership, bounded decoder, exact replay order, and BPA-call
ordering.  The dtn7-rs observations are experiment evidence, not a proof of all
BPA implementations or crash modes.

`fn-bp-statep` does not imply `fn-bp-works-boundp`: a separate joint invariant
over durable and pending work remains open. Outbound projection therefore
rechecks each work's actual node/article/archive binding. State preservation
alone must not be cited as proof that an arbitrary recognizable work list was
derived from that node.
