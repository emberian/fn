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

An attempt's transport status moves only forward.  `fn-bp-live-statusp`
names the statuses that transport evidence may still advance (`:intent`,
`:bpa-submit-replied`, `:bpa-accepted`, `:attempted`, `:forwarded`,
`:inbound-persisted`, `:dequeued`, in the lifecycle order given by
`fn-bp-status-rank`); `fn-bp-transport-transition-okp` accepts an observation
only if it repeats the current status or strictly advances a live one.
`:delivered` leaves only through `fn-bp-request-retry`, and a retryable status
leaves only through `fn-bp-prepare-attempt` at a new generation.
`fn-bp-observe-transport-never-moves-status-backward` and
`fn-bp-observe-transport-never-returns-to-intent`
(`books/bp-workflow-transport-invariants.lisp`) state this over the production
transition for every work in the state, with no hypothesis.  Placing
`:inbound-persisted` and `:dequeued` between forwarding and delivery is a local
ordering choice for two statuses the current adapter never emits; a BPA that
reports them in another order is refused as stale, never admitted backward.

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

`books/bp-workflow-binding-core.lisp` and
`books/bp-workflow-binding-invariants.lisp` establish the stronger
`fn-bp-binding-statep`: structural state validity together with actual
node/article/subject/archive binding for every durable work and any pending
work. The initial state satisfies this invariant; each production transition,
dispatcher step and arbitrary finite event trace preserves it, including
indeterminate completion, restart and recovery. The theorem does not assume
that a prepared work has already become durable.

`fn-bp-statep` alone still does not imply this relation. The assertion book
includes fabricated works that are structurally valid but unbound: one whose
Message-ID has no binding, one whose article is present and bound but whose
immutable subject differs, and one whose archive obligation id differs; the
same work with the actual fields is bound. Outbound projection keeps
its explicit binding recheck for inputs not established to be reachable. The
joint invariant does not prove journal-byte decoding, host-event refinement or
physical durability.

**Durable intent before submission.**
`fn-bp-step-submit-requires-matching-durable-attempt-completion`
(`books/bp-workflow-invariants.lisp`): if a `:submit` effect is among the
effects of `fn-bp-step s event`, then `s` is a valid unfenced state holding a
pending `:attempt` intent, `event` is `:storage-complete` with `:durable` for
exactly that intent's transaction pair, the effect names that intent's work,
attempt id and attempt generation, and it is the step's only effect.
`fn-bp-apply-journal-record-submit-requires-ordinary-durable-attempt-outcome`
(`books/bp-workflow-records-invariants.lisp`) says the same of the record the
host applies: only an `:outcome` record with `:ordinary :durable` for the
pending attempt's pair, and only when the application succeeds. Committed
recovery of an attempt installs `:unknown` and emits nothing. What remains
host-side is A-HOST, stated in [the adapter specification](bp-workflow-host.md):
the model cannot grant the BPA call earlier than this; it does not make the
host obey the grant.

**Replay is a trace.** `fn-bp-replay-journal` and `fn-bp-apply-journal-record`
are the functions the host calls; `books/bp-workflow-records-invariants.lisp`
proves they preserve `fn-bp-statep`, `fn-bp-binding-statep` and the exact node
over arbitrary record lists, refuse a malformed or out-of-place record wherever
it occurs, and equal `fn-bp-step` and `fn-bp-trace` respectively on the events
a journal denotes. The denotation, the fabricated recovery fence and the
trailing restart are defined in the adapter specification.
