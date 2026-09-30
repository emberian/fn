# Checkpoint payload lifetime implementation contract

Status: coordinator architectural selection for the existing checkpoint work,
not an implemented or proved capability. The producer and physical owners must
land the actual transitions, representation boundary, resource accounting and
matching evidence. This adds no user decision or approval gate.

## What the source establishes, and what it does not

Inspection of the producer tree at `b95c5cc37` and the physical tree through
`b03b1dd6b` narrows the previously recorded "logical payload-view" gap:

- `books/payload-arena.lisp` has immutable sealed handles within an arena.
  Tombstones use fresh seals. Faithful extent reseating preserves the arena's
  logical payloads; it changes their physical placement.
- `fn-orcp-swap-word` in `books/owner-reclaim-pass.lisp` requires no other
  off-mutex reader. Current native reclaim installs the rebuilt Store, catalog
  and history; it does not clear the live arena. The snapshot capture also
  participates in the checkpoint/reclaim exclusion.
- Actual destructive native operations include `fnn-bridge-recover-begin` and
  `fnn-state-checkpoint-load-arena` in `host/native/io.lisp`, which call
  `fn-arena-clear`. These are recovery/open paths, not a demonstrated concurrent
  served mutation.

Therefore we have not demonstrated that today's live capture loses its logical
bytes during a normal seal or reseat. The remaining gap is enforcing and proving
the arena incarnation/reset lifetime at actual entry points, including future
recovery or reclamation changes. A history-file pin alone does not establish
that lifetime. Nor does a reader's birth generation grant ownership of whatever
physical file a later reseat selects.

## Selected contract

Use a fixed-size logical payload-view lease naming the arena incarnation, the
captured arena prefix count and a non-reused lease identity. Acquire it under
the owner mutex in the same admitted capture as the immutable Store/source
coordinates. The concrete host resource bound to that lease is the actual arena
instance, not an unvalidated lookup of a newly installed global arena.

The maintained relation says that each referenced captured handle lies in that
prefix and denotes its captured payload in the leased incarnation. Establish
the relation at source construction/capture through existing carried invariants;
do not scan all captured handles or payloads during admission or each read.
The prefix count is not a replacement for the source-to-arena relation and does
not authorize an unrelated source row merely because its handle is in range.

Appending seals and faithful relocation remain permitted. Clear, replacement,
handle reuse, or deletion affecting a leased prefix must refuse or wait for
definite reader retirement. Existing conservative reclaim exclusion stays until
a replacement establishes the same obligations. This does not claim that
blocking every reclaim forever, retaining all old files, or accumulating
uncharged stale arena entries satisfies the complete reclamation mission.

For each physical read, under the owner/extent lock order, validate the live
logical lease and obtain the handle's **current** placement. Atomically acquire
the exact file-incarnation/read/window lease before releasing the locks. Bind
the request identity, expected extent and integrity commitment to that lease.
Relocation after acquisition cannot redirect that request or close its owned
file. A later request may use a newer faithful placement. Staged-memory reads
likewise require ownership through their last borrow; a file lease cannot
protect a staged buffer.

Retain the logical lease through all census/emission passes and definite joined
cleanup. Cancellation requests stop further work but do not refund outstanding
workers, aliased buffers or the logical view. Release inner borrows/read leases
before the final logical lease. Reject stale and repeated releases without
releasing another reader's resources. Process death ends in-memory ownership;
recovery creates a fresh incarnation before admitting new captures, never a
valid continuation of an old in-memory token.

## Funding and implementation ownership

The producer owner implements the capture/controller lease and all actual
capture, refusal, cancellation, completion and cleanup transitions. The physical
owner supplies exact placement/read/borrow acquisition. The funding owner
accounts for their live and transient representations and any retirement debt
that a capture prevents reclaiming. The snapshot owner composes the logical
payload relation with the full recovery projection. Coordinate shared host
hunks rather than creating independent counters that can disagree.

Admission must reserve the required token/table and retained-resource terms
before mutation. Exhausted capacity refuses with unchanged ownership; a timeout
does not manufacture a refund. Concrete epoch/count/ticket arithmetic and
supported profile domains must agree, with no silent wrap or arbitrary data
ceiling. A conservative deferred reclaim is an explicit result; it is not a
proof of maintenance progress, rescue headroom or bounded retained disk.

## Evidence owed before activation

Prove preservation over the actual host-called capture/read/release and every
arena-changing entry point. Include positive and literal hypothesis-removal
witnesses for the lease/source relation and faithful relocation; retain the
trust scope of the durable-extent assumptions. Prove bounded scheduling work
and use the actual funded runtime representations.

Exercise at least: a post after capture; relocation before and after read
acquisition; a reader born after an old file's generation; attempted reset with
a live capture; reset and handle-index reuse after retirement; cancellation
with a worker still using a buffer; stale/duplicate token release; refusal
before admission; and full capture/restore with reclaimed history and composite
payloads. Keep model reachability and corruption witnesses distinct. A private
helper's green test cannot substitute for the actual composed controller.

This contract resolves the representation choice. Full S7/P12/W8 behavior,
funding, source proofs, certification and native evidence remain open.

## Registered close custody source, 2026-09-30

The additive close handler persists a revisioned close action before I/O and
retains the registered phase, including cancellation. It accepts only the exact
job token/action revision for a result. Closing does not delete the private
stage, transfer publication capacity, or release its claim. Definite close with
uncertain stage still yields `fn-bpck-cleanup-word :uncertain`.

The actual dormant native caller detaches its descriptor before the close
primitive; an ambiguous close is never retried. A detached NIL descriptor with
uncertain close custody cannot be observed as closed. The recording refuter
passes these paths and the prior competing-turn race; it uses explicitly
unfunded raw holders and recording callbacks/I/O. The additive ACL2 source and
fixture are **unadmitted**: the retained proof world expired before the send.
No bootstrap or native qualification was performed. The old cancelled primitive
result still needs a separate retentive settlement join before preparing close;
this source does not discharge that obligation or authorize constructors.

The additive cancelled-result handler now supplies the missing source
composition: only phase `:cancelled` and the retained exact action token/revision
may settle an already attempted open/write. It keeps that phase and the original
claim/CURRENT; definite result moves I/O toward cancelled close, unknown keeps
uncertain close. The dormant native settlement caller performs no primitive and
clears its old result only on this named registered disposition. Recording
callbacks demonstrate this caller custody; the actual registered trajectory
fixture and source guards remain unadmitted after proof-world expiry.

## Per-job holder association and operation-family request

The named `bp-checkpoint-registered-job` family request binds the native
holder and registered workspace creator roster to the actual SAME-pool job
claim/intent. Its executor role, BODY cost projection and constructor issuer
are not installed; storage-ready/constructing and callback presence authorize
none of its constructors. The public allocator still refuses first.

The holder is now twelve fields: immutable actual job token joins the controller
and native stage, surviving action-free turns. The genuine issuer must derive
that token internally. Native passes this identity to the literal
`fn-owner-bp-checkpoint-prefix-next-for-job` or `-close-next-for-job`; core
reads the actual pending job and rejects mismatch before preparing any effect.
The old eleven-field observation is historical runtime geometry only, not
current authority. These additive core guards/registered tests are unadmitted
while the combined-source proof replay is pending. Raw recording holders
remain explicitly unfunded.

Definite source return also includes the retained cancelled-result core callback.
The actual native caller marks it running under the same holder mutex and
publishes return via unwind-protect only after that callback returns. A real
SBCL held-callback recording refuter fails the exact354 preimage (it advertised
returned while the borrow remained active) and passes the repair. Descriptor
and stage debt remain owned. This is recording custody, not a grant or release.

## Publication intent and installed revision fence

Intent6 reserves `:promoting` and `:promoted` without new fields. The fixed
pending action is `(:bp-digest-publication originalVerifiedPlan7 :promoting
retainedVector intendedFinalBindingRevision)`. The original verified plan is
retained across each intent revision. Physical persists promoting BEFORE pool
C→U; unknown promotion keeps debt and globally fences allocation, never retries.
Known commit reduces the remaining claim, then publishes promoted intent.

Internal `fn-bpd-registered-publish-carry` derives the final successor revision
from actual promoted CURRENT and checks the stored intended revision. Its
genuine physical wrapper must establish the installed operation allowance and
qualified successor domain BEFORE invoking this unhooked storage mutator. No
installed scalar-domain getter exists yet; no u64 revision ceiling is invented.
Publication does not become public merely because this helper is present.

Example: constructing2 → promoting3 → promoted4 → carry installed5 → final
revision-checked intent installed5. The strong registered installed readout
requires BOTH the actual installed intent and carry5, with exact controller,
job, workspace nonce, source and revision. Carry5 while intent promoted4 stays
unexposed; final-write ambiguity remains fenced and cannot repeat pool transfer.
The old controller/job-only storage reader is forbidden for the actual consumer.
These source/fixture forms are unadmitted after proof-world expiry. The fixture
explicitly seeds promotion metadata without accounting or allocator permission.
