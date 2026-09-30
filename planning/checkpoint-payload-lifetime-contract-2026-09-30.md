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

## Native reset serialization selection

Inspection of producer source `57b70ff2b` confirms that the two destructive
entry points now call the guarded clear adapter. It also confirms that
`fnn-call` does not serialize concurrent calls. A lease check and clear inside
one ACL2 function therefore do not establish native mutual exclusion. Locking
only the lease table would still permit unrelated owner STATE mutations to
race with a recovery clear.

Keep destructive clear within quiescent startup or recovery. Use one lifecycle
mutex associated with the actual arena to exclude reset from transitions into
and out of owner service. Quiescent means before owner workers start, or after
every owner worker and outstanding borrower has definitely joined. Register
serving before exposing any worker. Startup failure must join any partially
started workers before restoring quiescent status.

During serving or draining, reject reset before accessing mutable ACL2 STATE
or the arena. The lifecycle phase is a native scheduling observation; ACL2
makes the reset-permission decision through a state-free entry. During an
allowed quiescent interval, hold the lifecycle mutex across the existing
guarded reset, clear and incarnation update. The existing live-lease refusal
still applies: quiescence does not manufacture a joined-cleanup result.

Capture, acquire and release use owner-then-lifecycle lock order. A lifecycle
mutex holder never waits for the owner gate or for a worker to join. Drain and
join outside that mutex, then establish quiescence under it. Live recovery
must follow this stop/drain/join sequence; no generic live-clear path is added.
This choice does not add a global lock around ordinary steady-state ACL2 calls.

The producer owns the implementation and its source/native evidence. Exercise
both barrier orderings: reset completes before owner startup/capture, or owner
startup/capture wins and reset refuses without changing the arena or lease.
Include draining, partial startup failure and outstanding cleanup. This is a
selected implementation obligation, not evidence that the native ordering is
already implemented or proved.
