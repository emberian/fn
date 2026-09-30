# Bounded history record preparation cursor

S7/P12/D33 component; PRF-1088 and SCN-1005. This is a source library
boundary, with no host caller, producer completion, physical allocation,
certification, qualified-image or publication claim.

## Controller contract

The private snapshot builder consumes the captured immutable source-list
reference directly. It does not first call `fn-hrc-load` or construct a doubling
suffix array. A census pass computes exact encoded byte counts without retaining
encoded rows; a second pass re-begins the identical pinned remapped history rows and emits
current-format bytes. The remapped history row and original arena payload handles are distinct;
this codec neither reads payload nor re-interns a row. Capture epoch, arena
incarnation and maintenance resource
lease remain owned by the controller across both passes. A cursor preserves
the supplied capture and lease identities; it does not validate or manufacture
their liveness. Publication and ambiguous I/O are separate controller events.

The assembler selects a disk-backed private builder: canonical placement is
computed in ACL2 from the completed census, and bounded page buffers emit the
four metadata columns and encoded pool in physical page order. Additional
read-only source passes are permitted; no whole-row encoded blob is retained.
The existing `pgs-x-grow-image` whole-array allocation/zero-fill and
`fn-hp-x-append-step` relocation are not called by a bounded private-builder tick.
A future in-memory alternative needs segmented backing or an independently
proved resumable migration, including old/new coexistence and initialization.
Neither backing implementation nor physical pools are supplied by this book.

## First implemented codec boundary: opaque octet leaves

`fn-hrcur-leaf-begin(octets, capture, lease)` allocates one seven-cell cursor
and retains the source pointer. It performs no source scan, copy or encoding.
This boundary is for the existing tree codec's **nonempty opaque octet leaf**;
NIL and non-octet lists need the general tree cursor and are deliberately refused.

`fn-hrcur-leaf-tick(cursor)` returns `(mv verdict octet next-cursor)`:

- `:continue` advances one classification/count cell or a phase transition;
- `:emit` returns exactly one codec byte;
- `:prepared` ends this byte stream, with no durable acceptance meaning;
- `(:refused :event)` rejects a malformed/nonempty leaf or an unrepresentable
  current-format length; `(:refused :cursor)` rejects a malformed cursor.

The count phase validates one source octet cell per tick. It does not invoke
`fn-sccb-treep`, `len` on a retained source suffix, `coerce` or `fn-scc-encode`.
The fixed seven-cell shape checker does not inspect the retained source fields.
`fn-hrcur-leaf-invariantp` and `fn-hrcur-leaf-rest` are proof vocabulary only;
they are absent from the runtime guard and tick. The count is bounded by the
existing history image's u64 encoded-length representation, not a new operator
profile or stored-data ceiling. Format representability failure is explicit.

After classification, one bounded prefix is constructed: opcode, natural's
length-of-length and at most eight u64 length digits, at most ten cells. The
existing `fn-scc-le-digits`/`fn-scc-nat-octets` work is fixed by that codec width.
Prefix emission visits one cell per tick, and body emission advances the original
source pointer one cell per tick. Exhausting a scheduling quantum retains the
cursor; it never truncates or substitutes a completed record.

`fn-hrcur-begin-refines-octet-leaf` connects the initial logical residual to
**the existing `fn-scc-encode`**, not a separately specified encoder.
`fn-hrcur-leaf-tick-refines-residual` equates each pre-tick residual with the
emitted byte, if any, followed by the post-tick residual.
`fn-hrcur-leaf-tick-preserves` preserves the carried invariant and byte/verdict
domain. Capture and lease identities are preserved on every branch, including
refusal. Their semantic liveness remains a controller obligation.

## Allocation and retention

Begin allocates seven list cells; a normal tick allocates seven replacement
cursor cells. Prefix creation additionally allocates at most ten final prefix
cells and the existing natural helper's transient digit list, each at most eight
cells. Old and new cursors coexist until the runtime reclaims them. Multiple-value
return representation, runtime stack frames and scalar/bignum representation
are additional costs, not assumed zero.

The original leaf remains referenced throughout classification and prefix
emission. Body emission drops consumed source references from the cursor, but
the captured Store/pin can still retain them. Dropping a reference does not prove
collector reclamation or justify refunding the controller's source reservation.
The page-buffer pool, task-stack storage, staging file and queued I/O have
separate admission/lifetime accounting. No numerical physical reserve or
unimplemented pool is assumed here.

## Implemented bounded word accumulator

`fn-hrcur-word-push(octet, k, w)` accepts the next byte and the carried
partial-word scalars. `k` is in 0..7 and `w` is the little-endian value of
those `k` bytes. It returns `(mv verdict word k2 w2)`, accumulating one byte
as `:continue`, or returning one u64 `:emit` on the eighth byte and resetting
both scalars. Invalid byte/word state returns a named refusal.

`fn-hrcur-word-finish(k, w)` emits a nonempty final partial word, zero-padded
through eight bytes, and resets. An exactly aligned stream (`k = 0`) returns
`:prepared` without an extra word. Scalars are bounded by the existing u64
word representation. There is no encoded-row list, byte copying, reversal or
source scan in either function; `expt` uses only the fixed 0..7 byte offset.

`fn-hrcur-word-push-refines-partial` preserves the exact partial little-endian
value. `fn-hrcur-word-push-refines-pack8` equates the eighth-byte emission with
the existing **`fn-hp-pack8`**, and
`fn-hrcur-word-finish-refines-pad8` equates the final word with that same
packer over exact zero padding. `fn-hrcur-word-push-preserves` establishes the
permitted verdict and u64 output domain. `true-listp` hypotheses on the logical
partial prefix were removed only after proving all three weakened boundaries.
Reachable eight-byte/partial/aligned traces and a literal removal witness for
every remaining word-boundary hypothesis are supplied; invalid cursor examples
are explicitly argument mutations/corrupted state.

This supplies scalar packing boundaries, not yet the composed tree-stream word
cursor or the total padded census equality. The caller must thread each emitted
codec byte through push and invoke finish only at that stream's terminal state.
No scratch-buffer or physical allocator is inferred from the scalar functions.

## Remaining union obligations

General trees, strings/symbol names and numbers need an explicit task stack and
resumable scalar/string traversal with exact `fn-scc-program` residuals. Octet
classification must itself resume. Composed word streaming must prove its total
zero-padding/word count agrees with the existing row. Message-ID key hashing
must consume characters incrementally and equal `fn-hp-mkey`. The completed
census must prove all five region lengths and placement equal the existing
`fn-hp-row`/`fn-hp-x-blocks` format. The source/profile invariant must establish
representability before allocation; a whole-row predicate is never a per-tick
runtime guard.

Literal reachable leaf/word traces and corrupted-state hypothesis removals are
in `tests/acl2/history-record-cursor-tests.lisp`. Initial leaf refinement's
u64-size hypothesis has no practically executable removal witness at this
stage; it is not represented as fully toothed. Full tree/census/controller
proof, funding, matched measurements, actual producer calls and coalesced
qualification remain open under the original S7/P12 portfolio.
