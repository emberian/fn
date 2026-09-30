# Bounded history record preparation cursor

S7/P12/D33 component; PRF-1088 and SCN-1005. This is a source library
boundary, with no host caller, producer completion, physical allocation,
certification, qualified-image or publication claim.

## Controller contract

The private snapshot builder consumes the captured immutable source-list
reference directly. It does not first call `fn-hrc-load` or construct a doubling
suffix array. A census pass computes exact encoded byte counts without retaining
encoded rows; a second pass re-begins the identical pinned source rows and emits
current-format bytes. Capture epoch, arena incarnation and maintenance resource
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

## Remaining union obligations

General trees, strings/symbol names and numbers need an explicit task stack and
resumable scalar/string traversal with exact `fn-scc-program` residuals. Octet
classification must itself resume. Word packing must prove exact zero-padding
and `fn-hp-pack8` equality. Message-ID key hashing must consume characters
incrementally and equal `fn-hp-mkey`. The completed census must prove all five
region lengths and placement equal the existing `fn-hp-row`/`fn-hp-x-blocks`
format. The source/profile invariant must establish representability before
allocation; a whole-row predicate is never a per-tick runtime guard.

Literal reachable leaf traces and corrupted-state hypothesis removals are in
`tests/acl2/history-record-cursor-tests.lisp`. Initial refinement's u64-size
hypothesis has no practically executable removal witness at this stage; it is
not represented as fully toothed. Full tree/word/census/controller proof,
funding, matched measurements, actual producer calls and coalesced qualification
remain open under the original S7/P12 portfolio.
