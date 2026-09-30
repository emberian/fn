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

This supplies scalar packing boundaries; the resident byte controller and census
below are also implemented. A production word-controller and the total padded
census/region-placement equality remain assembly obligations. The caller must thread each emitted
codec byte through push and invoke finish only at that stream's terminal state.
No scratch-buffer or physical allocator is inferred from the scalar functions.

## Implemented resident tree descriptor cursor

`fn-hrcur-tree-begin(tree, capture, lease)` allocates a three-cell outer
cursor, a two-cell initial task and one task-list cell. It retains the resident
source tree without scanning it. `fn-hrcur-tree-tick(cursor)` returns
`(mv verdict descriptor next-cursor)` with the same continue/emit/prepared
separation. Emissions are `(:atom source-atom)`,
`(:octets source-leaf exact-count)` or `(:byte CONS-opcode)`; they retain
source references and are **not** whole-atom byte expansion.

An explicit task stack traverses car, cdr and postfix CONS. Classifying a
possible opaque octet leaf visits one source spine cell per tick and retains
its original pointer and counted prefix. A failed classification beyond a
byte prefix carries a proved `:non-octets` task for the remaining suffix.
Byte-headed non-opaque tasks propagate that fact, avoiding repeated scans of
a shrinking suffix. Non-byte heads return the child suffix to ordinary
classification. A 200-byte prefix followed by a symbol completes within
810 descriptor ticks and still matches the original encoder; this is a
specific source-model witness, not a matched native cost measurement or a
general asymptotic completion claim.

`fn-hrcur-tree-domainp`, task/list invariants, descriptor interpretation and
residual functions are proof vocabulary only. The source domain reflects
existing scalar encodability and u64 image count representability for each
retained cons spine. Its connection to the captured producer/profile invariant
is still an assembly obligation. No whole-source domain check is executed by
begin, tick or a runtime guard. Safe logical prefix/tail functions permit the
codec's dotted trees without passing them to guarded Lisp list utilities.

`fn-hrcur-tree-begin-refines-encode` connects the initial descriptor residual
to existing `fn-scc-encode`. `fn-hrcur-tree-tick-refines-residual` proves exact
interpreted descriptor/pre/post residual conservation;
`fn-hrcur-tree-tick-preserves` preserves the carried source/task invariant,
permitted verdict and emitted descriptor validity. Capture and lease identities
are unchanged even on malformed-cursor refusal. The interpreter is proof-only;
the byte controller holds at most one active leaf/scalar cursor before returning
to descriptor traversal. The assembler routes emitted bytes to the word accumulator.

A count advance allocates one four-cell task, one task-list cell and one
three-cell cursor (eight cells); a pair expansion allocates three two-cell
tasks, three task-list cells and the cursor (twelve cells). Emission allocates
a two/three-cell descriptor and a three-cell replacement cursor. Remaining
stack/source references are shared. Old/new cell coexistence, runtime return
objects and retained source/pins still need concrete admission/lifetime
accounting. Arbitrary source depth is not silently truncated; task-stack
growth is incremental and must be funded from the supported source profile.

## Implemented resident byte stream and census

`fn-hrcur-byte-begin(source, capture, lease)` accepts `(:resident row)` and
retains references in a six-cell controller. Its phases are descriptor traversal,
scalar emission, opaque-leaf emission and done. `(:decoded node)` is explicitly
refused in this checkpoint; its borrowed-span extension is a remaining seam.
`fn-hrcur-byte-tick` performs one descriptor action or one leaf/scalar action.
An opaque descriptor already carries its exact count, so the controller begins
its bounded prefix directly without a second source classification pass.

The source domain now uses `fn-hrsc-domainp` for atoms, including the existing
255-digit scalar width and length-prefix representability. This strengthens
only proof vocabulary. No domain predicate or suffix validator is called by
the served tick. Each successful tick emits at most one byte, preserves the
carried invariant and capture/lease identities, and conserves the exact
`fn-scc-encode` residual. Prepared implies an empty residual. Scalar text
emission indexes the retained string; runtime never coerces a string to a list.

Controller replacement adds six cells to the chosen subcursor's bounded
allocation. A scalar begin adds ten cells. An opaque prefix begin adds seven
leaf cells, a prefix of at most ten cells and bounded transient length digits.
Traversal stack, source references, old/new cursors and captured pins coexist
until reclaimed; this book supplies no physical allocator or reservation refund.

`fn-hrcur-census-begin(source, capture, lease)` adds a three-cell cursor and
zero count. `fn-hrcur-census-tick` consumes the same byte controller, increases
its u64 count only on `:emit`, and returns that exact count only on `:prepared`.
It refuses before u64 overflow. Neither census nor byte emission retains an
encoded-row list. The census invariant conserves count plus the logical residual
length, and its initial refinement names `len(fn-scc-encode row)`. Its required
whole encoded-size hypothesis is a carried producer/profile fact, never a
runtime whole-row scan. A practically executable removal witness for this
initial u64-size premise remains open.

Tests reach every resident phase, interrupt and resume a nested dotted row,
compare complete bytes with the current codec, feed those bytes through the
word accumulator including final zero padding, and compare completed census
count with the codec length. Corrupted scalar metadata and a census total at
the u64 edge are separately labeled hypothesis removals. The composed word
trace is a test oracle, not a production word-controller completion theorem.

## Implemented borrowed raw span primitive

`fn-hrcur-span-begin(op, pkg, offset, count, capture, lease)` retains a
seven-cell cursor, forms only a bounded canonical header and names raw payload
bytes in an immutable history pool. Its natural width is the existing u64 pool
region representation. Strings use opcode3, symbols opcode4 with canonical
package0..2, and octets opcode6; zero-length octets emit the canonical NIL
opcode0. A normalizer may explicitly select opcode0 for an imported NIL name.
The supplied opcode/package are TARGET descriptors, never assumed to be the
canonical interpretation of an arbitrary old symbol instruction.

`fn-hrcur-span-begin` checks offset/count individually against the current
format u64 domain before adding them, so malformed huge metadata is refused
without performing an unbounded sum. Every valid-format result is unchanged.

`fn-hrcur-span-tick` emits one header byte, advances a phase, prepares an empty
stream, or returns `(:need-byte absolute-pool-position)` with the cursor
unchanged. `fn-hrcur-span-supply(cursor, position, octet)` emits one payload
byte and advances one position; wrong or replayed positions refuse unchanged.
No runtime pool lookup, whole string coercion, symbol interning, byte-list copy
or suffix validation occurs in this primitive. The source context and lease
are opaque retained references. The outer authenticated reader must validate
source epoch, capture ticket, pass, ordinal, physical file-pin incarnation and
request serial BEFORE supply; a matching position alone supplies no authority.
The snapshot lease `(capture-ticket, count)` and physical pin
`(:file-pin root-ticket file)` are distinct from a maintenance resource lease.
No guessed u64 ticket width or whole-root comparison is introduced here.

`fn-hrcur-span-begin-refines-wire`, tick/supply residual boundaries and carried
invariant preservation connect emitted bytes to the immutable pool model.
`fn-hrcur-span-octets-refines-abstract-codec` and
`fn-hrcur-span-string-refines-abstract-codec` connect this wire model through
proof-only **`fn-hdc-abstract`** to the existing **`fn-scc-encode`**. The symbol
case still requires composition with the bounded package-import/NIL normalizer.
The logical work measure proves each nonterminal local action decreases work
or requests the next source byte unchanged; authenticated supplies decrease
work. Waiting for external I/O has no completion-time assertion.

A begin/header tick retains seven cursor cells; canonical header creation adds
at most eleven final cells (symbol opcode, package, length prefix and at most
eight digits), plus the bounded natural helper's transient digits. A supplied
byte creates seven replacement cursor cells; old/new states coexist. Source
pool/pin, request object, scratch reader buffer, runtime return objects and
scalar storage require separate funding. No physical pool or reclamation refund
is assumed. Arbitrary represented payload length resumes byte by byte.

Tests reach prefix/payload/terminal states, yield and resume a borrowed span,
compare complete string/octet streams with the old codec, check opcode6zero
canonicalization and refusal of wrong/replayed positions. Supply refinement has
literal removal witnesses for all five premises. Initial span refinement has
nine removal witnesses; the u64 sum premise retains an enormous pool-length
hypothesis and has no practically executable removal witness. Tick progress
has both hypothesis removals. The stronger semantic span-domain refinements
and supply progress retain further literal-teeth work; no fully toothed full
cold-source/producer target is claimed.

## Bounded decoded NIL-tail probe

`books/history-decoded-record-cursor.lisp` adds the guarded seven-field
`fn-hrcur-nil-begin`, `fn-hrcur-nil-tick` and `fn-hrcur-nil-supply` seam.
Only package1/2 symbols with raw payload length3 request bytes. Each supply
compares one of the three NIL name octets; all other packages or lengths
complete as non-NIL without reading payload. Request ticks preserve the
cursor unchanged; wrong or replayed positions refuse unchanged. This is the
bounded nullness decision needed before decoded CONS classification can
canonically collapse an octet-list tail. General symbol import normalization
remains a separate emission boundary.

`fn-hrcur-nil-model-refines-decoded-symbol` equates the result with nullness
of the actual `fn-hdc-abstract` symbol span. Initialization, supply invariant
preservation, terminal denotation, productive supply progress and opaque
capture/lease retention are admitted with proper-local source replay after
cached `history-pages-row`. The runtime never reads the logical pool,
materializes a name or compares whole source references. The outer reader
must establish epoch/pass/pin/request authority before supplying a byte.

Begin and productive supply each retain seven cursor cells; begin temporarily
constructs no encoded name, and supply adds no source-sized object. Old/new
cursor retention, return tuples, source pin and authenticated scratch/request
objects require separate funding. Offsets/counts are checked individually
against the current format's u64 domain before their bounded sum is computed.
No physical allocation pool or reclamation refund is asserted.

Tests exercise both NIL packages, non-NIL names, metadata-only rejection,
yield/resume, decoded octet-list-tail canonicalization, all four supply
preservation removals, the tick invariant removal and all five productive
progress removals. Five initialization removals are executable; the u64 sum
removal retains a pool of at least2^64 octets and has no practical fixture.
The abstraction bridge's literal domain removals remain partial. This is a
source-library checkpoint, not a completed cold-tree encoder or producer.

## Normalized symbol to borrowed span

`books/history-normalized-span.lisp` connects the normalizer's canonical
`(opcode package)` descriptor to the existing guarded span emitter through
`fn-hrcur-ns-begin(descriptor,offset,count,capture,lease)`. It checks the fixed
descriptor and source-format scalar operands, then starts the actual span
child. NIL selects target count zero, retaining the original source descriptor
outside the child; other symbols retain their original name payload span.
No runtime name conversion, interning or source traversal occurs here.

`fn-hrcur-ns-begin-refines-abstract-codec` proves the initialized child
invariant and exact residual equals the current `fn-scc-encode` of the actual
`fn-hdc-abstract` symbol. Its canonical-descriptor premise is established by
the normalizer's named done/denotation boundary, not by shape alone. A wrongly
supplied package descriptor can have a valid child invariant and wrong codec
bytes; its literal removal witness demonstrates that obligation. Capture and
lease references persist unconditionally through valid and refused begins.
Existing span tick/supply refinements then apply to this initialized child.

The wrapper retains no new cursor frame beyond the span child's seven cells
and bounded canonical header. Old normalizer, source descriptor, old/new child,
request/return objects and source pin coexist until the outer owner relinquishes
them and require funding; no reclaim refund is assumed.

Protected proper-local source replay admits ten body forms with guards and
all refinements. Tests cover imported CAR, both NIL versus keyword-NIL
interpretations, unmatched ACL2 names, an actual child yield/resume stream,
NIL without payload reads, and capture/lease identity. All six practically
executable initializer hypothesis removals pass. The u64 sum premise retains
an enormous pool-length premise and has no practical removal fixture;
auxiliary wire/domain teeth remain open. This is still a source library,
with no full cold-tree encoder, host producer, funding or qualification claim.

## Bounded decoded octet classifier

`history-decoded-octet-scan` now supplies guarded seven-field
`fn-hrcur-dos-begin/tick/supply`. It advances one byte-headed borrowed pair,
uses an opcode6 tail's captured length, or delegates one three-byte NIL probe
action. Successful classification reports the exact nonempty octet-list length;
rejection carries the exact scanned prefix depth for subsequent postfix pair
expansion. No source conversion, pool read or suffix validation runs in a tick.

The carried proof-only invariant connects both outcomes through
`fn-hdc-abstract` to the current codec's opaque-list decision. Begin establishes
it, tick and attributed byte supply preserve it, and productive actions strictly
decrease a logical work measure. A demand leaves the entire cursor unchanged.
Capture/lease references survive every branch. The scanner does not authenticate
its supplied byte; the outer reader must fence the source context and physical
pin before supply.

Begin/replacement states allocate seven cons cells; delegated NIL child states,
old/new cursors, returned demand, original borrowed tree and pin coexist and
require outer funding. No physical pool or reclamation refund is assumed.
Thirty literal test forms pass in fresh standalone and cached-row source worlds,
including all five supply and seven supply-progress removals. The initial
abstract-length u64 premise has no practical enormous-data removal fixture.
Full cold encoder residual/invariant/progress and actual producer remain open.

## Remaining union obligations

The resident byte stream and exact byte census are admitted library components.
Production word-stream composition, full padding/placement equality and general
completion progress remain open.
The actual cold source is the sum `(:resident row)` / `(:decoded node)`;
the raw span primitive now streams pinned pool offsets, but decoded-tree composition must connect it without whole-string
coerce/intern at a terminal tick. Decoded CONS trees that abstract to octet
lists need resumable opaque-leaf classification; a zero-length opcode6 span
abstracts to NIL and canonically encodes as opcode0. Nonminimal old length
spellings are regenerated in current canonical form, never copied blindly.

Message-ID key hashing must consume characters incrementally and equal
`fn-hp-mkey`. The completed census must prove all five region lengths and
placement equal the existing `fn-hp-row`/`fn-hp-x-blocks` format. The
source/profile invariant must establish representability before allocation;
a whole-row predicate is never a per-tick runtime guard.

Literal reachable leaf/word/tree traces and corrupted-state hypothesis removals
are in `tests/acl2/history-record-cursor-tests.lisp`. Initial leaf refinement's
u64-size hypothesis has no practically executable removal witness at this
stage; it is not represented as fully toothed. Full cold-source and actual controller
proof, funding, matched measurements, actual producer calls and coalesced
qualification remain open under the original S7/P12 portfolio.

The NIL probe and normalized symbol initializer also replay in the standalone
source world, before cached history-pages-row is included. Their optional MIDX
rewrite exclusions remove a literal rune from an existing hint theory, so the
hint is valid whether that row theorem exists or not. The same exact bytes
replay again after the cached row include in hrcscan2; runtime and theorem
statements are unchanged. This is source admission, not certification.

## Importable cold runtime for private composition

`history-cold-record-runtime` contains the single guard-verified implementation
of `fn-hrcur-cold-begin(source, capture, lease)`,
`fn-hrcur-cold-tick(cursor)` and
`fn-hrcur-cold-supply(cursor, position, byte)`. Begin accepts
`(:decoded node)`; the tick and supply return three values: verdict, one emitted
octet or NIL, and next cursor. A byte demand is exactly
`(:need-byte pool-position kind child-coordinate)` and retains the cursor.
Kinds are `:octet-nil`, `:symbol-normalize`, `:span-body`, and `:opaque-span`.
The producer validates source/pass/root-pin, request kind/coordinate, reader
serial and fresh buffer ownership before supplying an authenticated scalar.
The emitter performs no whole-row conversion or retained-pool validation.

This source checkpoint makes private first-pass census and second-pass page
emission use the same executable stream. Count each `:emit`; rebegin the same
immutable source for replay. Existing resident-only census APIs are unchanged.
A tagged adapter lives above the resident and cold runtime books; placing its
cold dependency in the older record book would introduce an include cycle.

The lane's separate work-in-progress `history-cold-record-cursor` proof book
includes this runtime; that suffix is not part of this importable checkpoint.
Its complete all-phase invariant/residual, productive progress, literal teeth
and fresh full replay are still open. Runtime tests exercise complete current
codec outputs for scalar, borrowed strings/octet spans, collapsed pair tails,
imported symbols and NIL aliases. These tests and runtime guard admission do
not complete the cold producer, physical funding or qualification claim.
