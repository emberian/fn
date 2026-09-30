# Resumable history image preparation contract

Source design coordinate: operability producer `351822ca5`. D33 composition;
no producer completion, resource admission or durable acceptance claim.

## Boundary and ownership

The controller owns a captured immutable Store pointer, source epoch/frontier,
source arena incarnation pin, and a maintenance resource lease. They are acquired
before any preparation allocation and remain live until every worker has joined,
the last referenced buffer is released, and publication or cancellation cleanup
has finished. A cursor carries the capture and lease identities without copying
or validating their contents. The controller checks their identity/liveness at
each external completion; history preparation does not manufacture a lease.

Begin must be O(1) in source history, with no list copying, recognizer walk,
array zero-fill or codec work. Tick consumes one bounded primitive; phase changes
may yield without emission. The complete controller returns `:continue`,
`:need-page`, `:emit`, `:prepared`, `(:refused reason)` or `:uncertain`; preparing
an image is never durable acceptance. Publication and ambiguous I/O belong to the
controller. No legacy format reader is introduced.

## Dependency graph

1. Capture and admission precede all allocations. Scalar counters and exact
   codec representability come from maintained source/profile invariants.
2. History construction consumes record fields/codec cells into the private
   image. Merely doing one `fn-hrc-flush-one` is insufficient: its codec walk,
   suffix normalization and backing array growth must themselves resume or be
   bounded by funded supported profile terms. This precedes dirty page commit.
3. Dirty enumeration visits one flag per tick; ordered page checking, resident
   checking, touched-table deduplication and count/high-water accumulation can
   fuse with it. Per-page digest consumes a fixed 16 KiB page; a whole directory
   digest must carry incremental BLAKE3 state across its blocks.
4. Fresh-store allocation uses the exact `pgs-alloc` result, reserving the
   directory run and singles in the current format's order. General free-list
   allocation needs an independent cursor; snapshot begin uses `(nil 1)` only.
   No caller may invoke full `pgs-alloc` or `take`/`nthcdr` over the plan inside
   a supposedly bounded tick. Output lists need per-cell construction/reversal.
5. Table entry installation can tick per entry after its page digest/address
   exists. A table digest follows its final entry. Directory installation can
   tick per table; final directory digest follows its final entry. The root
   record follows the directory digest. Array resize/zero-fill remains a
   separate allocation/work seam, including old/new coexistence during resize.
6. **First independent component:** descriptor emission from the completed
   existing plan. `fn-hpc-begin(lpages, plan, epoch, lease)` captures references;
   `fn-hpc-tick(cursor)` emits at most one `(physical-address selector word-base)`
   or advances a phase. Data, table, directory then terminal phases preserve
   exactly `fn-his-plan-writes`. The cursor's fixed outer shape is checked without
   scanning retained lists. Source list validity is a carried proof invariant,
   never a runtime guard over the remaining suffix. No bytes or stobjs mutate.
7. Emissions can feed a bounded write queue directly. Removing the current
   `by-addr` hash requires either positional page I/O or a proved physical-order
   stream for the fresh allocation; descriptor emission alone does not remove
   that host whole-plan allocation. The controller owns this assembler choice.

Steps 3/4 and descriptor emission can be implemented and proved independently
of row encoding. Table/directory/root effects cannot precede their digest and
allocation inputs. Snapshot-specific row remap is an independent producer of
history input; this lane does not edit it.

## Resource quantities to fund

The existing retained source Store and pin coexist with the private history
image (data, table, directory, dirty/residency vectors), record encoding scratch,
digest state, allocation plan cells, and staging file. Charge concrete vector
capacities and list/record cells, not logical payload length alone. Each vector
growth includes both old and new capacity until collector reclamation, plus
initialization work; each digest includes its actual word/octet conversion
scratch. Source history suffix/plan lists remain retained as long as the cursor
references them; a stream that drops a reference does not prove GC reclamation.

For the descriptor component begin allocates one fixed 10-cell cursor. Each
emitting tick allocates one replacement 10-cell cursor and one 3-cell descriptor
(and the runtime multiple-value return representation). It allocates no copied
source list and no growing accumulator. The old cursor and new cursor may
coexist. Native queued descriptors and buffer/worker ownership are additional
funded terms, and cancellation never refunds them before release/join. Numeric
work is bounded by the existing codec/profile integer width, not an invented
stored-data ceiling. No numerical byte reserve or rescue borrowing is assumed.

## Proof and assembly obligations

PRF-1086 is reserved for the descriptor boundary: exact residual output,
well-formed cursor preservation, capture/lease preservation, one-emission bound,
and reachable nonempty data/table/directory witnesses. The bridge names existing
`fn-his-plan-writes`, not a second independently specified output. Source-ready
means clean REPL admission with literal teeth; runner owns coalesced certification.
Until a real host calls this boundary, it remains a library component. Full
`fn-his-snapshot`, `pgs-x-commit-prepare/apply`, by-address writer, funding and
publication remain open and are never relabeled bounded by this component.

## Selected private backing: census then disk-backed emission

Root selected this direction after the initial component contract. Reusing
`pgs-mem`/arena directly retains an O(image) resize and region relocation; a
private segmented trie would require a new concrete indexed representation and
its runtime correspondence. The selected writer instead holds fixed page and
codec/digest scratch, with the private staging file as backing. There is no final
whole-vector, list or hash materialization.

`fn-hpb-begin(source, salt, capture, lease)` borrows the captured remapped history.
`fn-hpb-tick(cursor, observation, scratch)` will return a phase, a bounded I/O
request or emitted page, and the next state. The census resumes the record codec
and MKEY hash too: one source cell/octet/word primitive at a time. It accumulates
row count, exact encoded length and padded payload sum. Four metadata regions
have length `8 * count`; the fifth is the sum of individually padded encoded
lengths. Current FNADTSN2 region capacities/starts and header are computed from
these five lengths; any variable-iteration capacity rounding is itself a cursor.
These are current-format representability checks, not arbitrary data ceilings.

The immutable source is traversed again in column order to emit logical pages
in ascending order: header, MKEYs, encoded lengths, payload offsets, payload
lengths, then padded codec payload, including the format's capacity padding.
This may require multiple bounded traversals; total work is linear in emitted
codec bytes plus source traversal, with no retained per-record encoding. The
record codec helper is `fn-hrcur-*`; the digest helper is `pgs-dc-*`, consuming
fixed 16-u32 blocks directly and yielding separately for every parent merge.

Let N be data image pages, T=`pgs-x-ntables(N)`, and M=`pgs-dir-run-pages(N)`.
The fresh-store `pgs-alloc(N+T,M,(nil 1))` reserves directory pages at `[1,1+M)`;
data page P is physical `1+M+P`, table page Q is physical `1+M+N+Q`.
The page file high-water is `1+M+N+T`, with physical page0 zeroed. ACL2 must prove
these equations against `pgs-alloc`, then own exact file offset checks, page
counts and all I/O effects. The writer may issue positional writes in dependency
order (data, table, directory, final root/binding); no by-address lookup is needed.
A sequential writer could instead use the same staging backing to stream final
physical order, but must budget and model the additional reads.

Data digest results become table entries; table digest results become directory
entries; final directory digest becomes the existing commit root at txid1.
Bounded metadata spools/read passes may replace in-memory digest lists. An ACK
advances only the matching emitted-page token. A short/failed attempted write
fences that staging attempt and enters the existing uncertain/cleanup boundary;
no cursor turns it into durable acceptance. Publication remains marker-last.

The key representation theorem names the completed effect stream's page-word
map, proves it is the current-format canonical `fn-hp-image` of the captured
remapped history, and composes with `fn-hp-decode-image`. Intermediate invariants
state the exact census/column prefix and scratch contents, not a recomputed
whole-history recognizer. A separate page-commit theorem binds that image to
its table/directory/root. The snapshot projection owner then composes the
remap's payload-alpha and full Store inverse; equal old relocation-selected
physical bytes are neither needed nor asserted.

Admission before capture includes fixed concrete page buffers and their
simultaneously-live old/new copies, codec task stack, digest CV stack, cursor
records, owned fds/workers, full staging data/table/directory region plus metadata
spools, and existing source/target coexistence. If buffers are allocated once at
startup their actual retained capacity belongs to startup baseline, with an
exclusive transfer lease during snapshot; if allocated per attempt the attempt
funds them before allocation. This distinction never excuses served vector
growth. Empty cancellation cannot release a worker's buffer before join.

## Folded concrete page scratch API

PRF-1093, `books/history-page-buffer.lisp`: `fn-hpb` has exactly a fixed
2048-u64 array, scalar `used` in [0,2048], epoch reference and lease reference.
`fn-hpb-begin(epoch,lease,fn-hpb)` resets used and identities only;
`fn-hpb-put(word,fn-hpb)` returns `:stored` or `:full` and the updated scratch;
`fn-hpb-word(index,fn-hpb)` returns `(:word,value)` or `(:unwritten,0)`;
`fn-hpb-ready` means all2048words are written. The old physical word is never
exposed through the word API after reset. Format padding is supplied explicitly
as zero words; begin does not clear an entire old page.

The concrete prefix append and representation preservation theorems are folded;
`fn-hpb-prefix` is a logical abstraction, never a host serialization API.
Runtime recognizers are at most this single fixed page, not whole image state.
The constructor owns16384payload octets plus measured runtime object overhead.
A native conversion vector adds16384payload octets; collecting a transient
word list additionally owns2048cons cells and actual boxed-u64 representation.
These coexistence terms must be funded if the adapter uses them. A direct
array I/O primitive needs its own named effect bridge before removing them
from the demand. Neither begin nor a timeout releases the physical owner's
lease: the controller may reuse scratch only after synchronous completion or
observed worker death and join.

## Census and header source contract (PRF-1096)

`fn-hcc-row(count,pool,ordinal,encoded)` returns verdict/new-count/new-pool.
Only `:counted` advances. The record source ordinal must equal count; the
codec must supply the exact canonical current `fn-scc-encode` byte length of
the remapped abstract row. Each row is padded separately to8 bytes. Captured
source may be resident or decoded tagged nodes with borrowed spans: this
boundary does not convert either representation. Repeated column passes share
source epoch, original arena incarnation and immutable descriptor references.

`fn-hcc-cap-begin(used)` returns required pages and initial capacity;
`fn-hcc-cap-tick(need,cap)` returns done/continue/invalid and capacity, doubling
once on continuation. u64 used bytes imply need<=2^50; continuation preserves
cap<2^51. Empty used bytes return zero capacity. Two cursors suffice because
the first four regions have identical lengths. `fn-hcc-starts(column-cap)` and
`fn-hcc-pages(column-cap,pool-cap)` refine canonical starts/end, without image
allocation. Final physical layout remains `fn-hpl-layout(N)`.

`fn-hch-word(i,count,pool,column-cap,pool-cap)` selects one current header word
by fixed scalar cases. `fn-hch-tick(...,fn-hpb)` uses the scratch used counter
as i, stores one exact header word, preserves identities/representation, or
returns done with the full buffer unchanged. Scalar guards constrain count to
61 bits, pool to64, capacities to51: these are consequences of current codec
field/domain arithmetic, not arbitrary data caps. A complete operator profile
must establish them before capture/admission. Header scratch execution never
calls `fn-hp-hdr2`; that full list occurs only in the refinement and tests.

Source decoder contract selected with producer: source sum `(:resident row)`
or `(:decoded node)`; decoded constructors atom/pair/span borrow immutable pool
bytes. Span opcode/package/offset/length must be consumed directly by encoder.
Canonical octet-list classification must still resume over pair nodes; copying
a noncanonical incoming CONS encoding would change existing canonical output.
Source adapter tokens bind epoch/lease/ordinal; no duplicate completion advances.

## Metadata emitter (PRF-1104)

`fn-hpm-request(ordinal,component,entries,base)` identifies one entry component
and physical address, padding, or refusal. A charged spool reader supplies the
u256 digest for that ordinal and holds it across six components. Each digest
uses existing high-to-low fouru64 order. Every emitted u64 hashes as low32 then
high32 input words, matching the unchanged current digest byte convention.

`fn-hpm-tick(ordinal,component,remaining,entries,base,digest,fn-hpb)` returns
verdict/newordinal/newcomponent/newremaining/scratch. Stored writes one word;
page-full yields unchanged until I/O completion releases the scratch; done
requires remainingzero. Initialize table remaining2048 with at most341entries;
directory remaining2048*M with T contiguous entries. Directory continuation
must survive page resets, because its entries can cross page boundaries. Hash
the whole directory with one digest begin(NB=256*M), including finalpadding.

Physical representations: one cached u256 result plus fixed scalar fields,
fixed scratch, and separately charged metadata spool32octets per data digest
and32octets per table digest. Stream inputs/reference wrappers and actual
runtime bignum/header costs remain part of admission. Existing source files,
new stage, spools and native buffers coexist until their workers complete/join;
no rescue reserve or page cache slot implicitly funds them.

FNSI wrapper distinction: its physicalpage0 is zeros, and root record lives in
the F-row binding. PageA starts at16384+16384*A; framed segments start after
NPphysicalpages. Headerword/tableword emitters do not publish a root or marker.
ACL2 offset-domain plans must validate the admitted platform/profile bound
before positional I/O; native code may not derive those decisions itself.

## Census controller composition (resident source increment)

`fn-hct-begin(expected,capture-context,resource-lease)` creates seven cells:
phase, expected rows, completed count, padded pool bytes, pending codec,
capture context, resource lease. `fn-hct-offer(c,ordinal,source-sum)` accepts
only the next ordinal while waiting for a row. `fn-hct-tick` performs exactly
one child census tick; only its prepared result permits `fn-hcc-row` to update
the scalar history totals. Continuation does not scan source or logical
invariants. The expected count uses the current four u64-column format's
61-bit count domain; rounded final image admission remains a separate check.

The capture context must come from the source protocol, including its pass;
it is distinct from the resource lease and retained physical file pin. The
controller borrows those references and never compares an entire Store, file
name or lease. The current child codec accepts resident rows; decoded spans
remain explicitly unsupported until the cold encoder joins. No disk reader,
source authentication, physical reservation or publication is implied by this
composition. Retained allocations include seven controller cells, the child
codec's bounded frontier and source references; completed rows are released.
Exact runtime representation charges remain the admission owner's obligation.
During a scheduling call the prior and successor seven-cell wrappers coexist;
admission must include that transient overlap and both child frontiers until
the old cursor is released. A successful offer allocates the two-cell child
capture/ordinal context as well. This is an allocation description, not a
numeric rescue reserve; Lisp cell/header representation remains runtime-specific.

## Five-region emission scratch

The selected producer representation has five separately funded page buffers:
four columns and one byte-pool stream. Four `fn-hpq0` through `fn-hpq3` stobjs
are ACL2-congruent to the existing `fn-hpb` pool buffer. All five use the same
proved prefix abstraction and scalar-reset operation. `fn-hpq-put` writes one
word into exactly the selected region; the other four concrete states are
unchanged. `fn-hpq-begin` resets five used counters and capture/lease metadata,
without copying or clearing their backing arrays. Creation is startup backing
allocation, distinct from admitting its exclusive use for a served snapshot.

Retained backing totals five arrays of 2048 u64 words, five used counters, and
five capture/lease reference pairs. Native serialization/I/O buffers and any
pending write overlap are additional charged resources. A full buffer remains
owned until its exact positional write completion is acknowledged; only then
may its prefix be reset. The snapshot controller supplies that lifetime rule;
the standalone scratch dispatcher does not claim I/O completion fencing.

During the second source pass, record bytes fill the pool buffer. When a row
finishes, its exact length/padded length/offset and streamed Message-ID key
supply the four column cells. Full column buffers flush independently at the
ACL2-derived region positions. After all regions are complete, the private
staged file is scanned for data-page digests and metadata spools. This keeps
two source passes, avoids a per-record length spool, and never constructs a
whole image or by-address hash. Final composed stream/root proof remains open.

## Record bytes into the pool buffer

`fn-hpe-begin(source,capture,lease)` creates seven cells: phase, byte-codec
continuation, partial-word byte count, partial u64 accumulator, emitted byte
count, capture reference and resource lease reference. `fn-hpe-tick(c,fn-hpb)`
returns verdict, summary, next cursor and scratch. It invokes at most one
actual codec tick and writes at most one u64. A full scratch page returns
`:page-full` with both states unchanged before consuming a source byte. The
owner completes its positional write before resetting that scratch and
resuming the same cursor. A terminal aligned row emits no extra word; a
nonempty partial word emits exact current-format zero padding. `:prepared`
returns the exact unpadded encoded byte count for column construction.

Named component boundaries establish byte-total conservation, carried codec
invariant, concrete scratch/identity preservation, and exact eighth-byte and
final padded-word effects against `fn-hp-pack8`. They do not yet constitute
a whole-record stream induction to `fn-hp-pe`, nor authenticate source span
responses or establish disk publication. Literal tests exercise an actual
16400-octet row across a full-page yield/reset/resume and compare both pages
with the old logical packing. The full per-literal helper premise audit and
complete page/record induction remain open. Encoded counts and final padded
region capacities must already have passed census/profile admission before
this emitter owns a served reservation.

## Exact carried pool residual (proof-only composition)

`books/history-pool-refinement.lisp` names a logical partial byte prefix,
never a host list. Its invariant carries emitter validity, octet prefix,
`k = len(partial)` and `w = adt-unle(k,partial)`; prepared implies no partial.
`fn-hper-pending` applies existing `fn-hp-pack8` to that partial followed by
the actual `fn-hrcur-byte-rest`. Begin equals packed current `fn-scc-encode`.
`fn-hper-tick-refines-pool-residual` equates old scratch prefix plus pending
with the post-tick concrete scratch prefix plus pending. This covers actual
nonemitting, partial, eighth-byte and final-word transitions. Its assumptions
are the carried ghost invariant and concrete scratch invariant.

A finite proof-only trace invokes actual `fn-hpe-tick` and resets full pages,
transferring each prefix to a logical completed trace. Exact residual and
byte-count conservation hold for every fuel. A prepared trace from empty
scratch equals packed current codec words and exact unpadded byte count.
The trace collects proof vocabulary only: it is neither a runtime serializer
nor an authorization to reset a buffer before its I/O owner releases it.
General progress, cold byte-source composition, full column/history placement,
funding and durable publication remain producer obligations. Literal tests
exercise nonempty rows, an actual16400byte page crossing, both residual
hypothesis omissions, sole carry and both prepared-empty omissions. The full
per-literal audit of all helper/terminal hypotheses remains open.
