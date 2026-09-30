# Page word digest continuation

Source design coordinate: `351822ca5`, existing S7/P12/D33 work. PRF-1087.
This is a library boundary until the preparation controller calls it. It makes
no standard-conformance, collision-resistance, producer, admission or publication
claim.

`pgs-dc-begin(sel, base, nb, capture, lease, pgs-digest-state)` captures scalar names
and exact known 64-byte blockcount. `pgs-dc-step(block16-u32, pgs-digest-state)` is the
streaming core. When `pgs-dc-needs-block` is true the producer supplies exactly
one fixed block at `pgs-dc-next-word-offset`. Other phases take no input.
`pgs-dc-read-demand` bounds the optional word-reader request by eight.
`pgs-dc-tick(pgs-mem, pgs-digest-state)` is that optional captured-array reader client.
Both return `(mv status pgs-digest-state)`; `pgs-dc-result` returns the terminal digest
natural. Source arrays never change; there is no whole-input `fn-octets-pg`.

The disk-backed two-pass builder's census knows final N data pages, T table
pages and M directory pages before emission. Page digests use NB = 256; directory
uses NB = 256*M with current-format u32 M. Sequential DFS leaves therefore need
one bounded emission buffer, with no random source access or full directory
retention. Root/controller still owns pin and lease identity/lifetime.

The continuation follows the existing `fn-b3-node` tree literally. Node split
search doubles one scalar per tick; it never loops inside a tick. A chunk tick
reads at most eight words, builds their sixteen little-endian u32 halves and
compresses at most one block. Returning a left or right node computes one CV;
a parent descriptor concatenates two fixed eight-word CVs. The root tick does
one ROOT compression. Split/return/root phases may yield without reading input.
Final block descriptors retain inputs for the required final ROOT compression.

The private `pgs-digest-state` stobj has fixed scalar fields, one fixed current CV and
one fixed output descriptor, and 64 fixed stack cells. The depth follows the
u64 word-address representation (at most 57 chunk-tree levels for an addressable
u64 word span), rather than an article/store-size policy. Admission must establish
that the supported profile fits this selected word-address/runtime representation;
otherwise this seam cannot be advertised as supporting that profile. Constructor
allocation is separately admitted; begin does not zero-fill its stack. No old
stack cell is read above the maintained depth.

Proof decomposition: direct block halves equal the existing word octets;
residual chunk denotation is `fn-b3-chunk`; node/stack denotation is `fn-b3-node`;
each tick preserves the terminal denotation under immutable captured source;
begin's denotation is the existing BLAKE3 word-list model; terminal result agrees
with `pgs-x-words-digest` via `pgs-x-words-digest-is-blake3`. Carry capture/lease,
source range and representation invariants rather than rescanning source. Prove
strict progress using remaining node/block/split/return work, read/compression
bounds and concrete retained/scratch allocation. Literal teeth must exercise
empty, single block, chunk boundary, uneven parent split, source/capture mutation,
and every nonredundant premise removal. The general bridge and allocation proof
remain open until admitted, irrespective of passing examples.

## Exact semantic proof decomposition for the implemented machine

The state fields use **word** positions; the old BLAKE3 reader uses octet
positions. Define a proof-only `span(s,e,msg)` as the first `8*(e-s)` octets
of `nthcdr(8*s,msg)`. No producer may execute this logical list vocabulary.
The expected supplied block is `fn-b3-words(16, span(pos,end,msg))` whenever
`needs-block` is true. The external client supplies a fixed sixteen-u32 block;
the implemented empty chunk ignores a stale supplied buffer and uses zeros.

The planned `denote(cursor,msg)` first chooses its current output:

- node/split: `fn-b3-node(IV,span(start,end,msg),counter,0)`;
- chunk: `fn-b3-chunk(cv,span(pos,end,msg),counter,0,pos=start)`;
- return/root/done: the stored output descriptor.

It then folds active frames from top to bottom. A left frame pairs this
output's CV with `fn-b3-node(IV,span(right-start,right-end,msg),right-counter,0)`'s
CV. A right frame pairs its stored left CV with this output's CV. Each parent
is the existing `fn-b3-output(IV,leftCV++rightCV,0,64,PARENT)`. These are proof-only
nodes over the original immutable stream, never recomputed on the served path.

Structural invariant: all current and frame spans are within total words;
positions/ends are multiples of eight; current CV and stored left CVs are fixed
true lists of eight u32s; each active frame is exactly a left/right five-tuple;
its continuation counters are naturals; depth is within the supported codec
bound. The split phase additionally carries
`left-chunks(power,8*(end-start)) = left-chunks(1,8*(end-start))`, with power
positive and `128*power < end-start`. Begin/phase entry establishes this;
one doubling preserves it; finishing search identifies the old exact split.
No full invariant recognizer is called by step.

The exact general step keystone must assert, under that structural invariant,
correct supplied block and the fixed original stream:

1. next status is continue/done, next invariant holds, capture/lease remain exact;
2. `denote(next,msg) = denote(cursor,msg)`;
3. a proof-only exact work potential decreases by one until done.

Initial denotation is `fn-b3-node(IV,msg,0,0)` for total-sized valid octets.
Done implies depth zero and answer equals `pgs-octets-be-nat(output-root(denote))`.
Compose these, then use the existing `pgs-x-words-digest-is-blake3` for the
actual old host-called boundary. Never cite the finite vectors as this theorem.

For progress, let `W(n)` count ticks from node-entry to return-entry, excluding
that final return's continuation. A leaf has `1+max(1,ceiling(n/8))`. An internal
node has one node tick, its separately counted split doublings/final push,
`W(left)`, one left-return tick, `W(right)` and one right-return tick. A current
chunk has `max(1,ceiling((end-pos)/8))` remaining ticks. Fold continuation work
from active frames: left costs one left-return + `W(right)` + one parent-return
before its outer continuation; right costs one parent-return. The empty outer
continuation costs return-to-root + root-to-done (two). Root costs one; done
zero. This potential never runs in the producer. Domain induction proves the
fixed stack sufficient: children fit the next lower power-of-two chunk bound;
u64 word spans need at most57 levels, current u32 directory M at most 36.

The source increment admits guarded execution, preserved capture/lease and
actual reader demand <=8, plus literal comparisons including external blocks and
the old word-digest entry. The general decomposition above remains work to do.

## Phase refinement checkpoint

`books/pagestore-digest-cursor-refinement.lisp` now supplies all actual step
phase denotation equations, split carry, initialization and the conditional
terminal bridge `pgs-dcr-terminal-step-is-existing-digest`. The latter requires
captured-source denotation equality in the root state; establishing that carry
through the complete executable trajectory remains open, alongside progress,
supported stack domain and allocation. Clean source evidence and literal teeth
are in `planning/evidence/page-digest-cursor-refinement-2026-09-30.md`.
Root requested a subsequent compatible arbitrary-byte extension for protected
extents; these page-scoped equations and evidence remain tied to their bytes.

## Exact-byte reusable extension

The NEW byte book leaves the page core/stobj and page-scoped equations unchanged.
`pgs-dcb-begin(sel,base,B,capture,lease,cursor)` sets word end/total to ceil(B/8).
`pgs-dcb-step(B,block16,cursor)` delegates except final rightmost chunk; its
output descriptor records B-8*pos exact bytes. B is the controller's captured
immutable length, not inferred from scratch or stored in an unrelated field.
`pgs-dcb-read-demand(B,cursor)` is0..64 bytes and `pgs-dcb-next-byte-offset` is8*pos.
The caller supplies canonical u32 words little-endian with zero padding beyond
demand; it advances source only when the step consumes a block. Internal phases
are independent yields. `pgs-dcb-result-octets` provides exact32 digest octets,
performing an additional bounded ROOT compression/fixed output allocation that
must be funded. Source proof/refinement covers exact partial tails and a
conditional terminal fn-blake3 correspondence; full trajectory/resource and
constrained frame-digest joint attachment are explicit residuals. Evidence:
planning/evidence/page-digest-byte-source-2026-09-30.md.

### Admitted representation domain (source checkpoint)

`pgs-dcd-domainp(limit, state)` is proof-only. It carries scalar ordering,
CV shape, power-of-two search budget and active-frame child-span bounds.
`pgs-dcd-begin-establishes-domain` establishes it;
`pgs-dcd-step-preserves-domain` preserves it for the actual guarded subject;
`pgs-dcd-step-is-never-invalid` excludes the malformed-state branch under it.
No whole-state validation executes on the served path.

The representation uses 64 array slots. For the supported word-span domain
at most 2^64 words, ghost limit57 suffices; current directory page count
M<2^32, NB=256*M, uses ghost limit36. The directory theorem admits even the
inclusive endpoint; the codec's actual u32 domain is narrower. These are
representation sufficiency proofs, not stored-data implementation ceilings.
The exact-byte wrapper's additional `8*pos <= byte-total` guard still requires
its own carried invariant. Semantic trajectory and strict progress are open.

### Exact-byte guard domain (source checkpoint)

`pgs-dbd-domainp(limit, byte-total, state)` carries the page domain, captured
natural B, total=ceil(B/8),8pos<=B and active frame right-start<total.
`pgs-dbd-begin-establishes-domain` establishes it;
`pgs-dbd-byte-step-preserves-domain` preserves it for actual `pgs-dcb-step`;
`pgs-dbd-domain-implies-byte-step-guard` exports the complete actual guard;
`pgs-dbd-byte-step-is-never-invalid` excludes malformed status under it.
The predicate is proof-only. Semantic and progress proof consumes this leaf
without changing executable state or requiring a served-path validation.
