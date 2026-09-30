# Bounded stored DEFLATE windows (PRF-1112, SCN-1020)

The stored decoder and COMPRESS use the same resumable inflater, with
separate expansion policies. Network `fn-zin-feed` retains its existing
256 times consumed-input plus 65,536 prefix bound. Stored decoding uses
`256*C + 65,536`, where C is the declared compressed length, and requires
exactly the declared N decoded octets. C and N are untrusted descriptors:
core positional containment, supported-profile bounds and resource admission
must precede use, independently of later extent authentication.

This is an intentional change of stored acceptance policy, not an equality
between the old lookahead decoder and the network loop. The old decoder
accepted a 108-byte valid raw stream for 93,100 `A` octets that the network
loop refused at 92,672. The new policy preserves that valid success. It can
also accept valid high-ratio prefixes followed by ordinary data, and trailing
bytes contribute to declared C even if the final block ends earlier. This
broader stored domain remains subject to total output, work and integrity
bounds. No network expansion allowance changes.

A nonempty stored stream succeeds only at a final block or a complete sync
flush: `:stream-ended` in mode 13, or `:more` in mode 0 with no buffered bits
and a recorded empty non-final stored block. The marker is reset at each
new block and decoder reset; only a valid zero LEN/complement pair sets it.
A one-byte final stored header `01`, previously accepted at N=0, now refuses
as truncated. A nonempty stored block ending in bytes `00 00 ff ff` does not
impersonate a sync flush. Trailing bytes after a final block remain allowed.
The explicit empty representation C=0,N=0 remains valid.

`fn-pzw-initialize` receives a pinned shipped dictionary (the dictionary
registry permits at most 64 KiB), initializes the 65,536-byte ring/preset and
3,494-byte table, and reserves a 64-byte scratch output. Admission precedes
these fixed reserves. These are dedicated slots: reserve never shrinks a
legacy oversized vector. Scalar state is twenty boxed naturals; runtime
charges must include representations of profile-sized counters and temporary
stored credit, not assume a 20-byte state. Dictionary tails are shared until
copied into the fixed preset half. The initializer has fixed bounded buffer
work separate from a decode scheduling quantum.

`fn-pzw-stored-chunk` consumes a span of at most 64 input octets, runs at most
1,024 decoder actions and at most the caller's remaining action budget, and
returns at most 64 scratch output octets. The total is bounded by
`min(N, 256*C+65,536)+1` when starting at or below the bound. The extra octet is
a private overflow sentinel. A caller must run `fn-pzw-stored-decision` after
each call and stop on refusal rather than resume an overshot state. Quantum
exhaustion resumes; the existing total `fn-pzd-budget` remains separate.
No arbitrary payload-size ceiling or full payload allocation is introduced.

The stored allowance temporarily credits C inside the existing inflater;
`fn-pzw-stored-chunk-counts-real-input` proves that returned state restores
actual input consumption, and that output length equals the counter delta.
`fn-pzw-stored-chunk-is-resumable-run` relates every returned value and buffer
effect to the logical resumable run over precisely the given input span.
`fn-pzw-select` derives scratch source/count/private-window destination for
the requested decoded interval, bounded by 64 and 16,384 respectively.

`:decoded` is private codec completion. It grants no publication permission.
The extent controller must still scan and authenticate the complete protected
prefix, including compressed trailing bytes, compare its trailer, and match
the issued token, incarnation and lease. Physical ownership retains all
buffers until actual worker settlement and output transfer/release.

Current source includes the canonical whole decoder and pooled decoder
conversion plus the bounded component. The existing whole-payload host
realizer still allocates whole input/output and is not the completed streaming
path. Full window-selection/copy composition, authenticated publication,
physical funding, matching images/natives and performance measurements remain
open. The old lookahead fast-path timing is historical and does not qualify
this source. Literal regressions and narrow source proofs support only their
stated boundaries.

Runtime operation inventory (numeric allocator bound still open): each
`fn-zin-loop` action pulls one input octet or invokes `fn-zin-step`.
Copy/literal bulk helpers emit at most the remaining 64-byte output room
across a chunk. A table-building action has fixed work: fills touch at most
320 lengths; `fn-zin-construct` clears a 512-entry lookup, counts/places at
most 288 symbols, and walks fifteen code lengths. Its lookup fill nests at
most 288 symbols with at most 256 replicated entries each (a conservative
syntactic bound, not a claim that valid tables reach that product). Two
constructs build literal and distance tables. Tables mutate the reserved
3,494-byte slot. These helpers allocate no new vector or octet list in the
concrete path once dedicated slots are initialized.

Arithmetic includes shifts and bit operations, bounded table indices, and
profile-sized input/output/budget counters. Live magnitudes include C,
actual input at most C, temporary credited input at most 2*C, allowance
256*C+65,536, and budget 4,096+16*C+2*N. The wrapper temporarily biases the
input counter; it never represents the declared C as a C-sized allocation.
Admission must charge boxed integer temporaries, twenty natural registers,
bounded status/error conses, runtime multiple-value/control overhead and
fresh-vector replacement coexistence. Source loop/action bounds are not a
measurement or proof of those SBCL allocator costs. A positive scheduling
quantum is necessary for progress; a zero quantum merely yields.

## Carried scalar width (PRF-1132, SCN-1039)

`books/payload-window-width.lisp` proves that the actual initializer establishes
`nbits <= 39` and `bits < 2^nbits`, and that actual stored chunks preserve this
carry when the input is an octet representation. The proof follows every
actual loop, bulk literal/match and single-action branch, including malformed
input and refusal. It introduces no served revalidation and no payload ceiling.
The actual stored chunk also returns a natural input position in `[START, END]`
under natural START and START <= END. END being natural was proved redundant
for that theorem; the executable entry's existing guards still require it.

The actual Huffman walker has a separate length-relative code/first/index
carry. Non-error exits preserve it; every exit, including a bad-code refusal,
has code <= 32,767, first <= 2,147,319,810, index <= 917,490 and length in1..15.
Octet-table and natural-bit-count premises were proved redundant for these
walker facts. `books/payload-window-register-width.lisp` now establishes the
Huffman carry in the actual initializer and preserves it through the actual
stored quantum on all exits except `(:refused :bad-code)`. The weaker fixed
scalar envelope holds on every exit, including that refusal.

The same book establishes actual initializer header carry unconditionally and
preserves it through stored chunks under the carried fixed table representation:
mode <=13, remaining stored length <=65,535, distance/preset <=32,768,
history position <32,768, final/sync marker <=1, symbol <=65,535,
HLIT <=286, HDIST <=30, HCLEN <=19 and index <=316. Window and output-buffer
hypotheses were proved redundant for this header carry and removed. The
fixed table representation is a proof-only boundary predicate; the served
path does not scan it on every quantum. Guard verification alone does not
exclude an unbounded corrupted register.

The reviewed profile-arithmetic candidate per chunk plus one budget update,
window selection and stored decision is `17 + 6*Q + 2*O + I`: at most
`3 + 2*Q` multiplications and `14 + 4*Q + 2*O + I` additions/subtractions,
where Q <=1,024 and I/O <=64. Initial budget construction adds two
multiplications and two additions. This is a high-level source inventory candidate,
not an actual translated primitive-count or allocator theorem. Source
subtraction must count separate unary negation and binary addition unless
matched compiler evidence proves fusion; the copy loop has three sites per
output octet (negation, destination addition, and loop increment). The runtime must account for
primitive workspaces, extra limbs, signs, status conses and control overhead.

With the controller's source-position carry keeping actual TIN <= C, stored
credit can make temporary TIN reach2*C, so the bomb-limit intermediate is
`512*C + 65,536`. With only TIN <= C at chunk entry and a64-byte span, it may
instead reach `512*C + 81,920`; the stronger bound needs the complete source
sequence premise. At signed63-bit C, even `512*C + 65,536` needs up to73
magnitude bits. None of these source facts supplies a selected-runtime
allocation bound or authorizes native admission. The evidence file records
the exact component and the remaining width, count and runtime obligations.


`books/payload-window-profile-width.lisp` connects the captured source
sequence and output carry to the actual internal loop. Its cheap scalar
invariant keeps credited TIN plus unread input <=2*C and TOUT plus remaining
scratch room <=N+1. Actual stored-credit establishment and stored-chunk
preservation are proved; no previous scratch-list validity is required at
the entry because that scratch is cleared. The inner proof covers pulls,
bulk/single output actions, yielded and refused exits.

Under explicit supported signed63-bit C/N, actual `fn-zin-bomb-limit` is
below2^73, actual TOUT+PRESET below2^64, and actual `fn-pzd-budget` below2^68.
Natural-C/N hypotheses on the standalone budget-width theorem were proved
redundant and removed in favor of bounds on their normalized inputs. These
are operand/result magnitude bounds, not primitive allocation counts. Their
supporting upper-bound lemmas are explicit-use facts without generic global
rewrite/linear rules. Literal teeth include an actual maximum-profile bomb
above2^72, retained-hypothesis removals and labelled coefficient mutations.


`books/payload-profile-source-trace.lisp` observes nine actual nonrecursive
profile helpers, generated from pinned trusted source. Each observer has an
actual value-projection theorem and dynamic arithmetic-source count theorem.
Events distinguish binary addition, multiplication and unary negation,
preserving argument and branch evaluation. Multiple-value events describe
logical projections; the observer's own lists are not implementation
allocations. The closed generator rejects unreviewed operators. This source
coordinate does not yet prove whole decoder counts or selected-runtime
workspace lowering.

`books/payload-window-expanded-profile-width.lisp` preserves the stored
allowance semantics: signed63-bit compressed C can admit decoded N above
2^63. Under actual stored admissibility and that compressed bound, N is below
2^72, actual fn-pzd-budget below2^73, and carried TOUT+PRESET below2^72.
The former signed63-bit N theorem retains its explicit narrower premise; it
never becomes a stored-data policy. Each widened keystone has literal full
positive and hypothesis-removal teeth, including the permitted large N that
refutes a new signed63-bit decoded ceiling. These magnitudes do not supply
primitive workspaces or authorize native admission.


`books/payload-copy-source-trace.lisp` connects the counter-cost correction
to actual fn-zin-copy effects: its observer returns the same ring position,
ring bytes and output bytes and records K unary negations plus2K additions
for the large output-counter family. Under nfix(TOUT)+nfix(K)<=2^72 every
recorded operand fits that magnitude domain. Small ring/index arithmetic,
compiled frames and other decoder/controller calls are separate obligations.
The primitive source review permits a conservative32-byte pre-normalization
buffer for each selected72/73-bit signed neg/add; source-to-compiled lowering
still needs its explicit narrow runtime contract.


The actual copy-counter roster is joined to the shared selected runtime in
`payload-copy-runtime-workspace.lisp`. Under the exact qualified-coordinate
requirement and named single NEG/ADD allocation assumptions, one negation and
two additions per copied byte have a conditional96*K-byte workspace envelope.
The scalar demand selector refuses an unsupported coordinate/span; it is not
a new stored-data policy or complete decoder funding gate. Actual compiler
lowering, other arithmetic/modes, constructors, frames, first-use/cache,
collector coexistence and retained activation-to-return lifetimes remain
separate obligations before native admission. The central assumptions umbrella
must include the shared book at convergence.


`A-SELECTED-RUNTIME-POSITIVE` adds a separate conditional single positive
fixed-factor multiplication family for factors 2, 16 and 256 at the same
runtime/compiler/attachment coordinate. Its natural input limit and extra
result digit are explicit; negative copies, ratios and general multiply are
excluded. Existing actual storage allowance and decode-budget source observers
join to conditional 64/128-byte arithmetic-family sums. C63/N72 alone need a
conservative 74-bit helper operand bound; under full stored admissibility the
existing narrower budget theorem remains unchanged. The positive fixture uses
an admissible stored length; unsupported wider input is labelled separately.
Actual compiled constant-site lowering remains to be qualified before any
complete runtime demand consumes the conditional primitive family. The
central umbrella patch includes both shared assumption books at convergence.


Actual emission, input-pull and match-copy observers in
`payload-action-source-trace.lisp` are generated from the pinned actual source.
Their value/effects equalities cover the complete returned state and buffers.
`payload-action-source-counts.lisp` distinguishes refused/successful emission
(two/four additions plus one multiplication), input pull (two additions), and
match copying. For positive K, match has two plus K negations, four plus2K
additions and one multiplication; a zero-K refusal still has one negation,
two additions and one multiplication. Borrowed getters/setters, ring/index
and bit-buffer helpers remain explicit unpriced events. Literal guarded
success/refusal fixtures and an omitted-negation mutation accompany the
unconditional projection/count theorems; these have no removable hypotheses.
This does not establish all decoder modes or actual allocator adequacy.


Actual saved-core diagnostics show `fn-pzd-budget` constant factors16/2
lowering to ASH4/1, while bomb/allowance ratio multiplications call generic
multiply. `payload-budget-shift-workspace.lisp` therefore maps the actual
budget source roster to two positive shifts and two adds, rejecting unknown
factors instead of dropping them. `A-SELECTED-RUNTIME-SHIFT-RESULT` is limited
to positive ASH result buffers at counts1/4 under the exact shared coordinate.
The conditional128-byte sum includes two shift RESULTS and two add primitives.
Internal fixnum shift temporaries, compiled call/frame and collector lifetimes
remain open; this sum is not total ASH or decoder allocation demand. New
literal domain-removal and unsupported-factor mutation teeth preserve that
scope, and the central inclusion patch remains a convergence obligation.


`payload-action-runtime-workspace.lisp` establishes the actual emit/pull/match
arithmetic operand domains from carried input/output/header/bit/span bounds.
Under the named shared NEG/ADD and positive256-multiply families at the exact
coordinate, the arithmetic-only sums are96/160 bytes for refused/successful
emit,64 for pull,128 for zero-K match, or224+96K for a positive match.
Thus K64 costs6368 for this family, including the surrounding match counters.
Eleven complete conditional-positive and retained-premise removal teeth
accompany those component joins. The corrupt NBITS removal fixes the bad
scalar and proves domain failure for every unrelated external buffer; the
getter refinement is closed so proof preprocessing cannot execute unsupported
huge shifts. Width monotonicity helpers remain local. Borrowed getters/setters,
bit/ring/index helpers, compiled calls, cache/fault/collector lifetimes and
whole initialization/activation authority remain separate open obligations.

The separately proved `payload-action-header16-workspace.lisp` match join uses
the actual generic pending-register bound N<65536. It preserves the same
arithmetic-only sums, including6368 at K64, and does not require an unproved
mode12-origin N<259 invariant or impose that smaller bound on stored data.
Five literal positive/removal/corrupted-origin teeth distinguish header width
from valid length-code provenance; complete decoder/native funding remains open.

`payload-pull-runtime-workspace.lisp` connects the actual needed-input pull
condition, carried bit width and one octet to the scalar helper domain:
NBITS<=31, bits<2^NBITS and octet<=255. The actual `fn-zin-shift-in`
power/product/result stay below2^39. The named source/body-qualified
A-SELECTED-RUNTIME-PULL-OBJECTS assumption covers only the reviewed ASH(1,n)
for n0..31 and fitting fixnum multiply/add result/workspace object paths.
These arithmetic paths allocate no such objects under the exact domain and
compiled-body coordinate. The derived workspace corollary is explicitly
`-by-definition`, not a separate keystone. Ten complete literal domain
positive/removal/mutation teeth ship; local assumption countermodels concern
unsupported model choices, never observed allocator failure. Exact disassembly
hashes are qualification requirements, not a final image attestation.
Frames/control stack/cache/fault/GC, other borrowed helpers and full decoder
job activation-to-cleanup adequacy remain open. The complete alternative
central-inclusion patch remains mandatory at convergence.

`payload-table-runtime-domain.lisp` proves the actual `fn-zin-tget` scalar
domain from its entry index and two pointwise octet reads: both offsets are
within the fixed3494-byte Huffman table, high-byte multiplication is at most
65280 and the actual assembled value is natural below65536. These are the
existing decoder table representation sizes, not a stored-data ceiling.
A complete positive produced by actual reset/input-pull/fixed-header action,
four retained-premise removals and a separately labeled corrupted maximal-octet
representation witness accompany the actual helper theorem. No table scan, invented primitive count,
compiled getter/arithmetic allocation or whole-job tariff is asserted.

`decoded-window-profile.lisp` joins the actual nine-field
`fn-pwz-descriptorp` to the selected signed `off_t` end bound. Its theorem
derives compressed C below2^63, admissible decoded N below2^72 and the
actual action budget below2^73. N below2^63 is not an added data policy.
The descriptor recognizer does not prove the trailer came from the actual
32-byte packed digest; `fn-bch-pack` includes a terminal sentinel, so that
separate format relation has257bits. File/ticket/trailer/dictionary identities
remain arbitrary naturals at this boundary. The fixed-field natural-ceiling
helper retains their actual widths, ticket+1, actual budget and the credited
input intermediate512*C+65536. A corrupted trailer2^400 deliberately passes
the descriptor and offset checks, demonstrating why those checks cannot
authorize a257-bit tariff. Two complete core descriptor positives (including
N above2^63), both literal premise removals and separately scoped width-helper
witnesses accompany the theorem. This is a source scalar prerequisite for
actual `fn-pwz-job-demand`; the supplied-demand admission remains insufficient,
and complete constructors/wrappers/compiler frames/cache/GC/lifetime and
activation-to-definite-cleanup adequacy are still open.

`decoded-window-initial-funding-domain.lisp` now joins those descriptor
widths to the actual host-called `fn-pwz-begin` result. Actual initialization
establishes bit, Huffman and header carry; typed fixed history/table buffers
and empty output; and zero TIN/TOUT, without a prior decoder invariant. The
actual typed token and selected native offset profile establish the returned
continuation's N72, decoded-offset containment, at most16KiB requested window,
budget73, zero input span and initial status. Complete empty-preset, shipped-
preset and supported wide scalar positives, plus both control-premise removals,
accompany these literal theorems. These facts supply actual initializer inputs
to future full job demand composition. Compiled callbacks, frames, constructors,
cache/GC/lifetime and definitive cleanup remain separate open obligations;
no supplied-demand or native activation authority follows.

The separate A-SELECTED-RUNTIME-TABLE-OBJECTS encapsulate qualifies only the
reviewed standalone TGET arithmetic and two direct UB8 getter object paths.
At a natural entry below1747 and current fixed3494-byte table, pointwise octet
reads give fitting fixnum operands/results for the two measured multiply-by2
sites, index addition, ASH8 and final sum. The conditional component charge is
zero result/workspace objects, excluding control/XEP frames, cache, faults, GC
and full call lifetime. Historical diagnostic d44 matches the f441 source
form; it does not qualify actual inline callers or a final attached image.
The entry upper bound is proved from natural entry, fixed table length and
one typed read, so the actual domain bridge drops that redundant premise.
Four complete premise-removal tests and an actual reset/pull/header-produced
table positive accompany the weakened theorem. The central assumptions
umbrella inclusion is a mandatory separate convergence patch before a
compliance/completion claim; full INIT/job demand remains open.


The actual initializer now has a generated trusted-source observer with a
complete returned-value/effects projection. Its source roster establishes
35 explicit constructor cells,21 decoder field writes,3 ceiling sites,
69094 requested reserve octets and69030 populated history/table octets.
Observer-created trace/MV lists are excluded from the target constructor count.
Every typed buffer operation, field write and immutable preset lookup remains
an explicit borrowed site; this roster does not price those transitive runtime
implementations as zero. Under the selected native offset profile, the digest
byte/block ceilings and temporary/final word counts fit their proved scalar
bounds. No typed-token hypothesis is needed for that normalized digest scalar
component.

Actual begin preserves the inactive64-frame array. Concrete buffer reserve
keeps an existing larger vector, or grows exactly to the requested capacity;
only in the growing branch are the old and new payload capacities bounded by
twice the request. Logical fixed fill length does not authorize discarding
older retained vector/frame charges. Complete fresh/shipped source positives,
a trace mutation, a reachable prior split frame, larger retained buffer and
literal offset/natural premise removals accompany the component. The actual
installed Store/CP7/pool/source lineage, native callbacks/constructors/frames,
cache/GC/lifetime and activation-to-definite-cleanup demand remain open before
INITIAL admission.


The selected WIN/TAB/OUT executive composition now has a named complete
six-result/effect refinement to actual `fn-pwz-begin`. Its generator reads
the real abstract-stobj `:exec` selectors and pins each source body; the
composition is proof-only and no host executes it. Only typed physical
arrays are required. Prior logical-content correlation was proved redundant
because actual initialization clears all three buffers. Typed unused tails
remain necessary: a malformed cell beyond the newly populated region survives
and invalidates the full representation relation.

Actual selected initialization retains capacities exactly
`max(old,65536)`, `max(old,3494)` and `max(old,64)`, with fills65536/3494/0.
The complete positive, three retained-array removals and old-capacity tariff
mutation accompany this boundary. These are representation/capacity facts,
not a zero-allocation assertion: old/new reserve arrays, payload/header
constructors, selected compiler callbacks/frames/cache/GC and full definite
cleanup lifetime still require their actual funded runtime join. Installed
Store/CP7/pool/source authority and complete INITIAL admission remain open.


The selected concrete buffer routines now have trusted-source observers with
complete returned effects and source event counts. Actual initialization
performs69030 array writes and `7+H+(2 if H<32768 else0)` fill updates, where
H is the captured preset suffix length. Resize events are precisely the
three indicators for old capacities below65536/3494/64. After these explicit
reserves, actual append-octet/list/back routines take no implicit growth
branch. Larger preallocated arrays produce zero resize events.

The complete six-output/count boundary has fresh, shipped and preallocated
positives, all three retained typed-array removals and labelled count
mutations. Traces preserve actual reserve/write arguments and borrowed
operations; trace/MV lists are proof artifacts, not target allocations.
Source resize/write counts are not a compiled allocation charge. Actual
array payload/header lowering, callbacks/frames/cache/GC, old/new coexistence
and definite full lifetime still need the selected runtime funding join.

The actual selected initializer source resize requests now sum precisely the
65536/3494/64 payloads whose captured old capacities are too small; the sum is
at most69094 octets. The complete six-output host refinement joins this
quantity with final retained capacities bounded by old capacities plus
requested payload. Fresh, preallocated and mixed complete witnesses and all
three typed-array removals accompany that boundary. This counts requested
payload and retained logical capacity, excluding physical headers, alias
lifetimes, GC and full INITIAL admission. Larger old buffers remain retained.

The actual resize source roster is ordered output64, history65536, then
table3494, with each actual old capacity strictly below its request. This
joins the named generated UB8 success primary-object family at the explicit
qualified body/backing/compiler/HONS-NIL coordinate. The conditional fresh
primary-object bound is69152 bytes (80+65552+3520), and larger old buffers
remove their corresponding requests. This bound excludes callers, errors,
memoization, collector/first-use and old/new alias lifetimes; it neither
qualifies a final image nor supplies a complete INITIAL admission. Central
assumptions inclusion remains required at convergence.

The actual initializer source updater boundary now preserves the complete
host tuple/effects and identifies all21 register writes: indices0..17 to0,
19 to0,11 to1,18 to the bounded preset length. The frozen16-field digest
has17 scalar/reference setter calls, including temporary total/end
8*ceil(B/64) and final overridesceil(B/8). Its numeric values are at most
2^60 under the selected native offset profile; source capture is the exact
12-reference tuple and lease is the original token. Mode/IV/output are
exact and no frame-array write occurs. These source operand facts do not
price setter macros/callers/memoization/frames/GC/lifetime or grant INITIAL.

The actual selected byte/fill source trace now checks each emitted write
against its current concrete capacity: byte indices are natural and strictly
within capacity, values are UB8, and fills are natural within capacity. All
are bounded by the fixed65536 initializer scratch extent. The complete
six-output host refinement retains the three typed concrete arrays; malformed
unused tails refute that full relation rather than demonstrating that every
standalone write needs a global type premise. This source argument boundary
does not price setter macros, compiled callers, memoization, frames, GC or
retained old/new lifetimes and supplies no INITIAL admission.

The actual21-register source roster joins the separately named standalone
initializer-register primary-object family at its explicit exact body,
compiler, genuine vector20 and installed HONS-NIL coordinate. Its conditional
assumed primary-object sum is zero, with the full actual returned tuple and
effects retained. Comparing a coordinate does not install those runtime
facts. This component excludes source value arithmetic, initializer inlining,
callbacks, frames, collector/first-use and alias lifetimes; full INITIAL
admission and central assumptions integration remain open.
