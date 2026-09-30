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
