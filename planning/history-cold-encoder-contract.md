# Cold history byte controller: remaining composition contract

This contract records the single guarded runtime and conditional source-library proof checkpoint; complete finite-run and actual producer joins remain open.
Source checkpoint32f150be4 provides only the guarded NIL-tail probe;
9a955789d provides borrowed raw string/octet span emission. The actual
producer/pool adapter continues to call the resident byte cursor until this
controller has its own exact current-codec residual and preservation theorem.

## Source and stable byte boundary

Input is `(:decoded node)`, with the public c17 atom/pair/span representation.
A retained sidecar may replace classification only after a named invariant
proves its octet-list flag/count against the actual decoder's node abstraction.
No eager conversion to an ACL2 row is permitted.

Stable APIs: `fn-hrcur-cold-begin(source,capture,lease)`,
`fn-hrcur-cold-tick(cursor)` returning `mv verdict octet next`, and
`fn-hrcur-cold-supply(cursor,position,octet)` with the same result shape.
Verdicts are `:continue`, `:emit`, `:prepared`, explicit refusal, or
`(:need-byte position kind child-coordinate)`; every demand yields an unchanged
cursor. Supply operates on exactly the current child/request. Child serials
are local state, not substitutes for authenticated source authority.

The outer adapter must validate epoch, capture-ticket, pass, ordinal,
physical root-file pin and its monotonic request serial before supply. It
retains the physical pin and funding lease. Capture context and snapshot
lease references remain opaque here; no whole-root/file/lease equality or
invented ticket-width bound appears in a byte tick.

## One action per phase

* Task: pop one constant-size task. Scalar atoms start the existing scalar
  child; spans start canonical header/payload emission; pairs start a scan.
* Pair scan: inspect one tagged node/head. An octet atom head increments the
  carried count and advances to the cdr. A terminal opcode6 span contributes
  its carried payload length. An atom NIL closes the proper octet list.
  A raw opcode4 package1/2 length3 tail invokes the existing NIL probe.
* NIL probe: tick/supply once. NIL closes the opaque list; non-NIL rejects
  opaque classification. No general symbol-name materialization occurs.
* Rejected scan: retain the original node and the proven non-octets suffix
  fact. Expand one pair to car/cdr/opcode5 tasks. Carry that fact into the
  byte-head prefix's cdr tasks to avoid repeated suffix scans.
* Opaque payload: consume one pair byte head or one opcode6 borrowed byte.
  A carried remaining count reaching zero terminates without rereading the
  symbol-NIL tail. Generate canonical length header before payload emission.
* Scalar/span/normalizer: invoke one existing child operation. Full symbol
  normalization returns canonical opcode/package while keeping its original
  borrowed name span. For opcode0 NIL, pass target count0 to the span child
  while retaining the original source descriptor separately; it has no name
  payload. Old nonminimal length
  prefixes are regenerated canonically.
* Done: return prepared only after all tasks/children are empty.

Zero-length opcode6 spans abstract to NIL and emit opcode0. Strings are
never octet-list leaves. Remapped history row handles and original arena
payload handles remain separate outer source streams.

## Exact proof boundary and storage demand

The proof-only residual is precisely the remaining
`fn-scc-encode(fn-hdc-abstract node immutable-pool)` stream. Initialization
must equal that whole stream. Each emit removes exactly one octet;
continue/request removes none. The carried invariant establishes child
metadata and this residual relation and is preserved without executable
whole-node/suffix/pool validation. Supply requires the authenticated byte's
exact immutable-pool attribution; terminal residual is empty. Capture/lease
identity persists across every verdict. Reachable literal witnesses and
hypothesis removals accompany each cited keystone.

Task storage retains source references and an explicit continuation stack;
its maximum live demand depends on represented tree depth, not a guessed
profile ceiling. Scanner/opaque/child control is constant-size. Decoded
nodes, optional annotations, source pin, scratch reader, old/new cursors,
continuation stack and return/request objects coexist and require separate
funding. No physical pool, immediate reclamation refund, whole encoded-row
buffer, suffix-array doubling or image resize is assumed. Supported records
resume until complete; quantum exhaustion never truncates them.

Runtime implementation is in books/history-cold-record-runtime.lisp.
The separate books/history-cold-record-cursor.lisp exposes conditional residual
and invariant laws, productive rank descent and a terminating proof-only oracle run. Its state has nine fixed cells:
phase, pending tasks, child, original borrowed node, capture, lease, bounded
header prefix, active borrowed node, remaining opaque count. Cold tick returns
mv verdict/octet/cursor, matching the resident byte emitter. The exact demand
is (:need-byte position kind child-coordinate), where kind is :octet-nil,
:symbol-normalize, :span-body or :opaque-span. Supply takes cursor/position/byte
only after outer source4, pin, kind, persistent reader serial and buffer identity
checks. Every demand leaves the entire cursor unchanged. There is no Store,
file/path or opaque lease equality in these functions.

A failed pair classifier preserves the number of leading byte heads it has
visited. The controller places :no-octets tasks with that depth on the stack;
each postfix pair expansion decrements it for the cdr, until classification
must resume past the known failing head. This avoids repeated suffix scans
without a retained per-row suffix array or equality on whole subtrees. The
classifier proof-only prefix relation must be preserved before this cost and
semantic optimization can be claimed. A successful classifier emits a bounded
canonical opcode6/count header, then reads resident pair heads and borrowed
op6 span bytes. Exhausted remaining count stops without rereading a NIL tail.

Storage demand is concrete and must be funded by the outer owner. Every new
outer state allocates nine cons cells; old/new outer states may coexist. A
pair expansion adds three task-stack cons cells plus three fixed descriptors
(two/two-or-three/two cells). Node and immutable source references are borrowed,
not copied. The u64 opaque header has at most ten cells (opcode, digit-count,
at most eight digits). Normal scalar/span/NIL/normalizer child state allocation
is inherited from the named helper, and old/new child states coexist through
the return. Stack depth and total borrowed node retention depend on the actual
represented tree; no profile ceiling or pre-existing physical pool is assumed.
The source pin, task stack, child state, scratch/page buffers and overlapping
return values require lifetime/funding proof in the actual producer.

The normalizer scalar guard bounds offset/count/index by existing history u64
format and serial by the proved static-table initial work bound12250. The
serial+work conservation join is admitted in the cold source: initialization,
tick and supply preserve serial plus remaining work at most 12250. This number
is derived from the current import table, not a new stored-name limit. No runtime source
coerce/intern, whole-tree domain scan or whole encoded-row allocation occurs.

Full-controller progress measure (proof-only): use a lexicographic
triple of remaining structural credit, phase order, and current child work. A
queued :node has twice its ACL2 node count as credit; :no-octets has two fewer
credits, and a queued literal byte has one. Active classification has one fewer
credit than an unclassified node; other active phases have two fewer. This
accounts for classification rejection without resetting an equivalent task at
the same rank, and for pair expansion into two children plus postfix opcode5.
Phase order is work5, classifier/normalizer4, scalar/span/opaque-prefix3,
opaque2, opaque-span1, done0. Child work comes from the existing scanner, scalar,
span and normalizer measures, or the remaining prefix/payload count. The triple
is never evaluated on the served path. A demand is unchanged; an attributed
supply or productive tick must strictly lower the triple. The general rank
and finite exact-output proof now compose conditionally on the carried source domain.

Conditional source checkpoint: exact initializer, all-phase tick/supply residual
and invariant, permitted verdicts and emitted-octet boundaries now compose in
hrcrt1 after cached row (139 source body forms,31.79s/11,159,948steps;22proof
test forms,.07s/4,464steps). Matching public source admissions are reused; this
is not certification. Initial/tick/supply literal removals are explicit.
The ordinal rank and progress initializer are admitted; strict general
productive rank decrease and finite-run completion are supplied by the following conditional checkpoint.

Productive progress source checkpoint: every productive actual tick strictly
decreases the well-founded rank when the carried progress invariant holds;
prepared and byte-demand are excluded explicitly. Every attributed actual
supply strictly decreases the same rank under current demand, position and
immutable-pool byte attribution. Both operations preserve the progress
invariant. Nine literal positives/removals cover the two progress boundaries.

The proof-only fn-hrcur-cold-oracle-step invokes the actual tick, and on demand
invokes actual supply with nth(request-position, immutable-pool). Its recursive
fn-hrcur-cold-oracle-run terminates by the proved ordinal descent and equals
the exact current-codec residual. Initialization consequently returns the
complete fn-scc-encode(fn-hdc-abstract source pool), without fixed fuel or
truncation, for every supported source in the explicit domain. Five literal
full-stream positive/removal witnesses accompany the initializer. This oracle
is non-executable; it does not supply runtime bytes or establish physical I/O
liveness. Actual decoder/source lineage, authenticated reader/pin authority,
continuation funding and full producer qualification remain open outer joins.

## Actual byte decoder establishes the cold codec domain

`history-cold-source-lineage` carries numeric potential, consumed-byte weight,
scalar/package lineage and borrowed-node extents through the actual
`fn-hdc-feed` and `fn-hdc-model-run`. The numeric potential uses the current
one-octet digit width (at most 255 digits); decoded list weight is bounded by
consumed source bytes, including opcode6 collapse. Payload nodes retain
`offset + count <= source end`. These are non-executable proof models; the
served decoder never rescans a completed tree or evaluates the weight.

`fn-hdcl-current-successful-decoder-is-cold-codec-domain` establishes the full
recursive cold domain from an octet pool, natural offset and a slice ending
below the existing u64 bound and within that pool. It assumes no caller node
predicate. Nonnatural count cannot produce successful decoding, so the
conditional successful-result theorem removes that redundant premise.
`fn-hdcl-current-successful-decoder-retains-node-bounds` exposes the exact
borrowed-node source-end relation separately. The named
`fn-hdcl-current-decoder-cold-run-is-canonical-codec` then joins the actual
successful decoder to the terminating cold encoder oracle and exact canonical
`fn-scc-encode(fn-hdc-abstract result pool)`, including accepted nonminimal
length prefixes and symbol NIL aliases.

Thirteen literal test events cover actual numeric-prefix feed/run positives,
all feed/run preservation hypothesis removals, four successful result/domain
and extent cases, and two decoder-to-complete-stream positives. Corrupted
numeric cursors and source mutations are labeled separately. Practical literal
removals of the final slice/u64 result boundary remain partial; they are not
inferred from preservation tests. PRF-1088 remains planned with no certified
events. Authenticated source4/pass/pin byte attribution, physical funding,
provider liveness, complete producer/placement and qualification remain outer
composition obligations.

The existing decoder proof models are factored, byte-for-byte, into
`history-decode-lineage-model`; the old inverse refinement includes that leaf.
Actual decoder definitions and theorem statements are unchanged. Scoped
numeric inverse, move/feed and guard hints repair the carried field facts in
the cached-row theory. The expensive whole inverse replay is not evidence for
this lineage checkpoint.

## Actual based-provider decoder carry

`books/snapshot-based-provider-decoder-lineage.lisp` joins the existing
`fn-obp-begin` and `fn-obp-tick` to the actual decoder's numeric, consumed-byte
weight and borrowed-span lineage. Its immutable pool relation is proof-only;
the runtime and seventeen-cell provider representation are unchanged. The
begin law checks the declared pool against the logical pool length. The tick
law assumes the existing cursor guard and carried lineage, and preserves that
lineage through metadata, CHECK, decoder, padding, key and completion phases.
It does not require exact source-byte equality merely to preserve numeric or
span bounds. Successful `:done` completion yields the full cold codec domain
and node extents without a caller node-domain hypothesis.

The separate matched-byte equation names the actual `fn-obp-tick` call and
actual `fn-hdc-feed` result. Its premises are decode phase, current fixed-field
byte matching, and equality of the supplied scalar to the immutable pool's
current parser position. A terminal decoder freezes under feed, so an earlier
result=`:yield` premise was proved redundant and removed. The physical reader
owner must establish the exact pool observation equation and source4/pass/root
pin authority; this companion does not claim native authentication or lifetime.

Eleven ground witnesses include a complete actual metadata/decode/padding/key
trajectory ending in decoded output and practical hypothesis removals. Stale
serial and wrong-source observations are argument mutations; reassigned phases
and over-bound numeric cursors are labeled corrupted states. The carry guard's
u64-header removal remains partial because a materialized pool of that size
is not a practical fixture. Source admission reuses unchanged public events;
no certification, full parser inverse, controller funding, image or deployment
claim follows. Exact source and donor digests live in
`planning/evidence/snapshot-based-provider-decoder-lineage-source-2026-09-30.json`.

## Actual observation trajectory to decoder result

`books/snapshot-based-provider-observation-bridge.lisp` supplies proof-only
folds over an explicit observation list. `fn-obpt-replay` calls the existing
`fn-obp-tick` and its cursor projection at every step; `fn-obpt-decode-count`
counts only matched productive decoder supplies. `fn-obpt-observation-tracep`
names the exact trajectory condition: existing guards at reached cursors,
decode or later phases, and supplied scalar equality to the immutable pool at
the actual parser position on each productive decode step. It is no callback
or source oracle, and the host never executes these folds.

The generic replay theorem equates the actual final parser to the existing
`fn-hdc-model-run` at that count. Demand, stale, padding, key and terminal steps
preserve the parser. A named constructor projection shows that the actual
successful CHECK tick initializes `fn-hdc-begin`; callers do not invent a twin
decoder. Successful replay from initialized carried lineage retains the exact
decoder result, cold domain and borrowed-node extents. It assumes no caller
node-domain predicate. Four ground events cover the complete trajectory with
stale/request pauses and all three completion hypothesis removals, affirming
retained hypotheses and failure of the full conclusion. Wrong-pool arguments
and corrupted numeric state are labeled separately. The predecessor carry
guard/u64 removal remains partial. Reader page-to-pool attribution, source4/
pass/root pin authority, authentication, funding and qualification remain
outer obligations; no full inverse replay or new runtime process is needed.
