# Cold history byte controller: remaining composition contract

This is the next implementation contract, not an admitted controller.
Source checkpoint32f150be4 provides only the guarded NIL-tail probe;
9a955789d provides borrowed raw string/octet span emission. The actual
producer/pool adapter continues to call the resident byte cursor until this
controller has its own exact current-codec residual and preservation theorem.

## Source and stable byte boundary

Input is `(:decoded node)`, with the public c17 atom/pair/span representation.
A retained sidecar may replace classification only after a named invariant
proves its octet-list flag/count against the actual decoder's node abstraction.
No eager conversion to an ACL2 row is permitted.

Proposed APIs: `fn-hrcur-cold-begin(source,capture,lease)`,
`fn-hrcur-cold-tick(cursor)` returning `mv verdict octet next`, and
`fn-hrcur-cold-supply(cursor,position,octet)` with the same result shape.
Verdicts are `:continue`, `:emit`, `:prepared`, explicit refusal, or
`(:need-byte position child-request)`; every demand yields an unchanged
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

Runtime implementation now exists in books/history-cold-record-cursor.lisp
(WIP, no source-ready/full inverse claim). Its state has nine fixed cells:
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
