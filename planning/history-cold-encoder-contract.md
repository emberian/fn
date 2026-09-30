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
  borrowed name span. Opcode0 NIL has no name payload. Old nonminimal length
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
