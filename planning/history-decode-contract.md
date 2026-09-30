# Bounded current-format history decode

The snapshot assembler uses `(:resident row)` for a borrowed resident suffix
row and `(:decoded node)` for an image row. The latter borrows one captured
history root, pool base, epoch and resource lease. A stable logical view pins the captured history mapping. One charged exact
checkpoint-file incarnation lease survives repeated scans; fixed page-buffer
borrows are acquired and released separately. Cancellation releases neither
an outstanding read nor its buffer before all actual borrowers return.

`books/history-decode-nodes.lisp` defines:

- `fn-hdc-atom(value)`: `(:atom value)`, for immediate NIL/natural/negative/character values and the fixed existing
  keyword `:hstxa`, recognized byte by byte without interning.
- `fn-hdc-pair(a,d)`: `(:pair a d)`, the decoded CONS instruction.
- `fn-hdc-span(op,pkg,offset,count)`: `(:span op pkg offset count)`.
  `offset` is the absolute byte offset within the immutable history pool
  region. `count` counts raw payload octets, excluding the instruction opcode,
  optional package octet and encoded length. Opcodes 3, 4 and 6 mean string,
  symbol and octet-list. The symbol package index is exactly 0 KEYWORD,
  1 ACL2 or 2 COMMON-LISP; the other opcodes use index 0.

The non-executable `fn-hdc-abstract(node,pool)` maps these nodes to the existing
logical value. It is proof vocabulary, never a materialization fallback.
The fixed-depth `fn-hdc-car` and `fn-hdc-cdr` support producer field remapping.
The producer transforms the existing held row's payload handle at field 4,
and the held row within `:hstxa`; all other nodes remain borrowed.

The encoder consumes nodes directly. A pair chain that abstracts to a nonempty
octet list must be classified incrementally and encoded as opcode 6. An empty
opcode-6 span abstracts to NIL and is canonically encoded as opcode 0. The
existing decoder accepts nonminimal numeric/length spellings; the encoder
regenerates their canonical numeric prefix rather than copying an entire old
instruction. Arbitrary package symbol names remain spans: the current history
codec's domain is not restricted to a fixed symbol vocabulary. Recognition of
fixed event tags compares their bounded expected spelling; it never interns an
arbitrary input name.

This contract preserves the current format. It adds no migration reader and no
admission ceiling. The current codec has an octet digit count (at most 255
little-endian numeric digits); history column lengths are u64. Profile validation
and the physical funding proof must establish representability and provision the
node stack/output. A byte parser does not alone fund either.

Status: constructors, abstraction and accessor equations admitted in protected
persvati REPL `hdc1` (13 forms, 5,481 prover steps). The byte parser, numeric
refinement, row semantic inverse, page authentication, padding and MKEY checks,
source-token matching, host composition and runtime evidence are separate
components under development. No complete bounded history reader is claimed.


The current parser API is `fn-hdc-begin(pool-offset,tree-length,epoch,lease)`
and `fn-hdc-feed(verified-byte,state)`. Its twelve fields are mode, opcode,
package, numeric cursor, span start, span count, remaining payload, absolute
pool position, tree end, node stack, epoch and lease. The last two are borrowed
opaque metadata, so the producer's two-natural lease fits without a new limit.
An active feed consumes exactly one byte. Terminal modes are `:done` and
`:refused`; only `:done` with a single stack node is a decoded tree.

The producer's authenticated source reader maps pool position to logical page
`pool-start + floor(position/16384)` and its byte offset. It must authenticate
captured-root directory, table and data pages before supplying a byte; logical
page number is never assumed equal to physical address. The page-source owner
implements that separate boundary through fixed scratch and streaming digest.
The old whole-directory/table open and pgsmem resize are not a fallback.
`fnn-snapshot-source-read-page(service,captured-source,request,maintenance-lease)`
is the agreed physical bridge under construction. MKEY verification needs a
bounded FNV fold over the decoded Message-ID span; calling the old materializing
row parser or hashing an abstract row would reintroduce the same obstruction.

PRF-1102 / SCN-1014 remain planned component evidence, with no production
keystone, manifest, image or native completion claim.


The current source checkpoint passed a clean protected persvati `hdc5` load:
27 stream-book forms (plus both source dependencies in proper encapsulates),
1,149,479 prover steps and 2.27 ACL2 seconds. Nineteen test body forms then
passed, including fifteen literal assertions and a ground non-executable
abstraction proof. The numeric residual's unnecessary shape and upper-byte
premises were removed only after the weaker theorem was admitted. These are
source admissions, not certification. No native module applies yet: this
component has no host caller. Full byte-stream semantic equivalence remains
open despite the finite compatibility witnesses.
