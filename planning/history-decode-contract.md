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


Current-codec symbol normalization is an additional bounded component in
`books/history-symbol-normalize.lisp`. Package index 1 can name imported
COMMON-LISP symbols, and `NIL` in packages 1 or 2 denotes NIL rather than a
non-NIL symbol. An authenticated page digest does not imply canonical spelling.
The normalizer derives the exact import table from `(pkg-imports "ACL2")`,
proves all its home packages COMMON-LISP, and verifies that the other two codec
packages have no imports. Arbitrary names remain borrowed spans.

`fn-hdsn-begin(pkg,offset,count)` creates a seven-cell cursor.
`fn-hdsn-tick(cursor)` returns two values: `:continue`, `(:need-byte offset
serial)`, `(:done (opcode package))`, or `:refused`, plus the next cursor.
`fn-hdsn-supply(offset,serial,byte,cursor)` consumes one exact requested byte,
returns `:continue` and the next cursor, or refuses without advancement.
A tick skips at most one static candidate; a supply compares one source byte
against one character of the existing imported symbol name. Neither operation
assembles or interns the input name. Opcode 0 means NIL; otherwise opcode 4 and
the canonical package accompany the original name span unchanged. Names are
case-sensitive. Keyword NIL and all T spellings retain the appropriate symbol
instruction. The authenticated provider and controller retain the captured
root/file lease, epoch, pass, row ordinal and read ownership throughout the
scan; the local request serial also rejects duplicate and stale completions.

Named semantic obligations connect classification to the existing
`fn-scc-intern`, establish initial residual meaning, preserve that meaning
through actual tick and byte-supply calls, and identify the terminal descriptor.
The supplied byte must equal the corresponding character of the logical source
name, and the source length must be the cursor's count. These are provider
refinement premises, not runtime whole-name checks. Coherence is established at
begin and preserved; each successful candidate skip or byte comparison strictly
decreases a proof-only remaining-work measure. The selected table contains 978
imports and has measure 12,249; initial remaining work is at most 12,250,
independent of source name length. This bounds productive scan transitions;
a waiting read remains pending and is not charged as productive advancement.
Under the same test driver, ACL2 CAR used 160 ticks and 9 byte supplies, ACL2 NIL
611 and 29, an unmatched `fn-private-name` 979 and 41, and COMMON-LISP NIL 4 and 3.
A static trie could reduce aggregate work but is not needed for bounded ticks.

The source-row request token is now `(epoch lease pass ordinal)`, with a
monotone pass on restart. The normalizer's serial is local to that outer token;
providers must not accept a prior pass merely because its offset is identical.
The mandatory transit-binding schema extension appends a held-row field; it
does not change this generic postfix decoder or symbol normalizer. Fixed-depth
producer remapping must use the producer's current schema, not a cached arity.

The symbol normalizer checkpoint passed a clean protected hbox `hdsn3` test-root
load with all four source dependencies encapsulated: 27 test-root forms,
4,840,666 total prover steps and 11.30 ACL2 seconds. Nineteen literal assertions
and four ground semantic proofs passed. The narrow theory and teeth checks have
zero findings. These are source admissions; no certificate, host invocation,
qualified image or full decoder inverse is claimed.

The normalizer now includes only `store-tree-codec`, so encoders can consume it
without importing the byte parser. A clean protected persvati `hdsn4` test-root
replay with the normalizer in one encapsulate passed all 27 forms, 3,628,003
prover steps and 8.29 ACL2 seconds. Its narrow API and semantics are unchanged.


The generic current-format inverse is now a source proof in
`books/history-decode-refinement.lisp`: `fn-hdc-current-codec-refinement`
equates the abstraction of repeated public `fn-hdc-feed` calls followed by
`fn-hdc-result` to `fn-scc-decode-tree` over every natural in-bounds slice of
an immutable octet pool. Malformed programs and nonminimal scalar spellings
are included. `fn-hdc-result` returns `(:ok node)`, `(:yield)` or
`(:refused :tree)` with fixed-depth access. The whole-pool model runner and
abstraction are proof-only, never served functions.

The per-feed inverse requires coherent carried parser state, an octet pool,
end within that pool, an octet supplied byte, and equality of that byte with
the immutable source at the parser position. A separate recursive invariant
names proper atom/pair/span shape and every span's nonnegative start/count
with start+count at most captured end. Actual feed preserves it. It is carried
proof vocabulary and never evaluated as a whole-tree runtime check. General
run-level epoch/lease preservation and fuel partition justify suspension
within payload and early malformed refusal. They do not establish physical
pin lifetime, allocation funding or authenticated provider bytes.

Literal source tests assert complete inverse premises and conclusion for
NIL, empty octets, nonminimal numbers, import NIL alias, arbitrary symbol,
string/CONS, embedded slices and malformed opcode/package/stack/length
programs. Source-byte hypothesis removal and separately labeled corrupted
cached-tag/stack witnesses affirm all retained premises and conclusion
failure. The octet-pool and negative-offset removal candidates remain
unestablished; failed proof search is not evidence of necessity.

PRF-1102 remains planned because authenticated page-byte mapping, outer token
matching, row columns/padding/MKEY, canonical cold reencoding, concrete node
funding and the actual host composition remain open. Source admissions carry
no certificate, qualified image or deployment coordinate.
