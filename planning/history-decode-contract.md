# Bounded current-format history decode

The snapshot assembler uses `(:resident row)` for a borrowed resident suffix
row and `(:decoded node)` for an image row. The latter borrows one captured
history root, pool base, epoch and resource lease. Its generation pin survives
all reads and all consumers; cancellation does not release it before outstanding
I/O and buffer borrowers return.

`books/history-decode-nodes.lisp` defines:

- `fn-hdc-atom(value)`: `(:atom value)`, for immediate NIL/natural/negative/character values.
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
