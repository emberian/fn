# Resumable current-format scalar encoding

PRF-1095 / SCN-1010, a library component of S7/P12/D33. The complete
history builder, maintained source/profile domain, funding, host composition,
matching certification and native qualification remain separate open obligations.

`fn-hrsc-begin(atom, capture, lease)` retains three references in a fixed
ten-cell cursor. It does not inspect or encode the atom. `fn-hrsc-tick(cursor)`
returns `(mv verdict octet next-cursor)`: `:continue` advances a phase, `:emit`
emits one octet, `:prepared` means the atom is exhausted, and
`(:refused reason)` identifies malformed cursor, unsupported atom or current
codec width failure. Prepared is a codec result, never durable acceptance.

The source is the existing `fn-scc-atom-octets` in `store-tree-codec.lisp`.
NIL, naturals, negative integers with magnitude `-1-x`, characters, strings,
and symbols in KEYWORD/ACL2/COMMON-LISP use precisely its opcodes and package
indices. One counting tick divides a numeric remainder by 256. After opcode
and package emission the cursor emits the byte count, then little-endian digits
one per tick. String/name bodies use their retained string and a character
offset; no full `coerce`, character list, scalar byte list, reverse or final
materialization occurs. The prefix is at most two cells.

The existing length-octet format permits 255 digits, hence natural magnitudes
below `256^255` (2040 bits), and negative integers down to `-256^255`.
The runtime rejects wider integers before allocating their transformed negative
magnitude. Fixed cursor shape checks require numeric remainders and string
lengths within that existing format domain. The counting loop still resumes;
it never builds the digit list. `fn-scc-atomp` alone leaves string/name length
representability unstated. `fn-hrsc-domainp` adds that existing prefix condition
explicitly; this is not a new stored-data limit or profile choice. The controller
must additionally establish the image's u64 encoded-length and total padded
length constraints before allocating its backing store.

`fn-hrsc-invariantp`, `fn-hrsc-rest`, and `fn-hrsc-work` are logical proof
vocabulary, never executed by the runtime tick or its guard. The initial
refinement theorem equates the residual to the existing atom codec. The step
refinement preserves the exact emitted-byte/residual equation, allowed verdicts
and empty terminal residual. Separate theorems preserve the invariant, preserve
capture/lease identities on every branch, establish a single octet on emission,
and strictly decrease a natural work measure in every nonterminal invariant
state. The byte subject is the implementation the enclosing tree cursor will
call; no host caller is claimed yet.

Begin allocates ten cursor cells. A normal advancing tick allocates ten
replacement cells, with at most two additional prefix cells during setup.
A refusal reason has two cells; the multiple-value return representation,
stack, bounded-width arithmetic temporaries and actual runtime object sizes
also require funding. Old/new cursor objects may coexist. Strings, symbol names
and source atoms remain references; dropping one reference does not authorize a
resource refund or imply garbage collection. Runtime string length/indexing and
symbol-name access require the host representation contract. The controller
retains its immutable source epoch/pin and maintenance lease across census and
emission; this helper preserves supplied identities but does not establish
liveness or manufacture resource credit.

The scenario checks every reached scalar phase against the complete theorem
antecedents/conclusions, compares final bytes for all supported atom classes,
restarts after a yield, covers both 255-digit signed boundaries and the first
unrepresentable natural, and labels malformed-state and hypothesis-removal
witnesses separately. Source admission is not certification or qualification.
