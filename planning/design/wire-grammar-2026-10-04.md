# Exported wire grammars and the store-identity command (Mini M4, M5) — 2026-10-04

Lane `mini-contract`. Sources: `redregg/work/FN-660-RESPONSE-20261004.md` §M4–M5
and `redregg/designs/MINI-FN-660-REQUIREMENTS-20261004.md` §M4, §M5, §3.2
("Mini *generates* its decoder from the export and never hand-parses"; the
codec decision: Mini reads FNCT frames and `fncu` directly, `--json` and CLI
text leave the contract).

## The rule today

- Each control frame has a hand-written ACL2 encoder and decoder per kind
  (`consumer-local-control`, `consumer-wait-codec`, `consumer-reason`,
  `native-control-reason`, `native-hybrid-control`, ...). Some round trips
  are proved for some kinds, in one direction.
- `fncu` (`consumer-position`) has `dec∘enc` (`fn-cp-cursor-decode-encode-roundtrip`)
  and no `enc∘dec`.
- FNCT kinds collide under one magic: 4 is both the consumer request and the
  hybrid enrolment, 5 the consumer reply and the hybrid author request, 7 and
  8 likewise. The owner tries decoders in turn.
- `tools/protocol_emit.py` reads `books/protocol-table.lisp` without
  evaluating it and prints NNTP-only JSON. Nothing exported is versioned and
  nothing exported is produced by ACL2.
- No command prints the genesis node identity, schema digest or format word.

## Decision (lane lean; the format is the lane's to propose, per brief)

### 1. One grammar language, one interpreter, generic round trips

A grammar is ACL2 **data**: a tree of the nodes below. `books/wire-grammar.lisp`
(prefix `fn-wg-`) defines

- `fn-wg-grammarp G`: the tree is well formed (the static rules below);
- `fn-wg-valuep G V`: V is a value of G;
- `fn-wg-encode G V`: octets;
- `fn-wg-decode G OCTETS`: `(:ok V REST)` or `(:refused REASON)`, REASON `:trailer`
  (a frame whose trailer is not the digest of its protected prefix) or
  `:malformed` (every other refusal);

and proves, once, for every well-formed grammar:

- `fn-wg-decode-of-encode`: `(fn-wg-decode G (append (fn-wg-encode G V) R)) = (:ok V R)`
  for a value V of G and octets R, when G is delimited or R is empty;
- `fn-wg-encode-of-decode`: if `(fn-wg-decode G B) = (:ok V R)` then V is a
  value of G and `(append (fn-wg-encode G V) R) = B`.

So for a whole message (decoded with nothing left over) `dec∘enc = id` on
values and `enc∘dec = id` on accepted octets.

**Canonicity is part of well-formedness, and `fn-wg-encode-of-decode` is
its theorem** (Mini's point 1): every octet string a well-formed grammar
accepts is the encoding of the value it decodes to, so each value has
exactly one accepted encoding. The language has no optional whitespace, no
line-ending variants (`:line` and `:base64-lines` end lines in CR LF only),
fixed-width big-endian integers with no leading-zero variants (the width is
the grammar's), base64 that is padded and canonical (the pad bits are zero:
`fn-ot-b64-accepted-is-canonical`, `books/octet-text.lisp`, the one base64
in the tree), and a tail-only node (`:rest`, `:maybe`, `:base64-lines`) only
in last position.

A family's grammar is a `defconst`. A **new** codec (the store identity, M4;
the application article kind, M6) uses the interpreter as its codec — there
is no hand-written encoder beside it. An **existing** hand-written codec the
host calls gets an agreement theorem with the interpreter at its grammar
(the host's decoder accepts exactly what `fn-wg-decode` accepts, with the
same value under a named projection; the host's encoder is `fn-wg-encode`
on valid values). That is the theorem that makes the export a description of
the bytes fn actually sends and reads; the round trips are then the generic
ones, instantiated. Replacing a hand-written codec by the interpreter is the
end state and a later step per family (it moves theorems downstream).

### 2. The nodes (language `fn-wire-grammar`, version 1)

ACL2 form / JSON form / value / encoding:

| node | JSON | value | octets |
|---|---|---|---|
| `(:const OCTETS)` | `["const","HEX"]` | `nil` / `null` | exactly those octets |
| `(:uint W LO HI)` | `["uint",W,LO,HI]` | natural LO..HI / number | W octets big-endian, W ∈ {1,2,4,8} |
| `(:bytes W LO HI CLASS)` | `["bytes",W,LO,HI,"CLASS"]` | octet list / hex string | W-octet big-endian length L, LO ≤ L ≤ HI, then L octets of CLASS |
| `(:rest LO HI CLASS)` | `["rest",LO,HI,"CLASS"]` | octets / hex | every remaining octet (tail only) |
| `(:line LO HI CLASS)` | `["line",LO,HI,"CLASS"]` | octets / hex | L octets of CLASS (LO ≤ L ≤ HI) then CR LF; CLASS excludes CR |
| `(:base64-lines WIDTH LO HI)` | `["base64-lines",WIDTH,LO,HI]` | octets / hex | `fn-ot-b64-encode` (RFC 4648, padded) of the value, cut into lines of WIDTH characters (the last 1..WIDTH), each followed by CR LF; the empty value is no lines (tail only); decoding accepts exactly that layout |
| `(:enum W BASE (NAME...))` | `["enum",W,BASE,["name",...]]` | a name / string | W octets big-endian: BASE + the name's 0-based position |
| `(:seq G...)` | `["seq",[G,...]]` | list, one per element / array | the elements in order |
| `(:tag W (CODE NAME G)...)` | `["tag",W,[[CODE,"name",G],...]]` | `(NAME V)` / `["name",V]` | W-octet code, then the arm |
| `(:maybe G)` | `["maybe",G]` | `nil` or `(V)` / `[]` or `[V]` | nothing, or G's octets (tail only; G's octets are never empty) |
| `(:where G CHECK...)` | `["where",G,[CHECK,...]]` | G's value / same | G's, accepted only when every check holds on the `:seq` value |
| `(:frame MAGIC VERSION KIND MAX G)` | `["frame","HEX",VERSION,KIND,MAX,G]` | G's value / same | MAGIC(4) VERSION(1) KIND(1) LENGTH(u32 BE, ≤ MAX) PAYLOAD TRAILER(32); PAYLOAD is G's octets, all of them; TRAILER = BLAKE3-256 of everything before it (`fn-frame-digest`) |

CHECKs over a `:seq` value's elements (0-based indices; each element named
must be a natural, else the check fails): `(:le I J)` / `["le",I,J]`
(element I ≤ element J), `(:eq I J)` / `["eq",I,J]`, `(:diff K J I)` /
`["diff",K,J,I]` (element K = element J − element I, J ≥ I). Both
interpreters evaluate them over values already decoded (Mini's point 2).

CLASSes: `"any"` (every octet), `"utf8"` (RFC 3629, the `utf8` book's
decoder, as `:text` frame fields), `"header"` (HTAB, SP, `!`..`~`: RFC 5322
field-body octets; excludes CR, so `:line` is self-delimiting).

**This section is normative** (the text Mini's interpreter is written from;
`books/wire-grammar.lisp` is its ACL2 definition and
`tests/test_wire_grammar.py` an independent reading of it).

Well-formedness (`fn-wg-grammarp`), exactly:
- `const`: OCTETS is a list of octets (possibly empty).
- `uint`: W ∈ {1,2,4,8}; 0 ≤ LO ≤ HI < 256^W.
- `bytes`: W ∈ {1,2,4,8}; 0 ≤ LO ≤ HI < 256^W; CLASS ∈ {any, utf8, header}.
- `rest`: 0 ≤ LO ≤ HI; CLASS ∈ {any, utf8, header}.
- `line`: 0 ≤ LO ≤ HI; CLASS is `header` (the only class without CR).
- `base64-lines`: WIDTH ≥ 1; 0 ≤ LO ≤ HI.
- `enum`: W ∈ {1,2,4,8}; BASE ≥ 0; NAMES non-empty, distinct;
  BASE + count(NAMES) ≤ 256^W.
- `seq`: every element well formed; every element but the last delimited.
- `tag`: W ∈ {1,2,4,8}; each arm `[CODE, NAME, G]` with 0 ≤ CODE < 256^W and
  G well formed; codes distinct; names distinct. (A `tag` with no arms is
  well formed and accepts nothing.)
- `maybe`: G well formed and non-empty (no value of G encodes to nothing).
- `where`: G a well-formed `seq`; each check `["le",i,j]`, `["eq",i,j]` or
  `["diff",k,j,i]` with natural indices. A check holds only when every
  element it names is a natural number (an index past the end, or a
  non-number element, fails the check).
- `frame`: MAGIC 4 octets; VERSION and KIND octets; 0 ≤ MAX < 2^32; G well
  formed (G need not be delimited: the frame's length delimits it).

Delimited (`fn-wg-delimitedp`): `const`, `uint`, `bytes`, `line`, `enum`,
`frame` are; `rest`, `maybe`, `base64-lines` are not; a `seq` is when all its
elements are (the empty `seq` is); a `tag` when all its arms' grammars are;
a `where` when its `seq` is. Non-empty (`fn-wg-nonemptyp`): `const` with
octets, `uint`, `bytes`, `line`, `enum`, `frame`, `tag`; `rest` and
`base64-lines` with LO ≥ 1; a `seq` with a non-empty element; a `where` whose
`seq` is; never `maybe`.

Decoding (`fn-wg-decode G XS` → `(:ok V REST)` or `(:refused R)`), per node,
on the octets XS, in this order:
- `const`: XS starts with OCTETS → value null, rest after them.
- `uint`: at least W octets and LO ≤ n ≤ HI for n their big-endian value.
- `bytes`: at least W octets; n = their value; LO ≤ n ≤ HI; at least n more
  octets; those n are of CLASS → value those n octets.
- `rest`: LO ≤ |XS| ≤ HI and XS of CLASS → value XS, rest empty.
- `line`: v = the octets before the first CR (all of XS if none); XS
  continues with CR LF after v; v of CLASS; LO ≤ |v| ≤ HI → value v, rest
  after the CR LF.
- `base64-lines`: text = unlines(WIDTH, XS), where unlines takes the whole
  remainder: while octets remain, if at most WIDTH+2 remain the line is all
  but the last two, else the first WIDTH and skip WIDTH+2; XS must equal
  lines(WIDTH, text) (text cut into WIDTH-octet lines, the last 1..WIDTH, each
  followed by CR LF; empty text is no lines); text must be canonical padded
  RFC 4648 base64 (length a multiple of 4, alphabet `A-Za-z0-9+/`, `=` only
  as the last one or two, zero pad bits) of v; LO ≤ |v| ≤ HI → value v, rest
  empty.
- `enum`: at least W octets; BASE ≤ n < BASE+count → value NAMES[n−BASE].
- `seq`: each element in turn on what the previous one left; value the list
  of their values (a `const` contributes null).
- `tag`: at least W octets; n their value; the arm whose CODE is n decodes
  what follows → value [NAME, V]; no such arm → refused.
- `maybe`: XS empty → value [] (rest empty); otherwise G → value [V].
- `where`: G, then every check on its value.
- `frame`: at least 4 octets and the first 4 are MAGIC; then at least 2 more,
  VERSION and KIND; then at least 4 more, n their value; n ≤ MAX; at least
  n+32 octets after the length; the 32 after the n payload octets equal
  BLAKE3-256 of everything before them (magic through payload) — else
  refused **`trailer`**; then G on exactly the n payload octets must succeed
  with nothing left (a refusal inside G is the frame's refusal) → value G's
  value, rest after the trailer.
Every other failure is refused **`malformed`**. A MESSAGE is accepted when
the decoder answers ok with nothing left.

Encoding is the inverse, node by node: `const` its octets; `uint` W-octet
big-endian; `bytes` W-octet length then the octets; `rest` the octets;
`line` the octets then CR LF; `base64-lines` lines(WIDTH, base64(v));
`enum` W-octet BASE+position; `seq` concatenation; `tag` the arm's W-octet
CODE then its encoding; `maybe` nothing or G's; `where` G's; `frame` MAGIC,
VERSION, KIND, 4-octet length of the payload, the payload, then BLAKE3-256 of
all of that.

Names are symbols in ACL2 and their lower-case print names (no colon) in
JSON.

Value JSON: octets are lower-case hex; numbers are JSON integers (Lean's
`Lean.Json` reads them exactly, beyond 2^53).

### 3. The export: `specs/wire-grammar.json`, written by ACL2

`books/wire-grammar-export.lisp` holds the family table and a renderer that
builds the JSON text **in ACL2** (the bytes of the file are an ACL2 value).
`python3 tools/protocol_emit.py --wire --write` runs ACL2 (through
`tools/acl2`) over that book and writes the text; `--wire --check` compares
it with the committed file; `make wire-grammar` and the `--check` in the
fast checks. Shape:

```json
{"format":"fn-wire-grammar","version":1,
 "trailer":"blake3-256",
 "families":[
   {"name":"fncu.cursor","grammar":[...],
    "acl2":{"encode":"fn-cp-cursor-encode","decode":"fn-cp-cursor-decode",
            "agreement":["..."],"round-trips":["fn-wg-decode-of-encode","fn-wg-encode-of-decode"]},
    "vectors":[{"value":[...],"octets":"666e637501..."}]},
   ...],
 "exchanges":[{"request":"fnct.store-identity.request","replies":["fnct.store-identity.reply","fnct.reasoned-reply"]}],
 "words":{"exit-classes":[...],"control-statuses":[...]}}
```

`vectors` are `fn-wg-encode` evaluated in ACL2 on values the table names
(including the boundary values: empty and widest fields, every tag arm).
Each vector carries its family name and the file's language version
(Mini's point 4). Every family whose grammar is a frame also carries
refusal vectors: the first accepted vector with one trailer bit flipped,
answered `{"refused":"trailer"}`, and a truncated one, answered
`{"refused":"malformed"}` (Mini's point 3: a wrong trailer is a named
refusal, distinct from a decode failure). For each request family,
`exchanges` lists every reply family it can receive — the refusal and
uncertain answers (`fnct.reasoned-reply`, `fnct.line-reply`, the plain
reply's `refused`/`uncertain`/`fault` arms) included — and those families
carry vectors for each status word (Mini's point 5: Reply / Refused /
Unknown checked against bytes).

**The file's digest.** `fn-wg-export-digest` is BLAKE3-256 of the file's
octets, computed in ACL2 from the same value the emitter writes. The
running image reports it in the M4 identity reply (`grammar-digest`), so
one command pins format word, node identity, schema digest, history,
incarnation, both revisions and the grammar file; Mini computes BLAKE3 of
the file it loaded at its pinned revision and compares.
The file's `version` is the language version; an unknown version is refused
by name on both sides. Family names carry their own version where the bytes
do (`fncu` version 1, FNCT version 1 are in the grammar's constants).

Mini's side (the contract statement of MINI §3.2): one Lean interpreter of
the same language with its own two round-trip theorems, the grammars loaded
from this file, and a CI check that it decodes every vector to its value and
re-encodes to identical octets. Lean needs BLAKE3-256 for the trailer (a
trusted primitive on Mini's side, as SHA-256/cSHAKE are).

### 4. Families in v1

Keyed by **family**, never by FNCT kind (the kind-4/5/7/8 collisions): a
client knows which family it expects from the request it sent (`exchanges`).

1. `fncu.cursor` — agreement with `fn-cp-cursor-encode`/`-decode`; closes
   C-0c (`enc∘dec`).
2. `fnct.store-identity.request`, `fnct.store-identity.reply` — new (M4,
   below); the interpreter is the codec.
3. `fnct.consumer.request` (kind 4), `fnct.consumer.reply` (5),
   `fnct.consumer.status-reply` (9), `fnct.consumer.poll-reply` (6),
   `fnct.consumer.reasoned-request` (22), `fnct.reasoned-reply` (18),
   `fnct.line-reply` (23) — agreement theorems with the host-called codecs.
4. `fnct.hybrid.author-request` and its reply — the posting path Mini uses
   (N10).
5. `fn-store-identity` text line, exit classes and status words as `words`.
6. M6's article kind (lane zmq owns the grammar constant and the acceptance
   theorem; the interpreter is its renderer and recognizer).

Not in v1 (named, not silently dropped): the `fn-e` poll-report record
(CBOR, `books/stx-accept-records.lisp`; needs CBOR nodes — v2), the FNWD
withdrawal report, and FNCR (QF-12: FNCR is a **distinct envelope**,
magic `FNCR`, spec-driven fields, `books/consumer-remote-codec.lisp`; it
never enters FNCT dispatch; the remote-consumer lane's family, same
language, added when it lands on dev).

### 5. M4: one command, answered by the owner

`fn store identity CONTROL` sends `fnct.store-identity.request` (FNCT kind
24, empty payload) over the 0600 control socket; the owner answers
`fnct.store-identity.reply` (FNCT kind 25), a `:seq` of

`format` (text), `node` (32 octets), `schema` (32), `profile` (32),
`history` (1..64), `incarnation` (1..64), `created-revision` (text),
`running-revision` (text), `grammar-digest` (32)

— the genesis record the open read (`fn-store-genesis`, the verdict of
`fn-gen-open`), the consumer state's history id and incarnation, and the
running image's recorded source revision. The CLI prints the ACL2-rendered
line `fn-store-identity-v1 format=… node=… schema=… profile=… history=…
incarnation=… created-revision=… running-revision=…` (a protocol-table
style row with its key and text), exit 0; refusals by name. Why the owner
and not an offline verb on ROOT: history id and incarnation live in the
owner's consumer state (a replay offline), and the **running** revision is
the owner process's image, which an offline verb (another process, perhaps
another image) cannot report. An NNTP `XFN-STORE` row (M4-c) is a later
slice over the same renderer.

## What would change this

- Mini preferring a closed set of per-family Lean decoders over one
  interpreter: the export still serves (each family's tree generates code),
  only Mini's side changes.
- A CBOR-node requirement for 6.6.0 (QF-14): v2 of the language adds
  `cbor-uint`, `cbor-bytes`, `cbor-array` nodes before `fn-e` joins.
