# bp-crc-exec: the executed BP CRC-32C (2026-09-26)

Lane bp-crc-exec (Opus), the performance ledger's fix lane 2: row 11 of
planning/performance-2026-09-26.md, PKT-414's per-octet cost. Ids taken:
PRF-190, SCN-119, PKT-546. PKT-547 not taken (no decision arose). No wire,
delta or format code taken; the bytes of every bundle are unchanged.

## What changed

books/bp-primary.lisp, and nothing else in books/:

- `fn-bpp-xor` is `(mbe :logic <the bitwise recursion, unchanged> :exec (logand
  (logxor a b) (+ -1 (expt 2 k))))`.
- `fn-bpp-crc32c-scan` is `(mbe :logic <the bitwise scan, unchanged> :exec
  (fn-bpp-crc32c-scan-table crc xs))`. `fn-bpp-crc32c-scan-table` advances the
  register an octet at a time: `c = (logand (logxor crc x) #xFFFFFFFF)`, then
  `(logand (logxor (ash c -8) (fn-bpp-crc32c-table-ref (logand c 255)))
  #xFFFFFFFF)`, the classic table-driven CRC.
- `*fn-bpp-crc32c-table*` is `(fn-bpp-crc32c-table-rows 0)`: 16 rows of 16,
  every entry `(fn-bpp-crc32c-octet i 8)` evaluated from the bitwise definition
  at certification, so the table cannot drift from it. `fn-bpp-crc32c-table-ref`
  walks at most 30 conses.
- `fn-bpp-crc32c` and `fn-bpp-crc32c-scan` are declared `:verify-guards nil`
  at the defun and guard-verified by the book's existing `verify-guards`
  events, which now cite the keystone.

CRC-16 (type 1) keeps its bitwise scan; it runs the executed exclusive-or,
so it is faster too, but not table-driven (PKT-546 (2)).

## What is proved (PRF-190)

Two keystones, both `defthmd`, both used by the guard proofs of the `mbe`
functions:

- `fn-bpp-xor-is-masked-logxor`: `(implies (and (natp a) (natp b)) (equal
  (fn-bpp-xor a b k) (logand (logxor a b) (+ -1 (expt 2 k)))))`. No hypothesis
  on `k`: a width that is not a natural is no width and both sides are 0. The
  first statement carried `(natp k)`; no violating value existed, so the
  weakened theorem was proved and the hypothesis removed.
- `fn-bpp-crc32c-scan-table-is-scan`: `(implies (and (natp crc)
  (fn-cbor-octet-listp xs)) (equal (fn-bpp-crc32c-scan-table crc xs)
  (fn-bpp-crc32c-scan crc xs)))`.

The argument, all local to one `encapsulate`: exclusive-or over k bits is a
commutative, associative, self-cancelling operation with 0 as identity (proved
over `fn-bpp-xor` by induction on the width); one register step
`fn-bpp-crc32c-bit` is linear under it on 32-bit registers; so eight steps
(`fn-bpp-crc32c-octet`) are linear; a register splits as its low octet
exclusive-or 256 times its high part; eight steps of a register whose low
octet is zero shift it down by eight. Hence eight steps of `c` are the table
entry of `c mod 256` exclusive-or `c / 256` (local
`fn-bpp-crc32c-octet-is-table-step`), and `fn-bpp-crc32c-table-agrees`,
evaluated inside the proof, says the table holds `fn-bpp-crc32c-octet i 8` at
every `i` below 256 (local `fn-bpp-crc32c-table-ref-is-octet`).

No existing statement moved: the logical bodies of `fn-bpp-xor`,
`fn-bpp-crc32c-scan` and `fn-bpp-crc32c` are unchanged, so PRF-038's codec
round trip and books/bp-primary-invariants' CRC facts hold as they were; they
are cited, not restated. The arithmetic of `logxor`/`logand` (arithmetic-5 in
a local encapsulate, ihs quotient-remainder lemmas) never reaches an includer.

## Host lines and the assurance chain

Native entry: host/native/bp.lisp and host/native/bp-app.lisp call
`(fnn-core 'fn-bpn-host-send ...)`; host/bp-node-host.lisp `fn-bpn-host-send`
calls `fn-bpn-send` (books/bp-node.lisp), whose bundle is encoded by
`fn-bpb-encode`, each block's CRC by `fn-bpb-block-crc` ->
`fn-bpp-crc-octets` -> `fn-bpp-crc32c` -> `fn-bpp-crc32c-scan`; the decoder's
CRC check (`fn-bpb-decode`, host/bp-node-host.lisp `fn-bpn-host-authored-retry`
and the node machine's open, SCN-077) computes the same `fn-bpp-crc-octets`.
Executed subject: the guard-verified raw functions, i.e. the `:exec` bodies
`fn-bpp-crc32c-scan-table` and the masked `logxor`. Refinement: the two
keystones, discharged in the guard proofs. No maintained relation is needed:
the equalities hold for every input within the guard. Behavioural theorems:
PRF-038's round trip and the CRC facts over the logical bodies, unchanged.
Observed: the bytes below are the base image's, and the costs.

## Teeth (tests/acl2/bp-primary-tests.lisp)

- `(fn-bpp-crc32c-table-agrees 256)` by evaluation.
- A differential: 4,096 pseudo-random octets from two registers (the
  initial one and 0x12345678), the table scan against a test-local scan of
  eight bitwise register steps an octet (`fn-bpp-crc32c-octet`).
- The existing CRC vectors (RFC check values, the pinned bp7 samples) now run
  the executed bodies.
- `fn-bpp-crc32c-scan-table-is-scan`: a reachable witness asserting both
  hypotheses and the conclusion over the check string ("123456789",
  0xE3069283); without `(natp crc)`: crc = -1 over no octets gives -1 against
  0; without `(fn-cbor-octet-listp xs)`: xs = (1/2) gives 0 against
  4,067,132,163 (logxor reads 1/2 as 0, the bitwise step its parity).
- `fn-bpp-xor-is-masked-logxor`: two reachable witnesses (5 xor 3 = 6; 2^40+1
  xor 0 over 32 bits = 1, the mask truncating); without `(natp a)` and without
  `(natp b)`: 1/2 against 0 at width 1; the removed width hypothesis: k = -1
  gives 0 on both sides, in scope.

## Validation (by batch)

- persvati proof_repl, ACL2 8.7 w25: books/bp-primary admitted whole (198
  forms); books/bp-primary-invariants' 50 forms and the test book's 160 forms
  sent into that session (no certificate of the changed book exists in the
  cache, so neither can start a session of its own) and admitted.
- hbox, tools/hbox_native.sh d9e3f0321 tests.test_bp_node_native: its certify
  step certified the changed book and the default profile's 82 books above it
  (all 83 passed; bp-primary 8.74 s at 8 jobs with the box at load 12, of it
  5.4 s the two new encapsulates; manifest planning/evidence/manifests/certify-20260926T155415Z-2417777.json, bp-primary 8.83 s wall; the books there over 10 s, bp-node-forward-plan 11.2 s and bp-fragment-sweep 10.4 s, are unchanged by this lane).
- tests.test_bp_node_native on the lane's developer image
  (fn-host-developer.core 61fe6a44...): OK (27 ran, 0 skipped); run.log status 0;
  log SHA-256 62470c343abfd3ebb75e0e6a2958f3d8287c95e52fe83c3dfecd1d20230d24e8
  (hbox:/tank/fn/scratch/bp-crc-exec/native-d9e3f0321e15/). Chosen because it
  is the BP node module that authors, sends, receives and replays bundles
  through the native image (tests.test_native_bp_service does not exist).
- `make check-lane` green in the worktree.

## Measurements

hbox, 24 CPUs, load average 8.0 to 8.3 throughout (the box's other tenants of
the moment; stated per run in each .out), the perf-ledger harness extended
(planning/evidence/bp-crc-exec-2026-09-26/bpenc.lisp, measure.sh), two rounds; logs planning/evidence/bp-crc-exec-2026-09-26/bpenc-after-1.out and its siblings
of base then lane, back to back. Base: the perf-ledger's developer image
(dev f314a5a3, core addf58ae...; its codec books are byte-identical to dev
6407de336's). Lane: 61fe6a44... (d9e3f0321). Seconds, round 1 / round 2:

| payload | base encode | lane encode | base decode | lane decode |
| ---: | ---: | ---: | ---: | ---: |
| 49,152 | 0.171 / 0.178 | 0.003 / 0.002 | 0.366 / 0.356 | 0.007 / 0.006 |
| 262,144 | 0.918 / 0.955 | 0.015 / 0.013 | 1.839 / 1.906 | 0.037 / 0.034 |
| 1,048,576 | 3.684 / 3.847 | 0.058 / 0.054 | 7.651 / 7.709 | 0.140 / 0.142 |

At 1 MiB the lane's encode is 1.5 percent of the base's and its decode 1.8
percent (about 65 and 55 times faster). The base's figures here are half the
ledger's (8.0 and 15.4 s at 1 MiB): the ledger's run was on a busier box;
only the pair above is matched. The wire length and the raw-Lisp digest of
every wire are identical on both images (49,254 / 262,248 / 1,048,680 octets;
digests 1732517768605067727, 351141540838418460, 221726367095178201), and
both images decode each wire back to its bundle. Allocation is unchanged
(the same bytes consed): the CRC's arithmetic never allocated; the codec's
48 bytes an octet is the octet-list representation. Output SHA-256s:
before-1 62fe5582..., after-1 c36891d7..., before-2 c77c4448...,
after-2 2554b1cb... (bpenc-SHA256SUMS).

## Row 11 and PKT-414

Row 11 narrowed: the CRC share (99.4 and 95.4 percent of encode and decode)
is gone; a 1 MiB bundle encodes in 0.06 s and decodes in 0.14 s on the lane's
image (the ledger predicted about 0.1 s). What is left of the row is the
codec's octet-list allocation and, at the node, PKT-308 (4)'s three encodes a
row and SCN-077's open (PKT-546). PKT-414 narrowed in
planning/backlog-2026-09-25.md: its per-octet cost is this; the three scans
per step remain.

## What is NOT done, and why

- SCN-077's receiver open (51.9 s at 1,311 rows) was not re-measured: it needs
  the dtn-developer image and bp-lifecycle-5's open.py over a 10 MiB fragment
  flow, and this lane builds one image (the developer image, for its one
  module). Expected from the profile: its 39.2 s of encode and decode fall to
  well under a second, leaving the quadratic `fn-bpnf-held-octets` (10.0 s)
  and the three encodes a row (PKT-308 (4)); PKT-546 (1).
- CRC-16 is not table-driven (PKT-546 (2)); fn authors CRC-32C (type 2).
- The codec's allocation (48 bytes an octet, octet lists; D27's concrete
  representation) is untouched; this lane moved only the CRC's arithmetic.
