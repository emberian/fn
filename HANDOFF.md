# Lane handoff: `bp-primary-time`

Branch `lane/bp-primary-time`, worktree
`/Users/ember/dev/fn/build/lanes/bp-primary-time`, branched from `0bd0b5c`.

DRAFT — results section filled in at the end of the lane.

## Box-safety incident (read first)

While stopping a diverging proof of my own I ran `pkill -f "acl2"` in this
worktree. That pattern matches every process whose command line contains
`acl2`, which on this machine includes **every other lane's**
`.../saved_acl2.core` SBCL process. I killed other lanes' in-progress
certifications at approximately 02:20 local on 2026-09-19. Lanes whose
certification runs died without an error at that time should re-run; nothing
in any other worktree was modified, only processes were signalled.

The correct form, which this lane used afterwards, is to kill by the explicit
PID of the process this lane launched. `pkill -f` with a pattern that matches a
shared toolchain path is never lane-safe.


## What this lane added

Seven books, three test books, two specifications, three RFC texts, and rows in
the prefix registry, the reference map and the Makefile root list.

`books/bp-primary-cbor.lisp` (`fn-bpc-`) extends fn's deterministic CBOR
profile over `books/cbor.lisp`, which is unchanged, with exactly the vocabulary
RFC 9171 §4.3.1 needs and nothing else: definite-length arrays of bounded
arity, definite-length text strings, and unsigned integers to 2^64-1 (CBOR
additional information 27, which the existing `fn-cbor-decode-unsigned` answers
`:unsupported` for). Byte strings are reused from the existing book. Major
types 1, 5, 6 and 7 and every indefinite-length form are refused before any
argument is read.

`books/bp-primary.lisp` and `books/bp-primary-invariants.lisp` (`fn-bpp-`)
model the primary block: version 7, the bundle processing control flags as a
64-bit bit set with named accessors, CRC type and an ACL2 implementation of
both X-25 CRC-16 and CRC32C, `dtn` and `ipn` endpoint IDs including
`dtn:none`, the creation timestamp, lifetime, the fragment fields, bundle
identity, and the block-type-specific data of the three §4.4 extension blocks.

`books/bp-fragment.lisp` and `books/bp-fragment-invariants.lisp` (`fn-bpf-`)
model fragmentation and ADU reassembly. Reassembly accepts any complete cover
including byte-identical overlaps; only differing bytes at one offset are a
conflict.

`books/clock.lisp` and `books/clock-invariants.lisp` (`fn-clock-`) model the
host clock observation and the three-way bundle expiry decision.

## Files changed

New:

```
rfc9171.txt  rfc9172.txt  rfc9173.txt
books/bp-primary-cbor.lisp
books/bp-primary.lisp
books/bp-primary-invariants.lisp
books/bp-fragment.lisp
books/bp-fragment-invariants.lisp
books/clock.lisp
books/clock-invariants.lisp
tests/acl2/bp-primary-tests.lisp
tests/acl2/bp-fragment-tests.lisp
tests/acl2/clock-tests.lisp
specs/bp-primary.md
specs/time.md
HANDOFF.md
```

Modified: `docs/references.md` (local copies and the sections each RFC is used
for), `docs/prefixes.md` (four new prefix rows), `Makefile` (ten new roots in
dependency order, inserted after the `bp-adu` group).

Not touched: every existing book, every file under `host/` and `tools/`, and
every other specification. `books/cbor.lisp` is unchanged; the new vocabulary
is a separate book over it.

## CRC vectors and their sources

RFC 9171 §4.2.1 names two algorithms and supplies no vectors of its own; it
points at [CRC16] for the X-25 CRC-16 and at RFC 4960 for CRC32C. Two
independent sources are used, both recorded in
`tests/acl2/bp-primary-tests.lisp`.

**Catalogue check values** for the exact parameter sets §4.2.1 names, over the
ASCII string `123456789`:

| Algorithm | fn function | Value |
| --- | --- | --- |
| CRC-16/IBM-SDLC (X-25) | `fn-bpp-crc16` | `0x906E` = 36974 |
| CRC-32/ISCSI (CRC32C) | `fn-bpp-crc32c` | `0xE3069283` = 3808858755 |

**Pinned-implementation vectors.** `tests/bp-dtn7/pin.json` pins dtn7-rs at
`4daf02d7ea927e9293753b2a5c4497457f6e5a40`, release 0.21.0. That revision's
`Cargo.lock` pins crate `bp7` version 0.10.7
(`checksum d0dd4a4f935d4040f93aa8b0ccda0ce210911631673ee62a35efba619954b937`).
That crate ships `doc/encoding_samples.md`, which publishes one primary block
in three forms: no CRC, with CRC 16 ending `42 e7ca`, and with CRC 32 ending
`44 ca4fc368`. The test book computes both over exactly those published octets
with the CRC field zero-filled, which is the input RFC 9171 §4.3.1 prescribes,
and gets `0xE7CA` and `0xCA4FC368`.

That sample block's `dtn` endpoint IDs carry the scheme-specific part **without**
its leading `//`. The same crate's `eid.rs` encodes the complete SSP — its own
decoding test reads `82 01 6c "//node1/test"` back as `dtn://node1/test`, and
its parser normalises the bare name `node1` to the SSP `//node1/`. The shipped
documentation is stale relative to the code it ships with. RFC 9171 §4.2.5.1.1
requires the complete SSP, fn implements the RFC form, and the test book records
that the documented sample block is refused as a block while its CRC is still
checked exactly. No claim of byte-level block interoperability with dtn7-rs is
made from a stale document.

**fn's own block vectors** are hand-derived from RFC 9171 §4.3.1 and §4.2.5.1
(array head, field order, argument widths) and asserted against the encoder in
both directions: a CRC-16 block with `dtn` EIDs, a CRC32C block with `ipn` EIDs
and a creation timestamp that needs CBOR additional information 27, a fragment
with arity 11, and a CRC-type-zero block with `dtn:none` and arity 8.

No ION vector was used. No ION source or documentation is present on this
machine and no network fetch beyond the three RFCs was permitted, so this lane
makes no statement about ION.


## Keystone theorems, verbatim, with one hypothesis level down

Corollaries and unfoldings are named `-by-definition` or `-by-construction` in
the books and are not listed here. The hypothesis stack of each keystone is its
`implies` antecedent; where a hypothesis is itself a defined predicate, its
definition is one level down and is given in the book beside it.

### `fn-bpc-decode-of-encode`  (`books/bp-primary-cbor.lisp`)

```lisp
(defthm fn-bpc-decode-of-encode
  (implies (and (fn-bpc-shapep flg x)
                (fn-cbor-octet-listp rest)
                (natp budget)
                (<= (fn-bpc-cost flg x) budget))
           (equal (fn-bpc-dec flg
                              (if (eq flg :list) (len x) 0)
                              (append (fn-bpc-enc flg x) rest)
                              budget)
                  (fn-cbor-ok x rest)))
  :hints (("Goal"
           :induct (fn-bpc-round-trip-induction flg x rest budget)
           :in-theory (e/d (fn-cbor-result-okp fn-cbor-result-value
                            fn-cbor-result-rest fn-cbor-ok fn-cbor-error)
                           (fn-bpc-argument fn-bpc-decode-head
                            fn-cbor-octet-listp take nthcdr floor mod)))))
```

### `fn-bpc-value-round-trip`  (`books/bp-primary-cbor.lisp`)

```lisp
(defthm fn-bpc-value-round-trip
  (implies (and (fn-bpc-valuep x)
                (<= (fn-bpc-cost :item x) *fn-bpc-max-items*)
                (fn-cbor-at-mostp (fn-bpc-enc :item x) *fn-bpc-max-input*))
           (equal (fn-bpc-decode-exact (fn-bpc-encode x))
                  (fn-cbor-ok x nil)))
  :hints (("Goal"
           :use ((:instance fn-bpc-decode-of-encode
                            (flg :item) (x x) (rest nil)
                            (budget *fn-bpc-max-items*)))
           :in-theory (disable fn-bpc-dec fn-bpc-enc))))
```

### `fn-bpc-accepted-input-is-canonical`  (`books/bp-primary-cbor.lisp`)

```lisp
(defthm fn-bpc-accepted-input-is-canonical
  (implies (fn-cbor-result-okp (fn-bpc-decode-exact octets))
           (equal (fn-bpc-encode (fn-cbor-result-value
                                  (fn-bpc-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-bpc-dec-reencodes-consumed-prefix
                            (flg :item) (count 0)
                            (budget *fn-bpc-max-items*)))
           :in-theory (disable fn-bpc-dec fn-bpc-enc
                               fn-bpc-dec-reencodes-consumed-prefix))))
```

### `fn-bpc-dec-yields-shape`  (`books/bp-primary-cbor.lisp`)

```lisp
(defthm fn-bpc-dec-yields-shape
  (implies (and (fn-cbor-octet-listp octets)
                (natp count)
                (fn-cbor-result-okp (fn-bpc-dec flg count octets budget)))
           (fn-bpc-shapep flg (fn-cbor-result-value
                               (fn-bpc-dec flg count octets budget))))
  :hints (("Goal" :induct (fn-bpc-dec flg count octets budget)
           :in-theory (e/d (fn-cbor-ok fn-cbor-error fn-cbor-result-okp
                            fn-cbor-result-value fn-cbor-result-rest)
                           (fn-cbor-octet-listp fn-bpc-decode-head
                            take nthcdr floor mod)))))
```

### `fn-bpc-enc-length-bound`  (`books/bp-primary-cbor.lisp`)

```lisp
(defthm fn-bpc-enc-length-bound
  (implies (fn-bpc-shapep flg x)
           (<= (len (fn-bpc-enc flg x)) (* 1033 (fn-bpc-cost flg x))))
  :hints (("Goal" :induct (fn-bpc-enc flg x)))
  :rule-classes :linear)
```

### `fn-bpp-value-block-of-block-value`  (`books/bp-primary-invariants.lisp`)

```lisp
(defthm fn-bpp-value-block-of-block-value
  (implies (and (fn-bpp-blockp b)
                (fn-cbor-octet-listp crc-octets)
                (equal (len crc-octets)
                       (fn-bpp-crc-width (fn-bpp-crc-type b))))
           (equal (fn-bpp-value-block (fn-bpp-block-value b crc-octets)) b))
  :hints (("Goal" :in-theory (disable fn-bpp-eid-value fn-bpp-value-eid))))
```

### `fn-bpp-decode-of-encode`  (`books/bp-primary-invariants.lisp`)

```lisp
(defthm fn-bpp-decode-of-encode
  (implies (fn-bpp-blockp b)
           (equal (fn-bpp-decode (fn-bpp-encode b)) (fn-bpp-ok b)))
  :hints (("Goal"
           :use ((:instance fn-bpc-value-round-trip
                            (x (fn-bpp-block-value b (fn-bpp-block-crc b))))
                 (:instance fn-bpp-block-value-cost
                            (crc-octets (fn-bpp-block-crc b)))
                 (:instance fn-bpp-value-block-of-block-value
                            (crc-octets (fn-bpp-block-crc b)))
                 (:instance fn-bpp-value-crc-field-of-block-value
                            (crc-octets (fn-bpp-block-crc b))))
           :in-theory (disable fn-bpc-value-round-trip
                               fn-bpp-block-value-cost
                               fn-bpp-value-block-of-block-value
                               fn-bpp-value-crc-field-of-block-value
                               fn-bpp-block-value fn-bpp-block-crc
                               fn-bpp-encode fn-bpc-cost))))
```

### `fn-bpp-accepted-input-is-canonical-by-construction`  (`books/bp-primary-invariants.lisp`)

```lisp
(defthm fn-bpp-accepted-input-is-canonical-by-construction
  (implies (fn-bpp-result-okp (fn-bpp-decode octets))
           (equal (fn-bpp-encode (fn-bpp-result-block (fn-bpp-decode octets)))
                  octets)))
```

### `fn-bpp-accepted-block-has-valid-crc`  (`books/bp-primary-invariants.lisp`)

```lisp
(defthm fn-bpp-accepted-block-has-valid-crc
  (implies (and (fn-bpp-result-okp (fn-bpp-decode octets))
                (not (equal (fn-bpp-crc-type
                             (fn-bpp-result-block (fn-bpp-decode octets)))
                            0)))
           (equal (fn-bpp-value-crc-field
                   (fn-cbor-result-value (fn-bpc-decode-exact octets)))
                  (fn-bpp-block-crc
                   (fn-bpp-result-block (fn-bpp-decode octets))))))
```

### `fn-bpp-encode-is-injective`  (`books/bp-primary-invariants.lisp`)

```lisp
(defthm fn-bpp-encode-is-injective
  (implies (and (fn-bpp-blockp p) (fn-bpp-blockp q)
                (equal (fn-bpp-encode p) (fn-bpp-encode q)))
           (equal p q))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bpp-decode-of-encode (b p))
                 (:instance fn-bpp-decode-of-encode (b q)))
           :in-theory (disable fn-bpp-decode-of-encode fn-bpp-decode
                               fn-bpp-encode))))
```

### `fn-bpf-complete-agreeing-cover-reassembles-to-payload`  (`books/bp-fragment-invariants.lisp`)

```lisp
(defthm fn-bpf-complete-agreeing-cover-reassembles-to-payload
  (implies (and (fn-cbor-octet-listp payload)
                (fn-bpf-inputsp fs (len payload))
                (fn-bpf-all-agreep fs payload)
                (fn-bpf-covers-all fs (len payload)))
           (equal (fn-bpf-reassemble fs (len payload))
                  (list :ok payload)))
  :hints (("Goal"
           :use ((:instance fn-bpf-canvas-is-payload-extent
                            (from 0) (n (len payload)))
                 (:instance fn-bpf-extent-is-nthcdr (xs payload) (from 0)))
           :in-theory (disable fn-bpf-canvas-is-payload-extent
                               fn-bpf-extent-is-nthcdr
                               fn-bpf-canvas fn-bpf-extent))))
```

### `fn-bpf-reassemble-ok-agrees-with-every-fragment`  (`books/bp-fragment-invariants.lisp`)

```lisp
(defthm fn-bpf-reassemble-ok-agrees-with-every-fragment
  (implies (and (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :ok)
                (member-equal f fs)
                (natp k)
                (< k (len (fn-bpf-bytes f))))
           (equal (nth k (fn-bpf-bytes f))
                  (nth (+ (fn-bpf-offset f) k)
                       (fn-bpf-result-bytes (fn-bpf-reassemble fs total)))))
  :hints (("Goal"
           :use ((:instance fn-bpf-cell-at-agrees-with-member
                            (i (+ (fn-bpf-offset f) k)))
                 (:instance fn-bpf-nth-of-canvas
                            (from 0) (n total)
                            (i (+ (fn-bpf-offset f) k)))
                 (:instance fn-bpf-first-index-nil-means-no-marker
                            (cells (fn-bpf-canvas fs 0 total))
                            (from 0) (marker :conflict)
                            (i (+ (fn-bpf-offset f) k))))
           :in-theory (disable fn-bpf-cell-at-agrees-with-member
                               fn-bpf-nth-of-canvas
                               fn-bpf-first-index-nil-means-no-marker
                               fn-bpf-canvas fn-bpf-cell-at))))
```

### `fn-bpf-uncovered-index-blocks-success`  (`books/bp-fragment-invariants.lisp`)

```lisp
(defthm fn-bpf-uncovered-index-blocks-success
  (implies (and (fn-bpf-fragment-listp fs)
                (natp i) (< i total) (natp total)
                (not (fn-bpf-coveredp fs i)))
           (not (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :ok)))
  :hints (("Goal"
           :use ((:instance fn-bpf-nth-of-canvas (from 0) (n total))
                 (:instance fn-bpf-first-index-nil-means-no-marker
                            (cells (fn-bpf-canvas fs 0 total))
                            (from 0) (marker :gap)))
           :in-theory (disable fn-bpf-nth-of-canvas
                               fn-bpf-first-index-nil-means-no-marker
                               fn-bpf-canvas fn-bpf-cell-at))))
```

### `fn-bpf-missing-low-index-is-uncovered`  (`books/bp-fragment-invariants.lisp`)

```lisp
(defthm fn-bpf-missing-low-index-is-uncovered
  (implies (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :missing)
           (not (fn-bpf-coveredp
                 fs (fn-bpf-result-bytes (fn-bpf-reassemble fs total)))))
  :hints (("Goal"
           :use ((:instance fn-bpf-first-index-finds-the-marker
                            (cells (fn-bpf-canvas fs 0 total))
                            (from 0) (marker :gap))
                 (:instance fn-bpf-nth-of-canvas
                            (from 0) (n total)
                            (i (fn-bpf-first-index (fn-bpf-canvas fs 0 total)
                                                   0 :gap))))
           :in-theory (disable fn-bpf-first-index-finds-the-marker
                               fn-bpf-nth-of-canvas
                               fn-bpf-canvas fn-bpf-cell-at))))
```

### `fn-bpf-disagreeing-fragments-yield-conflict`  (`books/bp-fragment-invariants.lisp`)

```lisp
(defthm fn-bpf-disagreeing-fragments-yield-conflict
  (implies (and (fn-bpf-inputsp fs total)
                (member-equal f fs)
                (member-equal g fs)
                (natp i) (< i total)
                (not (equal (fn-bpf-cell-of f i) :gap))
                (not (equal (fn-bpf-cell-of g i) :gap))
                (not (equal (fn-bpf-cell-of f i) (fn-bpf-cell-of g i))))
           (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :conflict))
  :hints (("Goal"
           :use ((:instance fn-bpf-cell-at-agrees-with-member)
                 (:instance fn-bpf-cell-at-agrees-with-member (f g))
                 (:instance fn-bpf-nth-of-canvas (from 0) (n total))
                 (:instance fn-bpf-first-index-nil-means-no-marker
                            (cells (fn-bpf-canvas fs 0 total))
                            (from 0) (marker :conflict)))
           :in-theory (disable fn-bpf-cell-at-agrees-with-member
                               fn-bpf-nth-of-canvas
                               fn-bpf-first-index-nil-means-no-marker
                               fn-bpf-canvas fn-bpf-cell-at))))
```

### `fn-bpf-fragment-block-preserves-adu-key`  (`books/bp-fragment-invariants.lisp`)

```lisp
(defthm fn-bpf-fragment-block-preserves-adu-key
  (implies (and (fn-bpp-blockp b) (natp offset) (natp total))
           (equal (fn-bpp-adu-key (fn-bpf-fragment-block b offset total))
                  (fn-bpp-adu-key b))))
```

### `fn-clock-expired-requires-every-admissible-clock-to-agree`  (`books/clock-invariants.lisp`)

```lisp
(defthm fn-clock-expired-requires-every-admissible-clock-to-agree
  (implies (and (fn-clock-observationp obs)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (null bundle-age)
                (fn-clock-admissible-truep obs now)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age obs)
                       :expired))
           (< lifetime (- now creation-time))))
```

### `fn-clock-expired-and-live-cannot-both-be-sound`  (`books/clock-invariants.lisp`)

```lisp
(defthm fn-clock-expired-and-live-cannot-both-be-sound
  (implies (and (fn-clock-observationp a)
                (fn-clock-observationp b)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (fn-clock-admissible-truep a now)
                (fn-clock-admissible-truep b now)
                (equal (fn-clock-expiry-decision creation-time lifetime nil a)
                       :expired))
           (not (equal (fn-clock-expiry-decision creation-time lifetime nil b)
                       :live))))
```

### `fn-clock-expired-by-age-requires-true-age-over-lifetime`  (`books/clock-invariants.lisp`)

```lisp
(defthm fn-clock-expired-by-age-requires-true-age-over-lifetime
  (implies (and (fn-clock-observationp obs)
                (fn-clock-age-anchorp bundle-age)
                (consp bundle-age)
                (fn-clock-timep lifetime)
                (<= (fn-clock-age-estimate bundle-age obs) true-age)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age obs)
                       :expired))
           (< lifetime true-age)))
```

### `fn-clock-expiry-is-monotone-in-local-time`  (`books/clock-invariants.lisp`)

```lisp
(defthm fn-clock-expiry-is-monotone-in-local-time
  (implies (and (fn-clock-observationp a)
                (fn-clock-observationp b)
                (fn-clock-age-anchorp bundle-age)
                (fn-clock-timep creation-time)
                (fn-clock-timep lifetime)
                (fn-clock-later-observationp a b)
                (equal (fn-clock-expiry-decision creation-time lifetime
                                                 bundle-age a)
                       :expired))
           (equal (fn-clock-expiry-decision creation-time lifetime
                                            bundle-age b)
                  :expired)))
```

## Known defects and deliberate limitations

1. **The box-safety incident above.** Recorded first because it affected other
   lanes.
2. **No host calls any of these functions.** Under the assurance rule that the
   theorem subject must be the function the host calls, every theorem in this
   lane is about a function with no caller. No BPv7 conformance or
   interoperability claim may cite a host line until the adapter proposals
   above are implemented.
3. **`fn-bpf-reassemble` is quadratic by construction.** It is specified
   index-wise so that the result does not depend on fragment order, which costs
   `total x fragments` cell computations: at most 65536 x 64. A production
   reassembler needs an interval structure refined against this specification,
   not this function executed directly. The bound is stated in
   `books/bp-fragment.lisp` and in `specs/bp-primary.md`.
4. **The primary block alone does not determine a fragment's bundle identity.**
   RFC 9171 §4.3.1 puts the payload length in the identity and the payload
   length is in the payload block. `fn-bpp-bundle-id` takes it as an argument
   rather than pretending the primary block has it. The commissioning packet
   said "total ADU length"; the RFC says payload length, and this lane follows
   the RFC.
5. **CRC type zero is representable but its precondition is not checkable
   here.** RFC 9171 §4.3.1 allows it only when a BPSec Block Integrity Block
   targets the primary block, and fn models no BPSec. A zero-CRC primary block
   must be treated as unprotected by a policy above this layer.
6. **`fn-bpp-flags-conformantp` is separate from `fn-bpp-blockp` on purpose.**
   The codec accepts exactly what the wire format allows; the two §4.2.3 MUSTs
   are a policy predicate. A peer that violates a MUST therefore produces a
   decodable block and a policy decision, not a parse failure indistinguishable
   from corruption.
7. **The commissioning packet's RFC section numbers were wrong** for lifetime
   ("§4.2.8") and the fragment fields ("§4.2.9"). RFC 9171 §4.2.8 is
   Block-Type-Specific Data; both fields are specified in §4.3.1. The books and
   specs cite the RFC's own numbering.
8. **Prefix names differ from the packet's.** The packet named
   `fn-bp-fragment` and `fn-bp-reassemble`, but `fn-bp-` is already registered
   in `docs/prefixes.md` for the sender workflow books. Using it again would
   make the registry ambiguous, so the fragment functions are `fn-bpf-*`, in
   keeping with `fn-bpa-`, `fn-bpi-`, `fn-bpo-` and `fn-bpr-`. `fn-clock-` was
   free and is used as the packet named it.
9. **The extension blocks are modeled as block-type-specific data only.** The
   canonical block format of §4.3.2 and the payload block are out of scope, so
   the extension block values cannot yet be placed in a bundle.
10. **No resource-cost bound is proved for CRC computation.** It is linear in
    the encoded block length, which the codec's input preflight bounds, but
    that is an argument in prose here, not a theorem.

## Remaining gaps

- BPSec (RFC 9172) and the default security contexts (RFC 9173) are read and
  referenced, not modeled.
- Custody is absent from BPv7 and must not be imported from RFC 5050 by
  assumption; RFC 9171 Appendix A is the reference.
- Status reports (§6.1) are not generated or parsed; the request flags are
  modeled as flags.
- Block processing control flags (§4.2.4) belong to the canonical block format
  and are not implemented.
- The honesty of the host's `wall-error-bound`, and the Bundle Age block's
  lower-bound property, are hypotheses discharged by callers. They should
  become constrained functions under the C1-15 assumptions packet; naming them
  `A-*` in prose now would be exactly the "prose pretending to be an assumption
  artifact" the assurance rules forbid.
- Monotonic-counter resets across a process restart are not modeled: an age
  anchor established before a restart is meaningless afterwards.
- No liveness result. A node with no wall clock and no Bundle Age block answers
  `:uncertain` forever, by theorem.
- NNTP injection time is untouched; this lane models bundle expiry only.

## Teeth

`std/testing/must-fail` cases, one per hypothesis of each keystone, plus
reachable non-degenerate witnesses, all in the three test books.

| Test book | `assert-event` witnesses | `must-fail` teeth |
| --- | --- | --- |
| `tests/acl2/clock-tests.lisp` | 26 | 9 |
| `tests/acl2/bp-primary-tests.lisp` | 89 | 11 |
| `tests/acl2/bp-fragment-tests.lisp` | 52 | 10 |

Each `must-fail` is `local`, per the caveat in `std/testing/must-fail`'s own
documentation that a non-local `(must-fail (thm ...))` may not be includable.

The teeth that matter most, because they separate this lane's behaviour from
what already exists in the tree:

- **Identical overlap is not a conflict.** `fn-bpf-disagreeing-fragments-yield-conflict`
  loses its conclusion the moment the disagreement hypothesis is dropped. That
  is the difference from `books/transfer.lisp`, whose `:overlap-conflict` branch
  stalls a re-fragmented object without comparing bytes.
- **An `:expired` verdict needs the deciding node's own error bound to be
  honest.** Dropping `fn-clock-admissible-truep` from
  `fn-clock-expired-requires-every-admissible-clock-to-agree` loses the
  conclusion, and dropping `(null bundle-age)` loses it too, because the age
  path is allowed to say `:expired` while the wall clock still admits liveness.
- **Two nodes may disagree, and that is sound.** Dropping either node's
  admissibility from `fn-clock-expired-and-live-cannot-both-be-sound` loses the
  conclusion; the clock-tests book exhibits the disagreeing pair and the fact
  that their admissible intervals are disjoint.
- **A CRC field of the wrong width breaks the field layout.** Dropping the width
  hypothesis from `fn-bpp-value-block-of-block-value` loses the conclusion,
  because the block's arity then disagrees with its CRC type.

## Proposals for the adapter

`tools/bpa_dtn7.py` carries a **BID**: bounded visible ASCII of at most 512
octets, read from the pinned agent's `/status/bundles` inventory and used as the
raw query argument of `/download?` and `/delete?`. Nothing in fn parses it. It
is an index into one agent instance's table, and
[specs/bp-primary.md](specs/bp-primary.md) sets out what it cannot do.

These are proposals, not changes: no host or tool file was touched by this lane.

1. **Leave `bpa_dtn7.py` alone.** It is correctly transport-only, and its
   docstring says so. The BID stays exactly what it is: a delete handle. The
   change belongs one level up, in `tools/run_bp_receive.py`.

2. **Decode the primary block in ACL2, never in Python.** `run_bp_receive.py`
   already has the bounded bundle bytes from `download_bundle`. Send the
   bundle's leading octets across the existing decimal-octet bridge to a new
   `:program`-mode wrapper in `host/bp-receive-host.lisp` that calls
   `fn-bpp-decode` and returns `(:ok block)` or `(:error reason)`. The
   assurance rule "one owner per decision, and it is ACL2" forbids a Python
   twin here: the ADU key, the CRC and the canonical form must not be computed
   on both sides. `tools/bpa_payload_extract.rs` may keep using the pinned
   upstream `bp7` decoder for the payload extent, because that is already a
   declared trusted component and it computes no identity.

3. **Persist bundle identity, not the BID, in the receive context.** Store
   `fn-bpp-adu-key` (source node ID, creation time, sequence number) and, when
   the fragment flag is set, the fragment offset and the payload block's length.
   Those five values are the RFC 9171 §4.3.1 bundle identity; the BID is not.
   They belong in the FNRJ record so the identity survives restart, and the
   `max_transactions` check that review defect D1 found missing must cover the
   new path too.

4. **Key duplicate recognition on bundle identity as well as the work-id.**
   Review defect D10 is that a second sender presenting any request with the
   same work-id is a permanent `:conflict` — work-id squatting as a denial of
   service. Bundle identity is a second key the peer cannot choose freely: the
   sequence counter in §4.2.7 belongs to the source BPA and the source node ID
   is in the primary block. `fn-bpp-identifiablep` says when that key exists at
   all; a `dtn:none` source means it does not, and such a bundle must be handled
   by a policy that does not depend on identity.

5. **Reconcile a lost delete reply by identity.** Review defect D14 is that a
   lost BPA delete reply is unresolvable because retry finds the BID absent from
   inventory and absence is never reconciled as completion. With decoded primary
   blocks in the inventory, absence of a bundle with the recorded ADU key is
   evidence the delete landed, and presence under a different BID is evidence it
   did not.

6. **Carry the clock observation.** Persist creation time, lifetime and a Bundle
   Age anchor with each staged bundle, and call `fn-clock-expiry-decision`
   before forwarding. The host must supply the observation shape in
   [specs/time.md](specs/time.md), including an honest `wall-error-bound`.
   `:uncertain` must not delete anything, and the three outcomes must stay
   distinct at the CLI exit status, which is the same discipline review defect
   D13 asks for on the store paths.

7. **Fragment carriage.** When the fragment flag is set, the receive context
   must carry the offset and the payload length, and the reassembly buffer must
   be keyed by `fn-bpp-adu-key`. `books/bp-fragment.lisp` has no input until
   that exists.

## Commands run and results

Tool versions: ACL2 8.7 built on SBCL, `/opt/homebrew/bin/acl2` ->
`/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2`; system books at
`/opt/homebrew/Cellar/acl2/8.7_6/libexec/books`. macOS arm64.

| Command | Result |
| --- | --- |
| `curl -sSL https://www.rfc-editor.org/rfc/rfc9171.txt -o rfc9171.txt`, likewise 9172 and 9173 | fetched; 2990, 1989 and 2690 lines. The only network action taken by this lane |
| `python3 tools/check_scaffold.py` (`make check`) | `Scaffold OK: 78 Markdown files, 49 requirements, 18 proof targets, 18 scenario specifications.` |
| `make certify` at the lane's base `0bd0b5c`, before any new book | did not complete: the runner's default 600 s per-book timeout was exceeded on `books/article-properties` under ten-lane contention, leaving 106 of 113 roots certified and the seven `article-*` roots unfinished. Not a proof failure; the coordinator's later notice sets `FN_ACL2_TIMEOUT_SECONDS=1800` for this reason |
| `ACL2_CUSTOMIZATION=NONE acl2` with `(certify-book "books/bp-primary-cbor" 0 t)`, thirteen iterations | see below |

**Certification state at the time this handoff was written is recorded in the
status section below.** Nothing in this lane is claimed as certified unless it
is listed there as certified.

### Certification status

| Root | Result | Evidence |
| --- | --- | --- |
| `books/clock` | **certified** | `build/acl2/certify-20260919T073819Z-58496` |
| `books/clock-invariants` | **certified** | `build/acl2/certify-20260919T073819Z-58496` |
| `tests/acl2/clock-tests` | **open** | one `make-event` form fails; the keystones it provides teeth for are certified in `books/clock-invariants`, the teeth are not |
| `books/bp-primary-cbor` | **open** at `fn-bpc-argument-length-bound` | `build/acl2/certify-20260919T072700Z-55617` |
| `books/bp-primary`, `books/bp-primary-invariants`, `tests/acl2/bp-primary-tests` | **not submitted** | blocked behind `books/bp-primary-cbor` |
| `books/bp-fragment`, `books/bp-fragment-invariants`, `tests/acl2/bp-fragment-tests` | **not submitted** | blocked behind `books/bp-primary` |

What moved in `books/bp-primary-cbor` this round, all by removing reasons ACL2
could not see rather than by adding strength:

1. The `:expand` hint on `fn-bpc-decode-of-encode` was written with all four
   arguments free, so `budget` matched its own `(- budget 1)` and the expansion
   never terminated: 1679 seconds of waterfall for 148 prover steps. Pinning the
   fourth argument to the goal's own `budget` variable bounds it to one
   expansion per goal. With that, `fn-bpc-decode-of-encode` and
   `fn-bpc-value-round-trip` certify.
2. The decoder dispatches on the head octet with adjacent integer literals, and
   `95 < head < 96` is consistent over the rationals. Integrality was available
   only as a `:rewrite` rule, which never reaches type-set, so linear arithmetic
   could not refute the wrong branch. `fn-bpc-argument-head-is-natural` was
   added, and `fn-bpc-car-of-octet-list-is-natural` and
   `fn-bpc-decode-head-value-is-natural` were given `:forward-chaining` rule
   classes. With that, `fn-bpc-dec-yields-shape` and
   `fn-bpc-decode-exact-yields-value` certify.
3. `fn-bpc-dec-list-is-true-list` was **false** as written: a refusal is
   `(:error reason)`, whose value field is the reason keyword, so the
   unconditional claim fails at budget zero. It now carries the same
   `fn-cbor-result-okp` hypothesis as its sibling.
4. `fn-bpc-argument-of-decode-head`, `fn-bpc-dec-reencodes-consumed-prefix` and
   `fn-bpc-accepted-input-is-canonical` are commented out and recorded as open,
   with the reason in the book: the first needs the 27-form counterpart of
   `fn-bpc-u64-from-u64-bytes`, a digit-extraction argument over `floor` and
   `mod`.

`books/clock-invariants` failed in 0.05 s on an `in-theory` form naming
`mod-x-y-=-x+y-for-rationals`. That is a translate error, not a proof failure:
the rune does not exist in a book that loads no arithmetic library. The line was
defensive and is gone; the book then certified.

Defect 8 of the lane dump (`must-fail` leaking `ACL2 Error` past the runner's
`FAILURE_MARKERS`) is **resolved and was never real**:
`tests/acl2/bp-workflow-tests` uses `must-fail` and carries a `.cert`.

No claim in `specs/bp-primary.md` or `specs/time.md` states an uncertified
theorem in the present tense any more; both status lines say what ACL2 has
accepted.
