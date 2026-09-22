# The codec seam (T1): records and statement items, and the store cluster — 2026-09-22

Step T1 of [the trajectory plan](../plan-2026-09-22-trajectory.md) §3 and §4.1,
under [how we work](../how-we-work.md). Branch `t1/codec-seam`, worktree
`build/lanes/t1-codec-seam`. Nothing here is a server, proof or
flight-readiness claim beyond the certifications cited by manifest.

## Status at the restart (read first)

The first T1 lane died with its harness. Its work is `f604a84d` (a root WIP
checkpoint, uncertified). The second incarnation merged `dev` at `097c3274`
into it (`04cf3f87`) and took it from there.

**What the seams export, per family.**

*Records* (`books/records-seam.lisp`). An `encapsulate` constrains
`fn-record-encode` and `fn-record-decode-exact` (guards `t`), with the
implementation (`fn-record-encode-impl`, `fn-record-decode-exact-impl`,
`books/records.lisp`) as the local witness. Six constraints:
`fn-record-encode-domain` (a non-record encodes to nil),
`fn-record-round-trip`, `fn-record-accepted-input-is-canonical`,
`fn-record-accepted-input-bounds` (an accepted input is a nonempty octet list
of at most `*fn-record-max-octets*`), `fn-record-accepted-input-magic` (it
begins with the five octets `*fn-record-magic-octets*`, h'44666e2d72'), and
`fn-record-accepted-schema-is-the-stamp-kind` (its sixth octet is
`fn-record-schema-octet` of the record it decodes to; 0 at schema 0). The last
two replace the WIP's single six-octet header constraint, at T2's request
(specs/acceptance-stamp.md §2.1, §6.2); no consumer named the old one. Derived
below the `encapsulate`, from the constraints alone: the result-shape and
kind-dispatch facts (`fn-record-decode-exact-yields-a-record`, the octet-list
and length forward/linear rules, `fn-record-encode-shape`,
`fn-record-encode-length`, `fn-record-encode-is-an-octet-list`), the
encoder-side magic and schema octet, `-refuses-another-magic`, and
injectivity. The record's shape (`fn-defrecord fn-record`, field domains,
the two result shapes, `fn-record-schema-octet`) is `books/records-shape.lisp`,
which is not a codec and stays concrete. `books/records-attach.lisp`
`defattach`es the implementation, discharging each constraint from the six
`fn-record-impl-*` facts of `records-invariants`/`records-canonicality`.

*Statement items* (`books/statement-seam.lisp`). Constrains
`fn-stmt-encode-items`, `fn-stmt-decode-items-bounded` and
`fn-stmt-decode-prefix-items-bounded`, the implementation in
`books/statement-codec.lisp`, the shared item vocabulary in
`books/statement-items.lisp`. Five constraints: the encoder's two equations
(`-of-atom`, `-of-cons`: an item list encodes to its items' CBOR encodings
concatenated), and at the profile budgets the decoder's round trip, its
canonicality, and that what it accepts is an item list. The prefix decoder
is constrained by its guard only; no book proves a fact about it today.
`books/statement-attach.lisp` attaches; `books/codec-attach.lisp` includes
both attach books for every evaluator (image build files, test books).

*CBOR and frame.* Not started. Their codecs are still opened book-wide by
the books `theory_check --table` lists (BP receiver, relay, anchor, identity,
transfer-journal, feed-journal, peer-feed and others), which are the other
three cluster lanes of §4.1.

**Which cluster books include the seam.** `store-events`, `replay`,
`store-files`, `store-files-invariants`, `store-files-traces`, `store-node`,
`store-node-invariants`, `store-node-traces`, `store-node-resolution`,
`store-observed`, `store-prepare-correspondence`, `config-records`,
`node-config`, `checkpoint` (and, outside the cluster, `stx-accept-records`
and `bp-receipt-records`). None of the store cluster opens a codec theory at
the top (`theory_check --books`, below). `checkpoint-codec` is a codec book
of its own family (the checkpoint encoding) and reads the record book's CBOR
item primitives; it is the codec layer, not above it.

**What was failing and why, at the restart.** The WIP's last provisional
wave (`build/triage-2`, persvati, 295 books) had 13 independent reds. Eleven
were `dev`'s own at the WIP's base (`2788d4cb`: checkpoint, checkpoint-codec,
owner-invariants, owner-prepare-correspondence, owner-tls-prefix,
store-node-resolution, store-node-traces, store-observed,
store-prepare-correspondence, bp-receiver-evolving-node-invariants,
byte-store-scan-tests; the freeze-3 merge on `dev` repaired them). Two were
the seam's:

- `books/principal`: the guard of `fn-prin-id` (and, once that was repaired,
  of `fn-prin-sign-succession`). The seam exports the item encoder's cons
  equation enabled, which is how the definition behaved on an explicit list;
  `principal` opens the CBOR codec at the top, so an explicit payload is taken
  apart into CBOR encodings the book then unfolds, and the guard stops
  returning in arithmetic about byte-string heads. The guard needs only
  `fn-stmt-encode-items-is-octet-list`. The WIP tried withdrawing the cons
  equation by default instead; that broke `statement-invariants`'
  `fn-stmt-encode-items-of-id-items-bound` and then `principal-invariants`
  and `policy-invariants`, whose length bounds compute the encoding of an
  explicit list. Decision below.
- `tests/acl2/stx-transit-tests`: a `defconst` whose body calls through the
  seam. ACL2 evaluates a `defconst` without attachments. Remedy below.

**The cons equation, decided on the review's terms.** The item encoder's
two equations are facts about the encoding (what octets a list of items
becomes), so they are constraints, and the consumers use them (the length
bounds of `statement-invariants`, `principal-invariants`,
`policy-invariants`). They stay exported and `-of-cons` stays enabled, which
rewrites only an explicit `cons`, as the definition's expansion did;
`fn-stmt-encode-items-when-consp` (the form that fires on a term merely known
to be a `consp`) is withdrawn and used by name. A guard that needs only the
octet-list fact names that (the two `principal` guards). What the books
above need about a record's shape is in `records-shape` as a shape theorem,
not in the seam.
