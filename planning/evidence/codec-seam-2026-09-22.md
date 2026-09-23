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

## The three families of checks (review 2026-09-22-bp-node-machine-2 §4)

1. **Abstract proof books over the seam.** Every book above the record codec
   includes `records-seam` and reasons through its six constraints; the
   statement books through the item seam's five. The guarded downstream
   consumers of the mini-closure: `fn-prin-id` and
   `fn-prin-sign-succession` (`books/principal.lisp`; their guards discharge
   from `fn-stmt-encode-items-is-octet-list`, a fact derived from the item
   seam's two encoder constraints) and `fn-stxa-bindsp`
   (`books/stx-accept-records.lisp`, guard `t`, decodes and re-encodes the
   article record through the record seam).
2. **Concrete codec conformance, exact wire vectors.** In `books/records.lisp`,
   over the implementation: `fn-record-schema0-golden-octets-are-the-encoding`
   (the ten-field golden record encodes to exactly
   `(68 102 110 45 114 0 1 2 3 67 60 97 62 66 9 8 1 65 103 65 111 65 115 65 101 4)`),
   `fn-record-schema0-golden-octets-decode`, and
   `fn-record-schema0-golden-grammar-refusals` (a wrong magic octet is
   `:magic`, a version octet 1 is `:unknown-version`, before any field). A
   round trip and canonicality hold of any length-preserving permutation of
   the encodings, so these stay concrete and are not seam constraints.
3. **Attachment smoke tests.** `tests/acl2/codec-seam-tests.lisp`: every
   record vector (the golden octets and eight refusals, including a Store
   event's `fn-e` magic and the empty input) decoded through the attachment
   equals the implementation's decode; the attached encoder writes the
   golden octets; the statement item list (five items, one a 300-octet byte
   string) encodes and decodes identically through both. **Streaming
   split-input test:** at every split point K = 0..6 of that item list, the
   counted-prefix decoder (`fn-stmt-decode-prefix-items-bounded`, the
   header-then-body read `checkpoint-compaction` does) agrees with the
   implementation, returns the first K items when K is in range and refuses
   when it is not, leaves exactly the encoding of the rest, and that residual
   decodes to the rest; an input cut inside the 300-octet item, and the whole
   stream less its final octet, are refused on both sides. These are
   `assert-event` computations, not theorems: ACL2 does not use an attachment
   in a proof.

Teeth for the two new constraints (`tests/acl2/records-teeth-tests.lisp`):
a witness (an accepted encoding carries the magic and schema octet 0), and
per hypothesis a `must-fail`: the magic conclusion on a Store event's octets
`(68 102 110 45 101 0)`, and the schema-octet conclusion on
`(68 102 110 45 114 1)`, of the seam and of the implementation.

## Certifications

All on persvati, ACL2 8.7, `/home/ember/fn-gates/toolchains/w25/acl2-literal`,
`--jobs 4 --timeout-seconds 1800 --closure --cache /home/ember/fn-certcache`,
remote root `/home/ember/fn-gates/t1-seam` unless named. The farm mirrors the
worktree without `.git`, so a manifest records source digests, not a
revision; the commit each run was submitted at is named here.

| Run | Manifest | Tree | Books | Result |
| --- | --- | --- | --- | --- |
| mini-closure | `certify-20260922T222952Z-613137` | `a46a2269` | 36 (roots `records`, `records-seam`, `records-attach`, `statement-seam`, `statement-attach`, `codec-attach`, `principal`, `stx-accept-records`, `store-events`, `codec-seam-tests`, `records-teeth-tests`, `records-tests`) | passed, 125 s wall |
| store cluster | `certify-20260922T232746Z-1148619` | `252becce` | 139 (roots: the 18 cluster books, `feed-connection-invariants` and 31 test books; with their closure) | passed, 2025 s wall |
| before-measure | `certify-20260922T223400Z-651836` | `dev` `097c3274`, root `/home/ember/fn-gates/t1-before` | 64 (roots `store-node-invariants`, `feed-connection-invariants`) | passed, 984 s wall |
| every root the seams affect | `run-20260923T000240Z-e993` | `c41c48ac` (books as `252becce`) | 231 roots, 310 books | submitted 20:02 persvati time; root harvests |

The first mini-closure submission (`run-20260922T222415Z-e6a6`, manifest
`certify-20260922T222422Z-562368`, not archived) failed at
`fn-prin-sign-succession`'s guard, repaired in `a46a2269`.

## The controls

**Golden vectors.** `tools/codec_golden.py record` over the five codec test
books (`cbor-tests`, `records-tests`, `frame-tests`, `frame-trailer-tests`,
`statement-tests`): 306 ground terms, every one evaluated, on `dev` `097c3274`
(worktree `build/lanes/t1-baseline`) and on this branch at `252becce`.
`codec_golden compare`: 306 identical, 0 different or unevaluated; the two
JSON files are byte-identical (sha256
`b530d0d2e8cb5316376411101dcec3ef18651f3145c12deda35ff18e5aa3d6cd`). Scope:
the terms those five books' `assert-event`s pin, no more.

**Certify wall, persvati, jobs 4, ordinary certification.**

| Book | Before (`dev` `097c3274`) | After (`252becce`) |
| --- | --- | --- |
| `books/store-node-invariants` | 410.5 s | 410.7 s |
| `books/feed-connection-invariants` | 112.4 s | 89.8 s |
| (`books/store-node`) | 403.2 s | 408.6 s |
| (`books/store-node-resolution`) | 1748.0 s (`dev`, manifest `certify-20260922T221439Z-474314`, another lane's run) | 886.5 s |

Load (`uptime` on persvati): the before run ran 22:34 to 22:50 UTC with
load 5.80, 6.26, 4.70 at its start and 6.44, 8.00, 8.33 five minutes after its
end; the after run ran 23:27 to 00:01 UTC with 9.14, 7.40, 7.72 at its start
and 5.73, 7.30, 8.80 at its end. Four other lanes and one of this lane's
provisional waves shared the box through both.

**What the measurement says.** The seam did not move
`store-node-invariants`: four theorems carry 97% of its wall before and after
-- `fn-sn-finish-preserves-indexedp` (154 s before, 145 s after),
`fn-snt-prepare-that-stages-advances-by-one` (130, 132),
`fn-snt-prepared-durable-is-idle-at-successor` (83, 84),
`fn-snt-prepared-abort-is-frontier-advance` (35, 41) -- and
`store-node`'s wall is one event, `(verify-guards fn-sn-finish)` (400 s,
407 s). `store-node-resolution`'s is two theorems,
`fn-snrt-step-success-history-monotone` (466 s) and
`fn-snrt-step-records-prefix` (416 s); its `dev` figure is from a different
run and is not a controlled comparison. `feed-connection-invariants` does
not include the record seam; its 20% is the box, not the seam. The freeze
lanes had already closed the record recognizers and codec in the hints of
these books, so on this tree the seam makes that closure structural (a book
above it cannot open the codec, and `make check` refuses a top-level
opening in the cleared books) rather than faster. The time is in the node
machine's theorems named above, which are T4's (`fn-sn-finish`) and F2
findings, not codec cost.

**`theory_check`, the same tool (this branch's) over both trees.** Store
cluster (the 18 books of §4.1's list): 13 books opened a codec theory at the
top on `dev` `097c3274` (`checkpoint`, `checkpoint-publish`, `node-config`,
`replay`, `store-files`, `store-files-invariants`, `store-files-traces`,
`store-node`, `store-node-invariants`, `store-node-resolution`,
`store-node-traces`, `store-observed`, `store-prepare-correspondence`), 0
here. Whole tree: 59 books above the codec layer open a codec at the top on
`dev`, 46 here (13 theories). `dev`'s own tool, which has no codec layer,
counts 73 of 243 on `dev` and 14 in the cluster (it also counts
`checkpoint-codec`, which is a codec book of its own family).

## Reds that are not the seam's

A provisional wave of `dev` `097c3274` over the same books (persvati,
`build/triage-base-4`, budget 300 s) fails at the same forms the branch's
wave does: `bp-receiver-evolving-node-invariants` at
`fn-bprv-apply-record-installs-record`, `bp-receiver-evolving-store-invariants`
at `fn-bprv-observed-reopen-facts`, `byte-store-keystones` at
`fn-bs-crash-image-reopens`, and `byte-store-scan-tests` at a `defconst`
through the frame digest seam. The branch repairs the last one's two
transaction-name constants and its frame constants (both through seams, both
`make-event`s now); the first three are `dev`'s, and `green_check` on `dev`
records them red since 12:16Z. `books/peer-inbound` (another lane's) takes
613 to 770 s on `dev` and timed out at the waves' 800 s budget on both
trees.

## What the other cluster lanes need, by name

- **BP receiver cluster** (`bp-receiver-*`, `bp-receipt*`, `bp-ingress`,
  `bp-adu`, `relay*`): they open `fn-record-codec-vocabulary` and the CBOR
  vocabularies at the top. From the record seam they need
  `fn-record-round-trip`, `fn-record-accepted-input-is-canonical`,
  `fn-record-decode-exact-yields-a-record`, `fn-record-encode-shape`,
  `fn-record-encode-length`, `fn-record-encode-is-an-octet-list` and, for
  kind dispatch, `fn-record-decode-exact-refuses-another-magic`. The CBOR
  opening needs a CBOR seam, which does not exist: its constraints are
  `fn-cbor-value-round-trip`, `fn-cbor-accepted-input-is-canonical`, the
  input and work bounds, and, as the streaming primitive contract,
  `fn-cbor-decode-reencode-prefix` (consumed prefix and exact residual).
  `books/crypto-seam.lisp` includes `books/records` (the implementation) and
  opens the record codec vocabulary; the CBOR lane should move it to
  `records-shape`, since everything above crypto-seam carries the record
  implementation in its world today.
- **stx/identity/lace cluster** (`principal*`, `policy*`, `lace*`, `stx-*`,
  `hybrid-*`): the item seam's `fn-stmt-encode-items-of-atom`,
  `fn-stmt-encode-items-of-cons`, `fn-stmt-decode-items-bounded-of-encode`,
  `fn-stmt-decode-items-bounded-canonical`,
  `fn-stmt-decode-items-bounded-items`, and the derived
  `fn-stmt-decode-items-of-encode-items`, `fn-stmt-encode-items-of-decode-items`,
  `fn-stmt-decode-items-value-is-item-list`, `fn-stmt-encode-items-is-octet-list`.
  `principal`, `policy`, `lace` still open `fn-stmt-internals` and the CBOR
  codec at the top; a guard over an explicit payload names
  `fn-stmt-encode-items-is-octet-list` (as `principal`'s two do). Nothing
  constrains the prefix decoder beyond its guard; a proof about
  `checkpoint-compaction`'s header-then-body read needs its consumed-prefix
  and residual constraints first.
- **frame/anchor/transfer-journal cluster**: no frame seam exists; the
  frame vocabularies are opened by `anchor-record`, `identity*`,
  `transfer-journal-invariants`, `feed-journal`, `peer-feed`.
- **T2**: `fn-record-accepted-input-magic`,
  `fn-record-accepted-schema-is-the-stamp-kind` (through
  `fn-record-schema-octet` in `records-shape`, which T2 redefines over the
  stamp), and `fn-record-decode-exact-refuses-another-magic`; no consumer
  named the six-octet form.

## What is not verified

- The full run over every root the seams affect (`run-20260923T000240Z-e993`)
  was submitted, not harvested, when this was written. Until its manifest is
  filed, the books outside the store cluster's closure (`principal-invariants`,
  `policy*`, `lace-invariants`, `stx-*`, `bp-receiver-*`, `owner*`,
  `native-*`, `served*`, `nntp-auth*`) are proved only in provisional waves
  (`build/triage-4`), which is not certification.
- No image was built with `codec-attach`, so the attachment configuration is
  exercised only in ACL2 test books.
- The CBOR and frame seams, and the prefix decoder's contract, do not exist.
- `theory_check --strict` runs over the cleared books only
  (`THEORY_STRICT_BOOKS` in the Makefile), not tree-wide; 46 books still
  open a codec at the top.
- The seam's derived `fn-record-encode-magic`,
  `fn-record-encode-schema-octet` and `fn-record-encode-is-injective` have no
  consumer (`:rule-classes nil`); they are kept for T2's statements and can
  go if T2 does not use them.
