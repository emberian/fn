# Deputy report: codecs (cbor, records, frame, identity, store-config, bp-adu, bp-primary-cbor)

HEAD: `dep/codecs`, branched from `dev` a31ed5f. Conventions: `docs/proof-style.md`.
Board entries for includers: `planning/deputies/BOARD.md`, 2026-09-19 codecs.

## What changed and why

**Opaque results (style §1).** The CBOR result (`fn-cbor-ok`/`fn-cbor-error` and its
three accessors), the schema-0 record and both of its results, and the frame's field
parse result and frame result are records now: a shape predicate, constructors,
total `:guard t` accessors under `mbe`, one accessor-of-constructor lemma per field,
injectivity and constructor distinctness, then the `:definition` runes withdrawn.
Accessor and keystone names are unchanged. Two consequences worth naming: the CBOR
accessors no longer carry a `(true-listp x)` guard, so a caller does not prove
list-ness to read a result; and `fn-record-decode-exact` builds its success with a
new `fn-record-result-ok` constructor instead of returning a bare `(list :ok r)`,
which is what let the raw-list lemmas in `records-canonicality` become record lemmas.
`fn-record-schema0-golden-round-trip` is `:rule-classes nil`: it is one ground
vector, not a rewrite rule.

**Export theories (style §2).** Every book in the cluster now ends with an explicit
theory event, and the withdrawal lists the individual rules (a `deftheory` name is
also defined, so an includer re-enables exactly one name, but the `disable` names the
rules so `tools/ledger.py` can see them — it does not look through `deftheory`).
What leaves each book: keystones and record lemmas only. The measured reason is in
3.1b of `planning/lanes/LANEDUMP-twins-into-acl2.md`: the four
`len`-backchaining frame rules plus the two value predicates cost one `append`
associativity goal 108 s and `fn-id-hex-octets-are-octets` 619 s. Those rules are now
`fn-frame-octet-vocabulary`, withdrawn where they are proved, so no includer inherits
the cascade and no book has to disable them by hand.

**Layering (style §6).** `books/frame.lisp` (1083 lines) is split at its seams:
`frame-octets` (constants, the A-CRYPTO trailer, the splitter, big-endian fields),
`frame-fields` (field specs, the parse result, the generic frame encoder/decoder and
the frame result), `frame-journal` (the four magics, the workflow and receipt field
tables, the store/workflow/receipt entry points) and `frame` (FNBI inbound, protected
prefixes and the cluster's export theory). `frame` is still the name every includer
uses; no definition moved position relative to another, and no statement changed.
Three new Makefile roots. `books/bp-primary-cbor.lisp` (1215 lines) is **not** split:
see open items.

**Teeth (style §5).** `tests/acl2/{cbor-teeth,records,frame,identity}-tests.lisp` no
longer include `std/testing/must-fail`. Every general negated `must-fail` is now a
concrete `assert-event` on the negated conclusion, under `with-guard-checking :none`
where the witness is outside a guard: a `:float` value and a 2^32 uint for the CBOR
round trip, a non-minimal head for canonicality, `(0)` as a one-octet trailer and a
two-octet magic for the frame round trip, `32768`/`0` for charge monotonicity and
`(48)` for the odd-length hex projection.

## Per book: certified (worktree, ACL2 8.7, `build/acl2/certify-20260919T19*`)

All 23 roots of the cluster closure certify. Wall time per root, each run alone
after `make certs-install`:

| root | s | root | s |
| --- | --- | --- | --- |
| books/cbor | 0 | books/frame-journal | 34 |
| books/cbor-invariants | 1 | books/frame | 63 |
| books/records | 4 | books/frame-invariants | 14 |
| books/records-invariants | 34 | books/identity | 1 |
| books/records-canonicality | 38 | books/identity-invariants | 4 |
| books/store-config | 0 | books/bp-adu | 19 |
| books/frame-octets | 1 | books/bp-primary-cbor | 51 |
| books/frame-fields | 2 | books/wildmat (unchanged) | 1 |
| tests/acl2/cbor-tests | 0 | tests/acl2/records-tests | 1 |
| tests/acl2/cbor-teeth-tests | 0 | tests/acl2/records-teeth-tests | 1 |
| tests/acl2/frame-tests | 1 | tests/acl2/identity-tests | 0 |

Two numbers worth reading against 3.1b of the lane dump: `frame-invariants` is
14 s (it was 13 s there, after the hand-disables that this cluster now makes
structural), and `identity-invariants` is 4 s, the book whose
`fn-id-hex-octets-are-octets` cost 619 s and 163M prover steps with the frame
shape rules live. No pre-realignment baseline is quoted: the before times are in
`~/fn-gates/dev-0a16592/build/acl2/*/manifest.json` on persvati, which is not
reachable from this host, and `cbor` is included by almost everything, so the
honest comparison is the convergence gate's, not mine.

**The one trap this cluster paid for, for the convergence merge.** A `local`
in-theory disable inside a book stops protecting the books above it the moment
that book is split. The old `frame.lisp` closed `fn-frame-split` and
`fn-frame-u64-bytes` locally, so `frame-invariants` and `identity-invariants`
inherited them *open* and their proofs were tuned that way; making those
disables non-local in `frame-octets` (which the split requires, or parts 2 to 4
prove in a theory the original book never had) closed them for the proof books
too, and `fn-frame-fields-parse-aux-of-octets` and `fn-id-subject-shape` failed.
The fix is one line in each proof book: name `(:d fn-frame-split)` and
`(:d fn-frame-u64-bytes)` in its local enable. Any deputy splitting a book with
`local` theory events should expect exactly this.

## Open, recorded rather than weakened

1. `fn-frame-decode-is-open` keeps its crypto hypothesis and has **no** tooth:
   `fn-frame-digest` is constrained (A-CRYPTO), so no ground term evaluates it and no
   `assert-event` separates the host decoder from the specification decoder. The
   `must-fail` that stood there refuted nothing and looped with the seal rules
   enabled; it is deleted with the reason in the book.
2. `books/bp-primary-cbor.lisp` is realigned (local enables, export theory, keystones
   named) but not split at its three seams (primitives / arrays and text / 64-bit).
   1215 lines, 78 theorems; the split is mechanical and belongs to the next cycle.
3. `fn-bpc-decode-refuses-overlong-input` stays an enabled accessor equality: it is a
   keystone (bounds before allocation) whose statement is an equality between two
   one-argument applications, so the ledger lint flags it. Either the lint learns
   about refusal equalities or the theorem moves to `:rule-classes nil` with its two
   citations changed to `:use`; that is a tooling decision, not a codecs one.
4. ADU results (`bp-adu`) are not yet opaque records; the book has its export theory
   and its keystones, but `fn-bpa-*` still reads its results positionally.

## Proposal: cross-cluster steps (exact edit, owner)

1. **wire, article, wildmat, nntp (nntp)**: books that open the CBOR codec need
   `(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))`
   in one line; books that only read a result need nothing, the record lemmas fire.
   `books/wildmat.lisp` is in my closure and certified unchanged with that base.
2. **bp-primary, bp-receipt, bp-outbound, bp-receiver-\* (bp)**: same one-line enable
   for `fn-cbor-*`; for a book that reads a record or an ADU, use the accessors and
   `fn-record-result-ok` rather than `(list :ok r)` and `(cadr r)`.
3. **store-files, journal, checkpoint (store)**: `fn-record-decode-exact` success is
   `(fn-record-result-ok r)`; a host bridge that pattern-matched `(:ok r)` still
   matches, since the constructor is that list, but a *theorem* about it must use
   `fn-record-result-okp`/`fn-record-result-record`.
4. **statement, crypto-seam (substrate)**: these include `cbor` and open
   `fn-cbor-result-*`; one local enable of `fn-cbor-record-vocabulary` is the edit.
5. **tools (tooling)**: `collect_disabled` in `tools/ledger.py` should look through a
   `deftheory` defined in the same book, so a cluster can withdraw under one name and
   still read clean; today every book here disables by explicit rule name to satisfy
   the lint, which duplicates the vocabulary list.
6. **tools/frame_bridge.py (tooling/host)**: the frame books split; the bridge names
   `books/frame` only, so no change, but the certify root list gained
   `books/frame-octets`, `books/frame-fields`, `books/frame-journal`.
