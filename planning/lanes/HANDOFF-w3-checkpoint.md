# Handoff: w3/checkpoint

Branch `w3/checkpoint` in `build/lanes/w3-checkpoint`, merged with dev
`c8886ee`. The lane adds two books, two test books, one host bridge, one
host module and its tests on top of the store deputy's realigned
`books/checkpoint.lisp`, which it does not change.

## What the lane owns

| File | What it is |
| --- | --- |
| `books/checkpoint-codec.lisp` | `fn-cpc-`: canonical whole-state checkpoint bytes over the records book's CBOR primitives; the tagged node tree, the header, both canonicality directions, validation bound to capture, and the FNCP frame magic and kind table |
| `books/checkpoint-publish.lisp` | `fn-cpp-`: the generation machine (stage, two data/directory barrier pairs, marker selection), crash images with the `:old`/`:new` and `:absent`/`:present` choices, and recovery with four distinct outcomes |
| `tests/acl2/checkpoint-codec-tests.lisp`, `tests/acl2/checkpoint-publish-tests.lisp` | guard-world audit, malformed-input regressions, scenarios and ground-witness teeth |
| `host/checkpoint-host.lisp` | the ACL2-side bridge: protected prefix, decode, restore, differential |
| `tools/checkpoint.py`, the `recover` hook in `tools/run_store.py`, `tests/campaign/cuts.py` | host adoption and the six named cuts |
| `tests/test_checkpoint.py`, `tests/checkpoint_crash_child.py` | unittest: real store, real ACL2, real syscalls, process death at every cut |

## Keystones (statements unchanged by the realignment)

`books/checkpoint.lisp` (the deputy's, untouched):
`fn-checkpoint-plus-suffix-equals-full-replay` (PRF-008) and the
frontier-rejection keystone `fn-checkpoint-restore-rejects-frontier-reuse`.

`checkpoint-codec`: the two tree directions
(`fn-cpc-decode-tree-of-encoding-exact`, `fn-cpc-decode-tree-accepted`), the
two checkpoint directions (`fn-cpc-decode-of-encode`,
`fn-cpc-accepted-input-is-canonical`), the four
`fn-cpc-decode-rejects-*-before-node`, exact binding
(`fn-cpc-valid-is-capture-value`), and the frame and selection round trips
(`fn-cpc-frame-decode-of-encode`, `fn-cpc-frame-open-of-seal`,
`fn-cpc-frame-accepted-is-canonical`, `fn-cpc-selection-decode-of-encode`).

`checkpoint-publish`: the five numbered keystones named in
`specs/checkpoint.md` §3, plus the eight `-preserves-state` facts.

## Proof-style position (docs/proof-style.md)

- §1 Three opaque records in `checkpoint-publish`: `fn-cpp` (state),
  `fn-cpp-entry` (generation), `fn-cpp-image` (crash image). Shape predicate,
  `mbe` accessors over the total `fn-ag-` helpers, one accessor-of-constructor
  lemma per field, `:definition` runes withdrawn, the three forward-chaining
  shape facts per record and one per recognizer. The codec defines no record
  of its own; it uses `checkpoint`'s.
- §2 Both books end with an export theory.
  `fn-checkpoint-codec-vocabulary` holds the reader-domain, re-encoding,
  of-encoding and append facts; `fn-checkpoint-publish-vocabulary` holds the
  generation-list and lookup facts. `checkpoint-publish` re-enables the codec
  vocabulary locally.
- §5 Sixteen general negated `must-fail` teeth became ground witnesses;
  `std/testing/must-fail` is no longer included by either test book.

## Open (the next step, exactly)

`books/checkpoint-codec.lisp` does not certify against dev `c8886ee`. One
cause throughout: the codecs realignment withdrew the vocabulary these
proofs were written against, and each fix uncovers the next form. Seven
closed, one open. Each row's evidence is the farm run that proved the fix by
moving the failure later in the book.

| # | Form | Cause | Fix | Failure moved to |
| --- | --- | --- | --- | --- |
| 1 | `fn-cpc-decode-argument-of-encoding` | the CBOR u16/u32 byte facts | `(local (in-theory (enable fn-codecs-includer-vocabulary)))` | `certify-20260920T041014Z-2320373` |
| 2 | `fn-cpc-read-bytes-of-encoding` | the local head-bounds lemma's inequalities were rewrite-only, so linear arithmetic never got `(<= 64 head)` and the major-0 branch survived into a false induction | `:linear` corollaries on `fn-cpc-encode-argument-head-bounds`; `fn-record-cbor-decode-{argument,bytes}-success-domain` cited in that one `e/d`; `:do-not-induct t` | `certify-20260920T041617Z-2375759` |
| 3 | `fn-cpc-read-uint-small-reencode` | the value's `natp` was re-derived by a false induction | `:use fn-cpc-read-uint-domain`, `:do-not-induct t` | `certify-20260920T041937Z-2408034` |
| 4 | `(defun fn-cpc-encode-tree)` measure | the `t` clause recursed on `(car x)`; a character has `acl2-count` 0 and is none of the earlier cases | the recursive clause is `((consp x) ...)` with `(t nil)`. Behaviour changes only outside `fn-cpc-treep`, which every keystone hypothesises, so no keystone statement moves | `certify-20260920T042326Z-2445522` |
| 5 | `fn-cpc-decode-tree-rest-octets` | **the book-wide enable from #1 had been widened with the two record vocabularies; they open the parse result to `car`/`cadr`/`caddr`, so `fn-cpc-read-uint-domain` -- stated in `fn-record-parse-rest` vocabulary -- stopped matching** | dropped both from the book-wide enable. `fn-record-canonicality-vocabulary` was added instead: unlike them it holds no `(:d ...)` rune, so it opens nothing | `certify-20260920T043026Z-2513419` |
| 6 | `fn-cpc-decoded-string-is-string` | the canonicality round trip was withdrawn | `:use fn-record-string-octets-of-octets-string`, disabled in the same `e/d` so it is not left to match a goal where `fn-record-octets-string` has already opened to `coerce` | `certify-20260920T043408Z-2550517` |
| 7 | `fn-cpc-symbol-item-is-symbol`, `fn-cpc-enum-index-of-symbol-item` | `i` is symbolic, so `fn-frame-item` cannot unwind over the three-entry table | `:cases ((equal i 1) (equal i 2) (equal i 3))` | `certify-20260920T043800Z-2586175` |
| 8 | **open**: `fn-cpc-decode-tree-of-encoding` (the tree value-direction keystone) | Subgoal *1/1.14': the cons branch must refuse a head that is an octet, so the proof has to decide `fn-cbor-octetp` on a symbolic head with `(< 255 (car x))` | **attempted and insufficient**: a scoped `(local (in-theory (enable fn-cbor-octetp)))` around the form (left in place, so the successor need not retry it). The next thing to try is `fn-cpc-octet-list-tagp` and the decoder's own `fn-cpc-decode-tree` induction scheme in the same scope | `certify-20260920T044112Z-2618104:4535` |

`checkpoint-publish` and both test books have only ever failed on the
cascade from this include; no theorem of theirs has been refuted, and no
keystone has been weakened.

**The lesson the tree should keep**: widening a book-wide enable to get past
a realignment failure buys one form and costs the next -- #5 was caused by
the fix for #1. Cite the cluster's own `-domain` or round-trip lemma by
`:use` in the one form, and reserve a book-wide enable for a bundle that
holds no `(:d ...)` rune.

Resubmit with:

    python3 tools/farm.py submit persvati --jobs 12 \
      --remote-root /home/ember/fn-lanes/w3-checkpoint \
      --affected-by books/checkpoint-codec.lisp \
      --affected-by books/checkpoint-publish.lisp --closure

Do not certify these locally: on 2026-09-20 a local run sat 1560 s waiting
for one of the four ACL2 slots and never started. The rest of the closure
(43 books) certifies on the farm in about three minutes, so a fix-and-read
cycle costs about four.

`tests/test_checkpoint.py` (unittest, real store, real ACL2, process death
at each of the six named cuts) has **not been run** this cycle: it loads
`host/checkpoint-host.lisp`, which includes `checkpoint-codec`, so it cannot
run before the book certifies.
