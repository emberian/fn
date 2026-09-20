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

## Open

(none recorded; see specs/checkpoint.md if a keystone is withdrawn)
