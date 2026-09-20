# Deputy report: bp (workflow, ingress, receipt, receiver, release, relay, primary, fragment, clock)

HEAD: `dep/bp` at the commit carrying this file (on top of 6530a80 = dev ca66782 merged: core,
codecs, substrate, nntp, tooling realigned). Conventions: `docs/proof-style.md`.

## The blocker: bp-receiver-evolving-store-invariants, six minutes to 1800 s

Bisected on a scratch `ld` driver (step limit 2M, accumulated persistence) over the 40-book
closure. Root cause: the w2/bp-guards lane added a NON-LOCAL `(include-book "article-properties")`
to `books/bp-ingress.lisp` to cite one theorem in two guard hints. article-properties has no export
theory; `fn-article-successful-parse-input-octets` (`(implies (fn-article-result-okp
(fn-article-parse octets)) (fn-cbor-octet-listp octets))`, `books/article-properties.lisp:212`) and
its linear `-input-bound` sibling conclude over a bare variable, so every `fn-cbor-octet-listp` and
`len` goal above bp-ingress backchains into the enabled parser: 1.92M frames, 20,384 tries, 0
useful, inside the first 2M steps of one form; with that rule alone withdrawn the next form hits
`-input-bound`. With every article-properties rule withdrawn the whole book runs in 7.7 s on `ld`
(largest form 122k steps). The seven `fn-bpi-ag-*-is-*` equalities were not the cause (already
disabled at 0a16592). Fix: `(local (include-book "article-properties"))`; the helpers are their
readers by `mbe` and the equalities are deleted; bp-ingress ends with an export theory.

## Per book (this laptop; before = persvati gate dev-0a16592, `book_wall_seconds`)

Certified on the merged tree, one runner invocation, `build/acl2/certify-20260919T201653Z-67091`:
bp-workflow 0.5, bp-workflow-invariants 28.3 (was 29.0), bp-workflow-transport-invariants 0.5,
bp-workflow-binding-core 30.8 (was 136.1), bp-workflow-binding-invariants 0.3, bp-workflow-records
0.4, bp-workflow-records-invariants 0.6 (was 7.3), bp-outbound 1.4, bp-release 0.5,
bp-release-invariants 366.3 (was 427.4; 310.0 before the codecs merge), bp-primary 6.5,
bp-primary-invariants 676.7 (was 251.1; 208.6 before the codecs merge: the local enable of the
three cbor vocabularies is the cost, narrow it next cycle), bp-fragment 0.9, bp-fragment-invariants
23.9 (was 35.6), clock 0.1, clock-invariants 0.6, and the twelve test books 0.2 to 12.5 s
(bp-primary-tests 0.9, was 505.6; bp-fragment-tests 12.5, was 30.1). Those 27 roots: 1437.9 s on
persvati before, 1159.2 s here after. Of the gate-failed roots on ca66782, bp-primary-invariants,
bp-primary-tests, bp-fragment-invariants, bp-fragment-tests, bp-release-invariants and
bp-release-tests needed only the codecs vocabulary line (plus, for release, the node-shape lemma
below); none failed for a reason of its own.
Open, blocked outside the cluster: bp-ingress and everything above it (bp-receipt,
bp-receipt-records, the nine bp-receiver-* books, relay, relay-invariants, relay-crash-invariants,
their eight test books). `books/store-files` fails `(verify-guards fn-sf-replay-node)`
(`store-files.lisp:620`) on the core-merged tree, and the store deputy's fix (board, 0714151) is not
on dev; no store certificate exists to install and bp does not edit store books. Source evidence
only: a scratch `ld` of the edited chain against the pre-realignment certified store books passed
bp-ingress, bp-receipt and bp-receipt-records without error and was inside
bp-receiver-state-invariants when the session was cut. Before, this chain was 3,100 s of the
cluster's 4,346 s (state-invariants 477.6, relay-invariants 311.3, the timeout 1800).

## Ledger numbers for the cluster (before → after, `planning/ledger.json` at a31ed5f → 8983f24)

Books ending in an explicit export theory 3 → 8; named vocabularies 0 → 3
(`fn-bp-receiver-vocabulary`, `fn-bp-receiver-records-vocabulary`, `fn-clock-vocabulary`); opaque
record kinds 0 → 7 (ingress policy, context; receiver config, context, state, receipt entry; clock
observation: 33 accessors, 7 constructors, 7 shapes withdrawn, 40 record lemmas, 21
forward-chaining shape facts); exported `-is-` equalities 7 → 0; general negated `must-fail` teeth
12 → 0 (clock 7, primary 5); teeth-form lints 3 → 0; SUSPECT 6 → 6; export-hygiene lints 8 → 8.

## What changed and why

Local include and mbe helpers in bp-ingress (the blocker); opaque records and export theories in
bp-ingress, bp-receipt, bp-receipt-records, clock (style 1 to 3); includers open what they need
locally; core's withdrawn node, retention and replay names enabled locally where these books opened
them; codecs' six record/cbor vocabularies enabled locally in the 30 books that open them;
`fn-bprl-node-with-retention-is-shaped` supplies core's `fn-node-state-shapep` (the one proof
opaque node records broke); clock and primary teeth are witnesses (style 5). Statements: two
hypotheses of `fn-bpp-value-block-of-block-value` dropped (no violating value, the reader never
consults the CRC field); `fn-clock-drop-permission-is-exactly-expired-by-definition` is
`:rule-classes nil`. Recorded open in the test books: `(fn-clock-observationp b)` in
`fn-clock-expiry-is-monotone-in-local-time` and `(fn-cbor-octet-listp rest)` in codecs'
`fn-bpc-decode-of-encode`, both without a violating value. No accessor or keystone renamed.

## Proposal: cross-cluster steps (exact edit, owner)

1. Convergence (receiver chain, after store lands): `bp-receiver-evolving-store-invariants` includes
   `"store-observed"`; in the evolving and receiver-*-invariants books that open store definitions
   add `(local (in-theory (enable fn-store-files-invariants-vocabulary
   fn-store-files-traces-vocabulary fn-store-node-invariants-vocabulary
   fn-store-node-traces-vocabulary fn-store-observed-vocabulary fn-sf-statep fn-sn-statep
   fn-snt-relation fn-snt-step)))` dropping what a book does not open; `fn-bpi-ingress-prepare`
   and `fn-bpi-durably-acceptedp` call `fn-sn-prepare`/`fn-sn-node` under `fn-sn-statep`, which
   `fn-bpi-policy-appliesp` already tests first: carry it in the `:exec` branch, never re-check.
2. nntp: export theory for `article-properties` (withdraw `fn-article-successful-parse-*`,
   `:rule-classes nil` for the two bounds) and withdraw
   `fn-article-{nonempty-true-list-is-consp,field-list-true-listp}` (65k and 14k useless tries in
   one bp form).
3. codecs: delete or record open the `(fn-cbor-octet-listp rest)` hypothesis of
   `fn-bpc-decode-of-encode`; a narrower `fn-bpc-<x>-vocabulary` split so bp-primary-invariants
   need not enable all three (676.7 s).
4. bp, next cycle: opaque records for bp-workflow (8 kinds), relay, bp-primary, bp-fragment; fold
   the seven receiver invariants books and three evolving books into
   `bp-receiver-{definitions,properties}` and one test book; the two remaining export-hygiene rows.

## Closed 2026-09-19 (w4/convergence2)

The receiver chain named open above (bp-ingress through bp-receiver-evolving-store-invariants,
relay, relay-invariants, relay-crash-invariants and the eight test books) is certified on dev
b55dcea by the second convergence lane; the edits, one line each, are the CHANGE convergence2
entry on the board. Nothing in this cluster is open.
