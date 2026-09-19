# Deputy report: bp (workflow, ingress, receipt, receiver, release, relay, primary, fragment, clock)

HEAD: `dep/bp` (rebased on dev 41af077). Conventions: `docs/proof-style.md`.

## The blocker: bp-receiver-evolving-store-invariants, six minutes to 1800 s

Bisected on a scratch `ld` driver (step limit 2M, accumulated persistence) over the 40-book
closure. Root cause: the w2/bp-guards lane added a NON-LOCAL `(include-book "article-properties")`
to `books/bp-ingress.lisp` to cite one theorem in two guard hints. article-properties has no export
theory; its `fn-article-successful-parse-input-octets` (`(implies (fn-article-result-okp
(fn-article-parse octets)) (fn-cbor-octet-listp octets))`, `books/article-properties.lisp:212`) and
the linear `-input-bound` sibling have a bare-variable conclusion, so every `fn-cbor-octet-listp` and
`len` goal in every book above bp-ingress backchains into the enabled parser: 1.92M frames, 20,384
tries, 0 useful, inside the first 2M steps of one form; with that one rule withdrawn the next form
hits the same wall on `-input-bound`. With every article-properties rule withdrawn the whole book
runs in 7.7 s wall on `ld` (largest form 122k steps). The seven `fn-bpi-ag-*-is-*` equalities were
not the cause (already disabled at 0a16592). Fix: `(local (include-book "article-properties"))`;
the helpers are their readers by `mbe`, the seven equalities are deleted; bp-ingress ends with an
export theory. Certification of the book itself waits on store-files (below).

## Per book (runner invocations in `build/acl2/certify-20260919T19{5040,5322}Z-*`, this laptop)

Certified: bp-workflow 0.4 s, bp-workflow-invariants 23.1 (was 29.0 on persvati dev-0a16592),
bp-workflow-transport-invariants 0.4, bp-workflow-binding-core 25.0 (was 136.1),
bp-workflow-binding-invariants 0.3, bp-workflow-records 0.4, bp-workflow-records-invariants 0.6
(was 7.3), bp-outbound 1.2, bp-release 0.3, clock 0.1, clock-invariants 0.6, and the tests
bp-workflow{,-teeth,-binding-invariants,-records,-records-guards}-tests, bp-outbound{,-guards}-tests,
clock-tests (0.1 to 1.2 s each). PENDING_RELEASE
Open, blocked outside the cluster: bp-ingress and everything above it (bp-receipt, bp-receipt-records,
the nine bp-receiver-* books, relay, relay-invariants, relay-crash-invariants and their tests):
`books/store-files` fails `(verify-guards fn-sf-replay-node)` (`store-files.lisp:620`) against the
core-merged base and no store certificate has been published (ASK on the board, 2026-09-19).
On dev-0a16592 that chain cost 3,100 s of the cluster's 4,346 s (state-invariants 477.6,
relay-invariants 311.3, the evolving-store timeout 1800). Unchanged and cached: bp-adu, bp-primary,
bp-primary-cbor, bp-primary-invariants, bp-fragment, bp-fragment-invariants. PENDING_PRIMARY

## Ledger numbers for the cluster (before → after)

Books ending in an explicit export theory: 3 → 8 (bp-ingress, bp-receipt, bp-receipt-records,
clock, clock-invariants added; bp-primary-cbor, bp-release-invariants, relay-invariants had one).
Named vocabularies: 0 → 3 (`fn-bp-receiver-vocabulary`, `fn-bp-receiver-records-vocabulary`,
`fn-clock-vocabulary`). Opaque records: 0 → 7 kinds (ingress policy and context; receiver config,
context, state, receipt entry; clock observation): 33 accessors, 7 constructors, 7 shapes with
`:d` withdrawn, 40 record lemmas. Enabled `-is-` equalities exported: 7 → 0 (deleted). General
negated `must-fail` teeth: clock 7 → 0 (concrete witnesses; one hypothesis recorded open);
bp-primary-tests PENDING_TEETH. Closure certify wall: see per book; the receiver chain is open.

## What changed and why

Local include and mbe helpers in bp-ingress (the blocker); opaque records and export theories in
bp-ingress, bp-receipt, bp-receipt-records, clock (style sections 1 to 3); includers open what they
need locally (`bp-receiver-{state,store}-invariants`, `relay-invariants`, `relay-crash-invariants`,
`clock-invariants`); core's withdrawn node/retention/replay names are enabled locally where these
books opened them (`bp-workflow`, `bp-ingress`, `bp-workflow-{invariants,binding-core,records-
invariants}`, `bp-release-invariants` plus `fn-retention-invariants-vocabulary`, the two evolving
books); `fn-bprl-node-with-retention-is-shaped` added for core's `fn-node-state-shapep` (the one
proof core's opaque records broke here); clock teeth are witnesses (style section 5), and
`fn-clock-drop-permission-is-exactly-expired-by-definition` is `:rule-classes nil` (section 7).
No keystone statement changed; no accessor or keystone name changed. Not done in budget: opaque
records for bp-workflow (8 kinds), relay state, primary block, fragment; folding the seven
`bp-receiver-*-invariants` and three evolving books; test-book folding.

## Proposal: cross-cluster steps (exact edit, owner)

1. nntp: `books/article-properties.lisp` needs an export theory; `fn-article-successful-parse-*`
   are keystones but their conclusions are over a bare variable under a parser hypothesis, so
   withdraw them (`:rule-classes nil` for the two bound theorems) and let citers `:use`. Also
   `fn-article-{nonempty-true-list-is-consp,field-list-true-listp}` in `article.lisp` (65k and 14k
   useless tries in one bp form): withdraw at export.
2. store: publish store-files, store-node, store-node-traces, store-observed(-traces) certificates;
   bp certifies its receiver chain in one runner invocation as soon as they are in the cache.
3. codecs (on merge): bp-primary, bp-primary-invariants, bp-fragment{,-invariants} and their tests
   open `fn-bpc-*`; add `(local (in-theory (enable fn-bpc-vocabulary)))` to each; receiver proof
   books that open `fn-bpa-*` get `fn-bpa-vocabulary` the same way. `fn-bpc-decode-of-encode`'s
   `(fn-cbor-octet-listp rest)` hypothesis has no violating value (decoder returns the remainder
   unread): delete it or record open.
4. bp, next cycle: opaque records for bp-workflow, relay, bp-primary, bp-fragment; fold the
   receiver invariants books into `bp-receiver-{definitions,properties}` and one
   `bp-receiver-tests`; fold `bp-ingress-guards-tests` into `bp-ingress-tests`.
5. tooling: the certify runner's machine-wide slot cap (4) queues a deputy's root behind siblings
   with no message in the log until a slot is held; print the wait.
