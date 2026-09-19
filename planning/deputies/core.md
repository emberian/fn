# Deputy report: core (acceptance, retention, node, replay, exchange)

HEAD: `dep/core` at 101dcb1 (books, tests, docs, registries; rebased on dev
f9c4cd5). This report is the commit on top. Conventions: `docs/proof-style.md`.

## Per book (one runner invocation, `build/acl2/certify-20260919T192410Z-35697`, ACL2 8.7)

All 17 roots certified: acceptance-alloc 0.13 s, acceptance 0.35, acceptance-invariants 0.40,
retention 0.25, retention-invariants 0.18, exchange 0.21, exchange-invariants 0.32, node 0.24,
node-invariants 2.50, node-traces 0.25, replay 2.36, replay-invariants (shim) 0.26, and the five
test books 0.12 to 0.25. Closure wall 8.3 s. Before, the same runner on a detached `dev`
worktree over the 25 pre-realignment roots: 182.8 s (node-traces 105.9, replay 46.4,
replay-invariants 11.9, node-invariants 11.5). Nothing in the cluster is open.

## Ledger numbers for the cluster (before → after)

- Theorems exported as enabled rules on include: 172 → 164, of which 78 are now record lemmas
  (shape and accessor-of-constructor); non-record exported rules 172 → 86; 61 proof-vocabulary
  lemmas withdrawn under five `deftheory` names; `:rule-classes nil` 0 → 18.
- SUSPECT by shape: 12 → 9 (four dispatcher reduction lemmas deleted; `fn-ag-less-is-less` kept
  `:rule-classes nil` for transfer.lisp is the one new row). `minimal-theory` hints 2 → 0.
- Whole-state recognizer calls on the executable path: 10 → 0 (acceptance 662/695/720, node
  229/283 and the matching test, retention admissibility and release, exchange admissibility,
  replay loop 144/153 and advance). `fn-replay` checks the initial node once.
- Raw-list records opened by any rule: every accessor, constructor and shape is withdrawn
  (`:definition` runes only) in all five books; 44 accessors, 12 constructors, 12 shapes.

## What changed and why

Records opaque with shape lemmas (style §1); recognizers over shape predicates; export theories
(§2); guard equalities `:rule-classes nil` (§3); invariants carried under `mbe` with the original
total `:logic` bodies, so no keystone statement moved (§4); `replay` includes `node-invariants`
because the preservation keystones are its guard proof, and replay-invariants folded into it;
teeth are `assert-event` witnesses (§5); acceptance split at its seam, fourteen test books folded
to five, Makefile and runner defaults and the SCN-015/PRF-014 evidence paths repointed (§6).
Statement changes: `fn-retain-known-obligation-id-is-not-reused` lost its unnecessary
`fn-retain-statep` hypothesis (its teeth had said so). `fn-replay` is restated to test the
initial node once; it is the same function (the loop's first test). Guards changed, not
statements: the transitions, `fn-node-pending-matchesp`, `fn-node-stagep`, `fn-retain-
admissiblep/admit/release`, `fn-exchange-admissible-batchp/ingest`, `fn-node-step/trace`,
`fn-replay-advance-txid/apply-record/loop`. Deleted, none cited: the four `fn-node-step-*-
reduction` and three `fn-node-*-step-preserves-state` lemmas, `fn-replay-natural-successor`,
`fn-ag-{car,cdr,member,append}-is-*`. Open: dropping H1/H2 of `fn-allocate-at-watermark` needs
`fn-watermark-bump-other` restated without the membership-list hypothesis (core, next cycle).

## FTY

Keep raw-list records under the opaque discipline. `centaur/fty/top` plus a `defprod` admits in
0.9 s here, so the objection is not cost: `defprod` puts fixing functions into every keystone
statement, drags `std` rules into every includer, and does not match the host's positional
record encoding. Revisit per cluster behind a local `-fty.lisp` if congruences are needed.

## Proposal: cross-cluster steps (exact edit, owner)

1. store-node (store): `fn-node-prepare/complete/recover` now carry `(fn-node-statep s)`; give the
   store wrappers the same guard and discharge it from `fn-node-*-preserves-state`, never re-check.
2. store-files (store): `(include-book "replay")` instead of `"replay-invariants"`; core then
   deletes the shim.
3. index, nntp, nntp-index (reader): where a proof opened `fn-statep`, add
   `(local (in-theory (enable fn-statep fn-articlep fn-pendingp)))` or cite the keystone.
4. bp-workflow, bp-ingress (bp): guards over `fn-node-statep` need
   `(local (in-theory (enable fn-node-statep)))`; bp-release-invariants additionally
   `(local (in-theory (enable fn-retention-invariants-vocabulary)))`.
5. Host (reader, store): `fn-replay-okp` still runs `fn-node-statep` once per recovery, Θ(n²);
   dispatch on `fn-replay-result-kind` under `fn-replay-loop-result-is-typed` instead.
6. Ledger (tooling): count `(:d name)` withdrawals and `deftheory` vocabularies as export hygiene.
