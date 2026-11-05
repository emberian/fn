# fn2 layer B continuation (crash and log models, formats, the commit batch, recovery; present state at origin/dev a4bea27de, rewritten whole 2026-11-04)

Layer doc: `docs/b-durability.md` (§6, §11a, §11b). Brief: `docs/design/briefs/FN2-LAYER-B-DURABILITY.md`.
In flight on lane/b-form-port (the commit and recovery kinds into `defmachine-arms`); results are that lane's.

## On dev (B, newest first)
- 55c8290de (S12, Nov 1): `*fn2-commit-txn-records-max*` = 25 (`books/commit.lisp:15`); `fn2-commit-txn-body`
  decodes the records of `*fn2-commit-txn-record-kinds*` (`books/format-events.lisp:40`: article acceptance, the
  five identity records, article, overview, addr, group counts, consumer cursor, principal charges, groups,
  outcome, manifest, consumer names) through C's `fn2-run-layout-decode`. The durable POST path is
  `fn2-commit-admit-txn` -> `fn2-commit-txn-open`/`-join` (there is no `fn2-commit-open-entry`).
- c985342f8 (D's, Nov 1): the transaction wires its POST through S12 and C's `fn2-successor-emit`.
- 71a9f55bc `fn2-commit-posture` (S11, `:answers (:serving :draining)`, no `:child`); `fn2-commit-take` with
  `:child fn2-cs-take`. Earlier: B-S2 6d4e7f977 (admission, seal verbatim, `:batchable`, stream-wake hook, S9
  source ref, S10 block read), its keystones ca3aded2b (`commit-proof.lisp`), the envelope fields in the record
  header c0ae11af4, the 27 `assert$?` as named stops 75adea036, B5-1..B5-4a (717bec1c3 .. 747afb64c), the control
  connection rows cd45d4719.
- Replay: `fn2-commit-hook-form 'fn2-member-replay` (`books/commit.lisp:134`) is a hook; C attaches no body yet.

## What serves
POST's 240 is served on both carriers (H's line at 132ac2c62). The record a POST writes is B's member under
S12; whether every recorded kind is written by the txn is the txn's (D); the record decoder accepts all sixteen.

## Old form (the port in flight)
`fn2-commit`: 12 `defmachine-callback`s (`books/commit.lisp`; idle observe collect drain drop durable fence
install notify publish seal writes) and `defmachine-run fn2-commit`. `fn2-recovery-machine`: 13
(`books/recovery-machine.lisp`). `books/machines-b.lisp` holds 16 of the tree's 18 `:language :unchecked` sites.

## Owed, with the exact next step
1. The form port (lane/b-form-port). Done when no `defmachine-callback` is left in commit.lisp and
   recovery-machine.lisp and `commit-txn-unit`, `commit-proof-unit`, `recovery-proof-unit`, `sim-layer-b` pass.
2. `:child` bodies for `fn2-commit-posture`, `fn2-commit-admit-txn`, `fn2-commit-txn-source` (with the port), so
   the txn can move to child form.
3. Replay: `fn2-member-replay` (C attaches it): decode each record by kind, fill the `:event` fields from the
   header, insert through `fn2-succ-bind-slot`. B5-4b replay, B6 checkpoint and cleaner, B7 the decisive scenario.
4. Keystone subjects on `fn2-turn` (Argon §9.2); `fn2-block-read` (`commit.lisp:731`) gets its first caller from
   lane/article-octets; S10's borrow edge and block hash with it.

## Seams
- From C: `fn2-run-layout-decode`, the sixteen record kinds, `fn2-member-replay`.
- To D: `fn2-commit-admit-txn` (`:answers (:ok :exhausted :admission)`, `machines-b.lisp:360`), the posture.
- To D6 3/n: `fn2-block-read` (`:answers (:ok :exhausted :stale :bounds)`) and `fn2-block-read-done`.
- To E: the control connection rows (`fn2-b-ctl-rows`, `fn2-b-ctl-slot`).
