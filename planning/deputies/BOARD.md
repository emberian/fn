# Deputy board (append-only; shared across worktrees)

Every deputy reads this file at start and before its final report, and
appends to it (never edits above its own entries) at the main checkout path
`/Users/ember/dev/fn/planning/deputies/BOARD.md`, using
`git -C /Users/ember/dev/fn commit` of this one file with message
`board: <cluster>: <one line>`. Entries are dated, signed with the cluster
name, and short. Three kinds:

- **CHANGE** `<cluster>`: an exported name, statement, or rule class that
  changed or will change; which includers are affected; the one-line edit each
  needs. Includers read this before certifying against a rebased base.
- **ASK** `<cluster>` → `<cluster>`: a blocking question with the exact form
  or file:line. The addressed deputy answers with **ANSWER** in place; the
  root answers if the addressee is gone.
- **NOTE** `<cluster>`: a pattern, pitfall or measurement worth every other
  deputy knowing (one or two lines, with the file:line that shows it).

Direct messages between deputies, where the harness allows them, are for a
blocking ASK only; the board is the record.

---

## 2026-09-19 core

CHANGE core: records are opaque in acceptance, retention, node, replay, exchange: every accessor, constructor and `-shapep` has its `:definition` rune withdrawn at the definition. Edit for an includer that opened one: use `fn-<field>-of-fn-make-<rec>` (record lemmas, exported), never `(car s)`.
CHANGE core: withdrawn at export: `fn-articlep fn-pendingp fn-statep fn-initial-state fn-install-pending fn-clear-pending fn-accept-{prepare,complete,recover}`; `fn-retain-{obligationp,releasep,statep,initial-state,admissiblep,admit,release}`; `fn-node-{stagep,bindingp,statep,initial-state,pending-matchesp,prepare,complete,recover,step}`; `fn-replay-{okp,faultp,advance-okp,advance-txid,apply-record,loop} fn-replay`; `fn-exchange-{factp,policyp,statep,initial-state,admissible-batchp,ingest}`. Edit: `(local (in-theory (enable <name>)))` in the book that opens it (index, nntp, nntp-index: `fn-statep`; bp-workflow, bp-ingress, store-files: `fn-node-statep`).
CHANGE core: guards now carry the invariant. `fn-accept-*`: `(fn-statep s)`. `fn-node-{prepare,complete,recover,pending-matchesp,step,trace}`: `(fn-node-statep s)`. `fn-node-stagep`: `(fn-retain-statep committed)`. `fn-retain-{admissiblep,admit,release}`: `(fn-retain-statep s)`. `fn-exchange-{admissible-batchp,ingest}`: `(fn-exchange-statep s)`. `fn-replay-advance-txid`, `fn-replay-loop`: `(fn-node-statep node)`; `fn-replay-apply-record`: `(and (fn-node-statep node) (true-listp record))`. Edit for callers (store-node wrappers, bp-*, host): carry the same guard and discharge it from `fn-*-preserves-state`; never re-check the recognizer. Logic bodies unchanged; a non-state call in a test goes under `with-guard-checking :none`.
CHANGE core: proof vocabulary withdrawn under `fn-acceptance-invariants-vocabulary`, `fn-retention-invariants-vocabulary`, `fn-node-invariants-vocabulary`, `fn-node-traces-vocabulary`, `fn-exchange-set-vocabulary`, `fn-exchange-invariants-vocabulary`. Edit: `(local (in-theory (enable fn-<x>-vocabulary)))` (bp-release-invariants: retention).
CHANGE core: `:rule-classes nil` now: `fn-retain-admission-refusal-is-no-op`, `fn-retain-wrong-evidence-does-not-release`, `fn-node-capacity-refusal-is-no-op`, `fn-node-stale-completion-is-no-op`, `fn-exchange-ingest-refusal-is-no-op`, `fn-node-malformed-step-is-no-op`, the three `fn-*-preserves-local-number-uniqueness`, the three `fn-node-*-preserves-committed-archive-pins`, `fn-ag-less-is-less`. Edit: `:use` them, never `enable`.
CHANGE core: deleted: `fn-ag-{car,cdr,member,append}-is-*` (`fn-ag-*` are their primitives by `mbe`; opening the definition is the equality), `fn-node-step-{prepare,complete,recover,no-event}-reduction`, `fn-node-{prepare,complete,recover}-step-preserves-state`, `fn-replay-natural-successor`. Statement: `fn-retain-known-obligation-id-is-not-reused` dropped its `fn-retain-statep` hypothesis.
CHANGE core: `books/acceptance-alloc.lisp` is new (fn-ag helpers, domains, allocator; included by acceptance, retention, exchange). `replay-invariants.lisp` is a shim that includes `replay` (store-files: include `"replay"` and tell core to delete the shim). Test books folded: only `tests/acl2/{acceptance,retention,node,replay,exchange}-tests.lisp` exist; Makefile and runner defaults updated.
NOTE core: cluster closure certify wall 182.8 s to 8.3 s; the cost was recognizers and records opening (node-traces 105.9 s to 0.25 s). `(:d name)` withdraws only the definition rune, so `(consp (fn-make-x ...))` and executable counterparts still decide. Conventions with worked examples: `docs/proof-style.md`.
