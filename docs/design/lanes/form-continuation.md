# fn2 machine-form seat continuation (the generator: defmachine, the step language, arms, the assembly; present state at origin/dev a4bea27de, rewritten whole 2026-11-04)

Statement: `docs/design/MACHINE-FORM-20261030.md` (§6.10 = what is built, measured and open). Books:
`books/machine-arms.lisp`, `books/arms.lisp`, `books/machines.lisp`, `books/arm-children.lisp`, `books/assembly-*`.
No form seat is live on 2026-11-04.

## On dev (the form, newest first)
- 736591806 (F4): per-kind leaf books; `assembly-index.lisp` includes the `*-kind.lisp` books (schemas, links,
  registry rows) only; `fn2-machine-run`, the observe router, `arm-charge-ok-p` and `arm-bound` dispatch over
  constrained stubs with default attachments, the verified runs attached in `books/assembly-attach.lisp`.
- 19d57c6d5 (F3): `defcost :child` emits the `:core` `stobj-let` face (skipped for `:effects :per-use` ops); hand
  faces deleted from cns, the cursor's callbacks book and the txn's.
- c782ff824 (F2): holdings threaded sequentially through each arm path (`fn2-arm-effect-rows-seq`,
  `fn2-arm-paths-effect-rows`) and per-path hold checks on every generated kind; fuel exhaustion fails closed;
  sequential `:do` work bounds summed into the arm's cost; `defcost :faults` and `(:refuse WORD)` in
  `:on-refusal`, so a non-fault unrouted answer cannot route to a node stop; `:do` chains over four steps split
  into disabled child helpers.
- Nov 1 (393c3f4ff): `(:park K :F E ...)` named formals; `fn2-shape-one` adopted by C's `fn2-idc-op-shape`.
- Earlier: G1, the placement probe, P1-P4, G2, per-arm tuples, one shape theorem per function, the `:local`
  listener, G3 1/n-3/n (`:repeat` cost, multisets, phase-valued fields, paths, holds per path, typed links, `:sub`,
  `:genesis`, per-output facts as rule classes, the park-taken `:child`, the F9 owner lemma).

## The kinds by form (the tree at a4bea27de)
| form | kinds |
|---|---|
| `defmachine-arms K :children` (child form) | fn2-echo, fn2-scribe, fn2-cursor |
| `defmachine-arms K` (core form) | fn2-listener, fn2-conn, fn2-upload, fn2-txn, fn2-cns, fn2-ctl |
| `defmachine-callback` (old form) | fn2-commit (12), fn2-recovery-machine (13), fn2-sealer (2) |
`:language :unchecked`: 18 sites (16 in `machines-b.lisp`, 1 each in `arms.lisp`, `machines.lisp`).

## Owed, with the exact next step
1. **The `:carrier` mixin**: `(defmachine K :carrier (...))` generating the receive/send/borrow/close/drain phases
   and handlers over a framer; conn and ctl each spell them by hand today. E1, E4 and E5 each need a carrier.
2. **Child form for the core-form kinds**: the txn needs C's successor ops with `:child`; conn, upload, cns, ctl
   need the carrier first. The Lean measure only runs child-form kinds.
3. **The listener's registry arms** by family (admission into E's kind) and the outbound Connect issue
   (`fn2-issue-connect`, named by `(defaction :connect ...)`, undefined).
4. `:child` for `fn2-account-request-park` and `(:park :taken K)`: the two constructs the Lean measure cannot
   reach (LEAN-METATHEORY §6).
5. Assembly per-child books (assembly-access's per-field writer events, the reference books, assembly-init's
   `fn2-core-init-wfp`, the executor's per-kind run rewrite).
6. D26: `assembly-callbacks-d-conn` 336 s and `cursor` 249 s on bb2.
7. The old-form ports: B's two on lane/b-form-port; the sealer is C's.

## Seams
- The Lean seat reads the generator's output, never its source: `meta/emit/print-world.lisp` prints the arm
  bodies table (`fn2-machine-arm-bodies`) and the contracts; `Fn2.Arms.Derive` recomputes cost, writes, next,
  holds and tables from the declaration and `layerA_childForm_contracts_agree` compares them.
- Kind books certify alone; an arm-only edit must not change the executor's closure (F4's control).
