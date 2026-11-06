# fn2 lean-meta continuation (the Lean model of the machine; present state at lane/notebooks-lean over dev aeeb60068, rewritten whole 2026-11-05)

Contract: `docs/design/LEAN-METATHEORY.md` (§0's status block is the present state). Project: `meta/` (Lean 4.30.0,
Mathlib `1c2b90b1`, `meta/lakefile.toml`). Emission: `meta/emit/` (printers `print-registry.lsp`, `print-probe.lsp`,
`print-world.lisp`; emitters `emit_lean.py`, `emit_embed.py`; driver `emit.sh`; recorders `record-{arms,cursor,probe}.lsp`).

## On the branch (re-emitted at the tip, built on bb2)
- `Fn2/Instances/LayerA*.lean` regenerated from the world of books/reference + meta/emit/meta-probe certified on bb2:
  12 machines, 262 costs, 521 squares, F5's four tables; 4,560 functions, 0 refused, 0 dropped; 34 kinds (17 child form);
  8,313 equations. `LayerAFacts`' pins follow the registry (12/54/54/521/262/4/213; 126 machine cases; Q1 134).
- `lake build` 635 jobs green; `lake env lean AxiomCensus.lean`: 269 entries, 0 `sorryAx`, standard axioms only.
- Measure: echo+scribe 963/963, cursor 596/596, probe 31/31 (interp, generated, guard, frame). No named difference.
- Proved since 10-31 (in the census): F7 over the interpreter, no hypothesis about the run (lane/lean-bridge):
  `Fn2.Arms.Cost.runArm_charge_le_cost`, `Fn2.Arms.Frame.runArm_frame`, instantiated for FN2-CURSOR in
  `Fn2.Arms.Served`; the earlier `runArm_*` theorems in `Fn2.Arms.Derive` assumed an execution relation and were
  deleted. derivedWrites/Next/Holds stay computed and checked on concrete runs only; fuel has no theorem; H6 per-machine contracts and PW3 wrapper
  preservation (`Fn2.MachineProofs`); M1 natives and fuel (`Faithful`, `Fuel`); M2 packaged revision teeth, HM pasting,
  Mazurkiewicz completeness; M3 PW3 fuel monotonicity, seven `ArmCorrect` instances, PW4 BitVec refinement (`TypedModel`).

## Defects found by this re-emission (fixed on the branch)
- `defcost :faults` unprinted and unrouted in the interpreter: `faultRoute` in `Fn2/Arms.lean` (listed answers,
  `:on-refusal` not ending in a stop, code in faults -> `(:stop :machine-phase)`), `Op.faults`, `CostDecl.faults`.
- `(:refuse WORD)` unread: `expandRefuse` over `RefuseCtx` (word field WORD/REPLY/REASON, `refuse` sub-arm), emitted per
  arm by `emit_embed.py refuse_ctx`; a bare-step `:on-refusal` normalised as `fn2-arms-norm-refusal` does.
- Promotion path faults: `meta/emit/emit.sh` root was three levels up; `tests/sim-layer-a.lisp` loaded
  `../../build/scenario-revision.lsp`; `tests/scenario-revision.py` hashed `fn2/books` and `fn2/sim` (nothing) and needed
  `.git` (now `FN2_SCENARIO_HEAD`; `emit.sh` takes `FN2_EMIT_SRC`) so both run in a box tree.
- New registry keys: machine `:genesis` and `:links` omitted by name; arm-contract `:genesis-arm` carried as data.

## Owed, with the exact next step
1. Genesis arms in the embedding: print `fn2-machine-declared K :genesis` beside the arms, read them, record
   `fn2-exec-genesis` calls.
2. `Fn2.Arms.Derive`: runtime theorems for writes/next/fuel (cost and frame are done, the fault stop included);
   a tooth with a `:faults` op.
3. The two uncovered constructs: `:park :taken K` and a declared wait with a parker need `:child` (the form seat's).
4. Core-form kinds (listener, conn, upload, txn, cns, ctl) are outside the measure until they move to child form.
5. `fn2-ports` prints empty: decide whether the registry's world should include `books/consumer-port`.

## How to rerun (bb2)
`tools/box_certify_bb2.sh notebooks-lean -j 4 books/reference.lisp meta/emit/meta-probe.lisp tests/cursor-unit.lisp
sim/sim-recovery.lisp sim/check.lisp sim/echo.lisp`, then on bb2 in `~/fn2-notebooks-lean` with FN_ACL2, ACL2_SYSTEM_BOOKS,
ACL2_PROJECTS, `ACL2=$PWD/tools/acl2`, `FN2_EMIT_SRC`, `FN2_SCENARIO_HEAD` set: `sh meta/emit/emit.sh`;
`tools/acl2 --timeout 3600 < meta/emit/record-{arms,cursor,probe}.lsp`; in `meta/`: `SWARM_MEM_MAX=48G swarm-build lake
build`, `lake env lean AxiomCensus.lean`, `lake exe fn2-measure ../build/lean-meta/<r>-record.sexp`. A clean build of the
re-emitted world is about 20 minutes on bb2; LayerAEqns3 alone 157 s.
