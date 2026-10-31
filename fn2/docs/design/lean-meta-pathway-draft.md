## 9. The pathway: a Lean-native high-assurance path for the served core (statement-first)

*Opus draft, written when the measure (§6) held for echo and scribe; read once by Astra (§12).*

### 9.1 What it replaces, and what "higher assurance" has to mean
Today's planned path is ATC's: the forms generate ACL2 defuns; ATC, inside ACL2, generates C and an ACL2 proof that the C (under ATC's C semantics, formalised in ACL2) computes the defuns; a C compiler builds it. ATC is already proof-generating, so "higher assurance" cannot mean "proved where ATC is not". It means three things ATC does not give fn2, each a statement below:
1. **reach**: ATC accepts a flat subset (EXECUTION-MODEL §5); every kind records its lowering as an unmet capability (DSL-METATHEORY §1.2, column 9). The served core's kinds are stobj-heavy, multi-child, with nested `mv` and recursion through operations; a lowering the project owns can be built for exactly fn2's closed subset (§4), which is measured, not hoped;
2. **two kernels on one artifact**: the same definitions checked by ACL2 (the instances: squares, refinement, guards) and by Lean (the translation's faithfulness, the generator's per-instance correctness, the typed refinement, the lowering), with the measure (§6) turned from tests into theorems step by step;
3. **the generator in the proof**: today nothing proves that a generated arm function is what its declaration says (ACL2 proves the generated code's shape and frame properties, not its equality with the declaration's meaning); the interpreter of §5 makes that a statement (PW3).

### 9.2 The stages, each with its statement
| stage | object | statement (Lean unless marked) | status | teeth (what makes it fail) |
|---|---|---|---|---|
| PW0 | the ACL2 world (forms, generated defuns, instance proofs) | ACL2: guard verification, the squares, `fn2-turn-refinement` | ACL2's, unchanged; no Lean twin | an uncertified book |
| PW1 | the reader: world → `Val` shallow embedding (`LayerAWorld`) | for each translated `F`: `«F»` satisfies ACL2's defining equation of `F`. Non-recursive: true by construction (the body is the equation). Recursive: **fuel adequacy**, `∀ k args, «F».go (measure args + 1 + k) args = «F».go (measure args + 1) args`, from ACL2's admitted measure | by construction for 747 of 751; fuel adequacy owed for the 4 recursive (`FN2-POOL-CLASS-SCAN`, `FN2-SCRIBE-FILL`, `-PATCH-LOOP`, `-VERIFY`) | the measure's `generated` column: a mistranslated body differs from ACL2's execution on recorded calls |
| PW2 | the natives (`Fn2.ACL2.Native`) | `Faithful` per native: the native satisfies ACL2's definition | **8 proved** (`NTH MV-NTH UPDATE-NTH LEN MEMBER-EQUAL LOGNOT MOD NONNEGATIVE-INTEGER-QUOTIENT`), 4 stated owed (the bitwise through `LOGAND`), 4 trusted as written (`FLOOR EVENP EXPT ACL2-COUNT`, defined through rationals) | `Faithful` fails to prove; the measure differs |
| PW3 | the step language's generator, per arm | `∀ args, guard_FN args → project (runArm k a args) = FN args` (the interpreter of §5 on the declaration equals the generated function, both translated) | **measured**: equal on every recorded call (§6); the per-arm theorem is owed (symbolic evaluation of `runArm` against the translated body; the dispatch must be a `match`, not a hash map, to be unfolded) | a generator mutation (§8.4): interp equals ACL2, generated does not |
| PW4 | a typed model per declaration | generated from the registry: each columns table a structure of `Array (BitVec w)` per column (`w` from `ColKind.width`), each operation a typed Lean function generated from the same declaration; an abstraction `α : Typed → Val`; per operation, `guard_F (α s) → α (F_typed s) = «F» (α s)` | not started | a width mutation (`deadline` u60 → u32) breaks the square for every operation writing it |
| PW5a | executable, first form | the typed model compiled by Lean's compiler; trusted like ACL2's raw Lisp is trusted for the simulator today | not started | — (trusted) |
| PW5b | executable, high-assurance form | a flat-C lowering of the typed model inside Lean, with a C-subset semantics in Lean and the theorem `⟦lower F⟧_C ⊑ F_typed`; the replacement for ATC, built for fn2's subset only | not started; the statement waits on choosing the C semantics (decision 6) | a lowering mutation: the theorem fails to check |

The composed claim, once PW1-PW5b hold: every execution of the lowered C for a served kind refines the ACL2 machine, whose properties ACL2 proved, assuming the ACL2 and Lean kernels, the reader's syntax-directed printing (PW1 shrinks it to "ACL2's printer prints the world"), the C compiler (as ATC also assumes), and the environment assumptions of EXECUTION-MODEL (adapter, persistence, fairness), which no stage discharges.

### 9.3 What stays ACL2's and what is Lean's (the decision rule, §1, applied)
ACL2 keeps every statement about named functions of one world: guards, the instance squares, the refinement theorem, the forms' expansion checks, certification. Lean never re-proves them. Lean takes: the translation's faithfulness (PW1, PW2: about the reader, a bridge statement, §1 row 3), the generator's per-instance correctness (PW3: quantifies over the declaration's presentation, row 2), the typed refinement (PW4) and the lowering (PW5b), which ACL2 could state but fn2 would have to build; Lean's dependent types and Mathlib's `BitVec` carry them. An ACL2 theorem crosses to Lean only as a premise named by the bridge (§7), never as an axiom.

### 9.4 The order, and what each step unlocks
1. PW3 for echo and scribe as theorems (symbolic evaluation), with the dispatch as a `match`; this is the step that turns the measure into a proof and is cheap for the eight-step arms.
2. PW1's fuel adequacy for the four recursive functions (one lemma schema).
3. PW4 for one columns table and the operations of one kind (scribe: pool range writes, its fill and verify loops), generated, with the width mutation as teeth.
4. PW5b's statement once decision 6 names the C semantics; PW5a meanwhile lets the typed model run under the simulator's scenarios as a third execution in the measure.
Each kind that lands in child form joins the measure (§6) by printing; nothing in this order gates a seat.
