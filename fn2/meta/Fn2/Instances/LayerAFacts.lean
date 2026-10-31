import Fn2.Instances.LayerA
import Fn2.Square

/-!
# Fn2.Instances.LayerAFacts: what the emitted registry satisfies

Hand-written statements about the generated `Fn2.Instances.LayerA` (never edited by hand). These
are pinned structural regression controls over the emitted registry, checked by evaluation (ATLAS §6
law 9: witnesses, not theorems about the subject). `q1_licensed` specialises `Sq.paste_cover` to the
catalogue; it stays conditional on the correspondence's transitions, relation, interpretation and
per-case square proofs, and supplies no proof that the ACL2 obligations are discharged.

The catalogue is now the world's own: every machine row records its `:cases` (one `:run` per
state, one `:observe` per observed event), and `registry_wf` checks them equal to the row's phases
and events. A mutation is detected here only when it changes a property asserted below; a changed
capacity, initialiser or square statement changes the emitted terms but no pinned count
(LEAN-METATHEORY §8).
-/

namespace Fn2.Instances.LayerA

open Fn2.Decl Fn2.Square

/-- The directory's three row fields (P1), which no kind's own table holds. -/
def directory : List Sym := [.s_ready_prev, .s_ready_next, .s_wait_reason]

/-- The emitted rows satisfy the recorded-row and cross-row consistency conditions of `Registry.WF`. -/
theorem registry_wf : registry.WF .k_run .k_observe directory := by decide +kernel

/-- Qualified identities are unique, bare names are not: `defmachine fn2-echo` also emits
`defcolumns fn2-echo` (DSL-METATHEORY §1.1, Astra's correction A1). -/
theorem ids_qualified : registry.ids.Nodup ∧ ¬ (registry.ids.map DeclId.name).Nodup := by
  decide +kernel

theorem declaration_counts :
    registry.machines.length = 9 ∧ registry.columns.length = 51 ∧
    registry.coreChildren.length = 51 ∧ registry.squares.length = 425 ∧
    registry.costs.length = 151 ∧ registry.waits.length = 3 ∧
    registry.rows.length = 187 := by
  decide +kernel

/-- The labels the registry does not hold today: the executor's seven (DSL-METATHEORY §3.2, §3.5),
hand-declared and flagged as such until the executor registers its case source. The router's
fallback is now the world's: the operation set `fn2-machine-router` records `:cases ((:router
:fallback))`, and it is counted here from that row. -/
def nonRegistryCases : List (CaseLabel Sym) :=
  [.executor .clock, .executor .signal,
   .executor (.service 0), .executor (.service 1), .executor (.service 2), .executor (.service 3),
   .executor .emptyPrincipal]

/-- Q1's case catalogue: the machine-owned labels from the registry, the router's fallback from its
operation-set row, then the executor's seven. -/
def q1Cases : List (CaseLabel Sym) := registry.machineCases ++ [.routerFallback] ++ nonRegistryCases

theorem q1_case_counts :
    registry.machineCases.length = 93 ∧ q1Cases.length = 101 ∧ q1Cases.Nodup := by
  decide +kernel

/-- What `defsquare fn2-q1 :template :q1-loop-iteration` binds: one G1 row per case. -/
def q1Squares : List (SquareDecl Sym) := bindG1 "fn2-q1" q1Cases

theorem q1_square_count : q1Squares.length = 101 := by decide +kernel

/-- **The licence.** The ACL2 side owes one G1 square per case of the catalogue; this is the
implication the Lean side supplies: those squares are squares for every word over the catalogue,
for whatever transitions `stepA`, `stepB` and label interpretation `h` the correspondence's contract
names. -/
theorem q1_licensed {A B M : Type} {stepA : CaseLabel Sym → Loose A A} {stepB : M → Loose B B}
    (h : CaseLabel Sym → List M) (R : Tight A B)
    (cases : ∀ c ∈ q1Cases, Sq R (stepA c) (run stepB (h c)) R) :
    ∀ w, (∀ c ∈ w, c ∈ q1Cases) → Sq R (run stepA w) (run stepB (expand h w)) R :=
  Sq.paste_cover h R q1Cases cases

end Fn2.Instances.LayerA
