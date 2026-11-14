module
public import Fn2.ACL2.CanonicalEvaluation
public import Fn2.ACL2.Countdown
public import Fn2.Instances.LayerAWorld.S25_d2to3
import all Fn2.Instances.LayerAWorld.S25_d2to3
public import Fn2.Instances.LayerAWorld.S34_d0to6
import all Fn2.Instances.LayerAWorld.S34_d0to6
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.MemberExecEvaluation
open Fn2.ACL2.Translation
open Fn2.Instances.LayerAWorld
set_option maxRecDepth 10000

/-! The actual MEMBER-EQ-EXEC body reached by CNS. This pilot closes its
recursive body evaluation; it does not certify a fresh served export, symbol
package correspondence, or the primitive object model. -/
def sym (package name : String) : Object :=
  .symbol (package.toList.map Char.toNat) (name.toList.map Char.toNat)
def objects : List Object → Object
  | [] => sym "COMMON-LISP" "NIL"
  | x :: xs => .cons x (objects xs)
def objVar (name : String) := sym "ACL2" name
def call (package name : String) (args : List Object) : Object :=
  .cons (sym package name) (objects args)
def quote (x : Object) := call "COMMON-LISP" "QUOTE" [x]

def notDefinition : CanonicalDefinition := ⟨["P"],
  call "COMMON-LISP" "IF" [objVar "P",
    quote (sym "COMMON-LISP" "NIL"), quote (sym "COMMON-LISP" "T")], 32⟩
def atomDefinition : CanonicalDefinition := ⟨["X"],
  call "COMMON-LISP" "NOT" [call "COMMON-LISP" "CONSP" [objVar "X"]], 32⟩
def endpDefinition : CanonicalDefinition := ⟨["X"],
  call "COMMON-LISP" "ATOM" [objVar "X"], 32⟩
def eqDefinition : CanonicalDefinition := ⟨["X", "Y"],
  call "COMMON-LISP" "EQUAL" [objVar "X", objVar "Y"], 32⟩
def memberDefinition : CanonicalDefinition := ⟨["X", "LST"],
  call "COMMON-LISP" "IF" [call "COMMON-LISP" "ENDP" [objVar "LST"],
    quote (sym "COMMON-LISP" "NIL"),
    call "COMMON-LISP" "IF" [call "COMMON-LISP" "EQ" [objVar "X",
      call "COMMON-LISP" "CAR" [objVar "LST"]], objVar "LST",
      call "ACL2" "MEMBER-EQ-EXEC" [objVar "X",
        call "COMMON-LISP" "CDR" [objVar "LST"]]]], 32⟩
def notTerm : Term := .app "IF" [.var "P", .quote Val.nil, .quote Val.t]
def atomTerm : Term := .app "NOT" [.app "CONSP" [.var "X"]]
def endpTerm : Term := .app "ATOM" [.var "X"]
def eqTerm : Term := .app "EQUAL" [.var "X", .var "Y"]
def memberTerm : Term := .app "IF" [.app "ENDP" [.var "LST"], .quote Val.nil,
  .app "IF" [.app "EQ" [.var "X", .app "CAR" [.var "LST"]], .var "LST",
    .app "MEMBER-EQ-EXEC" [.var "X", .app "CDR" [.var "LST"]]]]
theorem not_decoded : readTerm 32 notDefinition.body = some notTerm := rfl
theorem atom_decoded : readTerm 32 atomDefinition.body = some atomTerm := rfl
theorem endp_decoded : readTerm 32 endpDefinition.body = some endpTerm := rfl
theorem eq_decoded : readTerm 32 eqDefinition.body = some eqTerm := rfl
theorem member_decoded : readTerm 32 memberDefinition.body = some memberTerm := rfl

def program : CanonicalProgram
  | "NOT" => some notDefinition
  | "ATOM" => some atomDefinition
  | "ENDP" => some endpDefinition
  | "EQ" => some eqDefinition
  | "MEMBER-EQ-EXEC" => some memberDefinition
  | _ => none

def domain : CallDomain
  | "NOT", [_] => True
  | "ATOM", [_] => True
  | "ENDP", [v] => ∃ xs, v = Val.ofList xs
  | "EQ", [.sym _, _] => True
  | "MEMBER-EQ-EXEC", [.sym _, v] => ∃ xs, v = Val.ofList xs
  | _, _ => False

def primitiveDomain : CallDomain
  | "CONSP", [_] => True
  | "EQUAL", [.sym _, _] => True
  | "CAR", [.cons _ _] => True
  | "CDR", [.cons _ _] => True
  | _, _ => False

theorem not_evaluates (v : Val) :
    CanonicalExportEval program domain primitiveDomain "NOT" [v]
      (if v.truthy then Val.nil else Val.t) := by
  refine ⟨notDefinition, notTerm, rfl, trivial, rfl, not_decoded, ?_⟩
  cases h : v.truthy
  · exact .if_false (.var rfl) h .quote
  · exact .if_true (.var rfl) h .quote

theorem atom_evaluates (v : Val) :
    CanonicalExportEval program domain primitiveDomain "ATOM" [v]
      (if v.isCons then Val.nil else Val.t) := by
  refine ⟨atomDefinition, atomTerm, rfl, trivial, rfl, atom_decoded, ?_⟩
  have hc : CanonicalEval program domain primitiveDomain [("X", v)]
      (.app "CONSP" [.var "X"]) (Prim.consp v) :=
    .primitive (by decide) (by decide) (.cons (.var rfl) .nil) trivial rfl
  have hn := canonical_call_of_export (actuals := [.app "CONSP" [.var "X"]])
    (by decide : "NOT" ≠ "IF") (by decide : "NOT" ≠ "RETURN-LAST")
    (.cons hc .nil) (nativeCall_none _ _ (by decide +kernel)) (not_evaluates (Prim.consp v))
  cases h : v.isCons <;>
    simpa [Prim.consp, h, Val.ofBool, Val.truthy, Val.nil, Val.t] using hn

theorem endp_evaluates (xs : List Val) :
    CanonicalExportEval program domain primitiveDomain "ENDP" [Val.ofList xs]
      (if (Val.ofList xs).isCons then Val.nil else Val.t) := by
  refine ⟨endpDefinition, endpTerm, rfl, ⟨xs, rfl⟩, rfl, endp_decoded, ?_⟩
  exact canonical_call_of_export (by decide) (by decide) (.cons (.var rfl) .nil)
    (nativeCall_none _ _ (by decide +kernel)) (atom_evaluates _)

theorem eq_evaluates (key : String) (v : Val) :
    CanonicalExportEval program domain primitiveDomain "EQ" [.sym key, v]
      (Prim.equal (.sym key) v) := by
  refine ⟨eqDefinition, eqTerm, rfl, trivial, rfl, eq_decoded, ?_⟩
  exact .primitive (by decide) (by decide)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) trivial rfl

/-- Every recursive call has an admitted domain and a finite body derivation.
Only the selected equality branch is evaluated. -/
theorem closed_evaluation (key : String) (xs : List Val) :
    CanonicalExportEval program domain primitiveDomain "MEMBER-EQ-EXEC"
      [.sym key, Val.ofList xs] (Native.memberEqual (.sym key) (Val.ofList xs)) := by
  induction xs with
  | nil =>
    refine ⟨memberDefinition, memberTerm, rfl, ⟨[], rfl⟩, rfl, member_decoded, ?_⟩
    apply CanonicalEval.if_true
      (canonical_call_of_export (by decide) (by decide) (.cons (.var rfl) .nil)
        (nativeCall_none _ _ (by decide +kernel)) (endp_evaluates []))
    · rfl
    · exact .quote
  | cons head tail ih =>
    refine ⟨memberDefinition, memberTerm, rfl, ⟨head :: tail, rfl⟩, rfl, member_decoded, ?_⟩
    apply CanonicalEval.if_false
      (canonical_call_of_export (by decide) (by decide) (.cons (.var rfl) .nil)
        (nativeCall_none _ _ (by decide +kernel)) (endp_evaluates (head :: tail)))
    · rfl
    · have carEval : CanonicalEval program domain primitiveDomain
          [("X", .sym key), ("LST", Val.ofList (head :: tail))]
          (.app "CAR" [.var "LST"]) head :=
        .primitive (by decide) (by decide) (.cons (.var rfl) .nil) trivial rfl
      have eqEval := canonical_call_of_export (actuals := [.var "X", .app "CAR" [.var "LST"]]) (env := [("X", .sym key), ("LST", Val.ofList (head :: tail))])
        (by decide : "EQ" ≠ "IF") (by decide : "EQ" ≠ "RETURN-LAST")
        (.cons (.var rfl) (.cons carEval .nil))
        (nativeCall_none _ _ (by decide +kernel)) (eq_evaluates key head)
      cases h : (.sym key == head)
      · simp only [Val.ofList, Native.memberEqual, h, Bool.false_eq_true, ↓reduceIte]
        apply CanonicalEval.if_false eqEval
        · simp [Prim.equal, h, Val.ofBool, Val.truthy, Val.nil]
        · exact canonical_call_of_export (by decide) (by decide)
            (.cons (.var rfl) (.cons (.primitive (by decide) (by decide)
              (.cons (.var rfl) .nil) trivial rfl) .nil))
            (nativeCall_none _ _ (by decide +kernel)) ih
      · simp only [Val.ofList, Native.memberEqual, h, ↓reduceIte]
        apply CanonicalEval.if_true eqEval
        · simp [Prim.equal, h, Val.ofBool, Val.truthy, Val.t]
        · exact .var rfl

abbrev State := Val × Val
/-- One step is the emitted recursive body with recursion exposed as a transition. -/
def step : State → Sum Val State
  | (x, lst) => if («ENDP» lst).truthy then .inl Val.nil
    else if («EQ» x lst.car).truthy then .inl lst else .inr (x, lst.cdr)
def measure (state : State) : Nat := state.2.acl2Count

theorem decreases (a b : State) (h : step a = .inr b) : measure b < measure a := by
  rcases a with ⟨x, lst⟩
  cases lst with
  | cons head tail =>
    cases heq : (x == head) <;>
      simp [step, «ENDP», «ATOM», «NOT», «EQ», Prim.consp, Prim.equal,
        Val.isCons, Val.car, Val.cdr, Val.ofBool, Val.truthy, Val.nil, Val.t, heq] at h
    cases h
    simp [measure, Val.acl2Count]
    omega
  | _ => simp [step, «ENDP», «ATOM», «NOT», Prim.consp, Val.isCons,
      Val.ofBool, Val.truthy, Val.nil, Val.t] at h

theorem domain_preserved (key : String) (xs : List Val) (next : State)
    (h : step (.sym key, Val.ofList xs) = .inr next) :
    domain "MEMBER-EQ-EXEC" [next.1, next.2] := by
  cases xs with
  | nil => simp [step, Val.ofList, «ENDP», «ATOM», «NOT», Prim.consp, Val.isCons,
      Val.ofBool, Val.truthy, Val.nil, Val.t] at h
  | cons head tail =>
    cases heq : (Val.sym key == head) <;>
      simp [step, Val.ofList, «ENDP», «ATOM», «NOT», «EQ», Prim.consp, Prim.equal,
        Val.isCons, Val.car, Val.cdr, Val.ofBool, Val.truthy, Val.nil, Val.t, heq] at h
    cases h
    exact ⟨tail, rfl⟩

/-- Independent structural membership solves the exposed transition equation. -/
theorem solution_equation (a : State) :
    Native.memberEqual a.1 a.2 = match step a with
      | .inl result => result
      | .inr next => Native.memberEqual next.1 next.2 := by
  rcases a with ⟨x, lst⟩
  cases lst with
  | cons head tail =>
    cases heq : (x == head) <;>
      simp [step, «ENDP», «ATOM», «NOT», «EQ», Prim.consp, Prim.equal,
        Val.isCons, Val.car, Val.cdr, Val.ofBool, Val.truthy, Val.nil, Val.t,
        Native.memberEqual, heq]
  | _ => simp [step, «ENDP», «ATOM», «NOT», Prim.consp, Val.isCons,
      Val.ofBool, Val.truthy, Val.nil, Val.t, Native.memberEqual]

theorem emitted_go (fuel : Nat) (x lst : Val) :
    «MEMBER-EQ-EXEC».go fuel x lst = Countdown.value Val.nil step fuel (x, lst) := by
  induction fuel generalizing lst with
  | zero => rfl
  | succ fuel ih =>
    rw [«MEMBER-EQ-EXEC».go, Countdown.value_succ]
    simp only [step]
    split <;> try rfl
    split <;> simp_all only [ih]

/-- Adequate fuel yields success equal to the actual generated function;
this strengthens exhaustion stability to existence of a result. -/
theorem adequate_emitted (x lst : Val) :
    ∃ result, (∀ fuel, measure (x, lst) < fuel →
      Countdown.run step fuel (x, lst) = .ok result) ∧
      result = «MEMBER-EQ-EXEC» x lst := by
  obtain ⟨result, hr⟩ := Countdown.certificate measure step decreases (x, lst)
  refine ⟨result, hr, ?_⟩
  rw [«MEMBER-EQ-EXEC», emitted_go]
  have hm : (Val.int lst.acl2Count).nfix = measure (x, lst) := by
    simp [Val.nfix, Val.toInt, measure]
  rw [hm]
  simp [Countdown.value, hr (measure (x, lst) + 1) (by omega)]

/-- Closed canonical evaluation and actual emitted recursion return the SAME
value, with success at every fuel above the admitted measure. -/
theorem closed_adequate_emitted (key : String) (xs : List Val) :
    domain "MEMBER-EQ-EXEC" [.sym key, Val.ofList xs] ∧
    CanonicalExportEval program domain primitiveDomain "MEMBER-EQ-EXEC"
      [.sym key, Val.ofList xs] («MEMBER-EQ-EXEC» (.sym key) (Val.ofList xs)) ∧
    (∀ fuel, measure (.sym key, Val.ofList xs) < fuel →
      Countdown.run step fuel (.sym key, Val.ofList xs) =
        .ok («MEMBER-EQ-EXEC» (.sym key) (Val.ofList xs))) := by
  obtain ⟨result, hr, he⟩ := adequate_emitted (.sym key) (Val.ofList xs)
  have hs := Countdown.equals_solution measure step decreases
    (fun a => Native.memberEqual a.1 a.2)
    (by intro a; cases h : step a <;> simpa only [h] using solution_equation a)
    (measure (.sym key, Val.ofList xs) + 1) (.sym key, Val.ofList xs) (by omega)
  have eqResult : result = Native.memberEqual (.sym key) (Val.ofList xs) :=
    Except.ok.inj ((hr _ (by omega)).symm.trans hs)
  refine ⟨⟨xs, rfl⟩, ?_, ?_⟩
  · rw [← he, eqResult]
    exact closed_evaluation key xs
  · simpa only [he] using hr

theorem positive : domain "MEMBER-EQ-EXEC" [.sym ":OK", Val.ofList [.sym ":MORE", .sym ":OK"]] ∧
    CanonicalExportEval program domain primitiveDomain "MEMBER-EQ-EXEC"
      [.sym ":OK", Val.ofList [.sym ":MORE", .sym ":OK"]] (Val.ofList [.sym ":OK"]) ∧
    Countdown.run step 3 (.sym ":OK", Val.ofList [.sym ":MORE", .sym ":OK"]) =
      .ok (Val.ofList [.sym ":OK"]) :=
  by
  refine ⟨⟨_, rfl⟩, closed_evaluation _ _, ?_⟩
  simp [Countdown.run, step, Val.ofList, «ENDP», «ATOM», «NOT», «EQ», Prim.consp, Prim.equal, Val.isCons, Val.car, Val.cdr, Val.ofBool, Val.truthy, Val.nil, Val.t]

theorem too_small_fuel :
    Countdown.run step 1 (.sym ":OK", Val.ofList [.sym ":MORE", .sym ":OK"]) = .error () := by
  simp [Countdown.run, step, Val.ofList, «ENDP», «ATOM», «NOT», «EQ», Prim.consp, Prim.equal, Val.isCons, Val.car, Val.cdr, Val.ofBool, Val.truthy, Val.nil, Val.t]

def unchangedTail : State → Sum Val State := Sum.inr

theorem broken_decrease : ¬ (∀ a b, unchangedTail a = .inr b → measure b < measure a) := by
  intro claimed
  have := claimed (Val.nil, Val.nil) (Val.nil, Val.nil) rfl
  omega

theorem broken_recursion_never_succeeds (fuel : Nat) (a : State) :
    Countdown.run unchangedTail fuel a = .error () := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

#print axioms closed_evaluation
#print axioms decreases
#print axioms domain_preserved
#print axioms adequate_emitted
#print axioms closed_adequate_emitted
#print axioms positive
#print axioms too_small_fuel
#print axioms broken_decrease
#print axioms broken_recursion_never_succeeds
end Fn2.ACL2.MemberExecEvaluation
end
