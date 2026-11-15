module
public import Fn2.ACL2.MemberExecEvaluation
public import Fn2.Instances.LayerAEqns1
public import Fn2.Instances.LayerAEqns2
public import Fn2.Instances.LayerAEqns3
import all Fn2.Instances.LayerAWorld.S25_d2to3
import all Fn2.Instances.LayerAWorld.S34_d0to6
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.MemberBodyCorrect
open Fn2.ACL2.Translation Fn2.Instances.LayerAWorld
open MemberExecEvaluation

/-! Connect the exact MEMBER canonical record to the actual generated global
 dispatcher. Syntax/evaluation fuel is 32 here; no 512-fuel equation is reused.
 Current ACL2 packet qualification, guard adequacy and primitive correspondence
 remain separate obligations. -/

theorem emitted_eq_native (x lst : Val) :
    «MEMBER-EQ-EXEC» x lst = Native.memberEqual x lst := by
  obtain ⟨result, run, emitted⟩ := adequate_emitted x lst
  have solved := Countdown.equals_solution measure step decreases
    (fun a => Native.memberEqual a.1 a.2)
    (by
      intro a
      have h := solution_equation a
      cases hs : step a <;> simpa only [hs] using h)
    (measure (x, lst) + 1) (x, lst) (by omega)
  exact emitted.symm.trans (Except.ok.inj ((run _ (by omega)).symm.trans solved))

theorem body_equation (x lst : Val) :
    (if («ENDP» lst).truthy then Val.nil else
      if («EQ» x lst.car).truthy then lst else «MEMBER-EQ-EXEC» x lst.cdr) =
      «MEMBER-EQ-EXEC» x lst := by
  rw [emitted_eq_native x lst, emitted_eq_native x lst.cdr]
  have equation := solution_equation (x, lst)
  cases hc : («ENDP» lst).truthy <;> cases he : («EQ» x lst.car).truthy <;>
    simpa only [step, hc, he, Bool.false_eq_true, ↓reduceIte] using equation.symm

private theorem «ENDP».dispatched {err : String} (lst : Val) :
    (match nativeCall "ENDP" [lst] with
     | some v => Except.ok v
     | none => match fns "ENDP" [lst] with
       | some v => Except.ok v | none => Except.error err) = .ok («ENDP» lst) := by
  simp only [show nativeCall "ENDP" [lst] = none from rfl, «ENDP».fns_eq]
private theorem «EQ».dispatched {err : String} (x y : Val) :
    (match nativeCall "EQ" [x,y] with
     | some v => Except.ok v
     | none => match fns "EQ" [x,y] with
       | some v => Except.ok v | none => Except.error err) = .ok («EQ» x y) := by
  simp only [show nativeCall "EQ" [x,y] = none from rfl, «EQ».fns_eq]
private theorem «MEMBER-EQ-EXEC».dispatched {err : String} (x lst : Val) :
    (match nativeCall "MEMBER-EQ-EXEC" [x,lst] with
     | some v => Except.ok v
     | none => match fns "MEMBER-EQ-EXEC" [x,lst] with
       | some v => Except.ok v | none => Except.error err) = .ok («MEMBER-EQ-EXEC» x lst) := by
  simp only [show nativeCall "MEMBER-EQ-EXEC" [x,lst] = none from rfl, «MEMBER-EQ-EXEC».fns_eq]

/-- The actual generated dispatch evaluates this exact canonical body at 32. -/
theorem eval_export_32 (x lst : Val) :
    evalExport 32 memberDefinition.body fns [("X", x), ("LST", lst)] =
      .ok («MEMBER-EQ-EXEC» x lst) := by
  have evaluated : Translation.eval fns [("X", x), ("LST", lst)] (.app "IF" [(.app "ENDP" [(.var "LST")]), (.quote Val.nil), (.app "IF" [(.app "EQ" [(.var "X"), (.app "CAR" [(.var "LST")])]), (.var "LST"), (.app "MEMBER-EQ-EXEC" [(.var "X"), (.app "CDR" [(.var "LST")])])])]) 32 = .ok ((if ((«ENDP» lst)).truthy then Val.nil else (if ((«EQ» x (Val.car lst))).truthy then lst else («MEMBER-EQ-EXEC» x (Val.cdr lst))))) := by
    refine Translation.eval_if (vc := («ENDP» lst)) (va := Val.nil) (vb := (if ((«EQ» x (Val.car lst))).truthy then lst else («MEMBER-EQ-EXEC» x (Val.cdr lst)))) ?_ ?_ ?_
    ·
      refine Translation.eval_app (vs := [lst]) (by decide) (by decide) ?_ (by exact «ENDP».dispatched (err := "no function ENDP of arity 1") lst)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
    ·
      rfl
    ·
      refine Translation.eval_if (vc := («EQ» x (Val.car lst))) (va := lst) (vb := («MEMBER-EQ-EXEC» x (Val.cdr lst))) ?_ ?_ ?_
      ·
        refine Translation.eval_app (vs := [x, (Val.car lst)]) (by decide) (by decide) ?_ (by exact «EQ».dispatched (err := "no function EQ of arity 2") x (Val.car lst))
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [lst]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
            ·
              rfl
      ·
        rfl
      ·
        refine Translation.eval_app (vs := [x, (Val.cdr lst)]) (by decide) (by decide) ?_ (by exact «MEMBER-EQ-EXEC».dispatched (err := "no function MEMBER-EQ-EXEC of arity 2") x (Val.cdr lst))
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [lst]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
            ·
              rfl
  exact (evalExport_of_decoded_by_definition member_decoded evaluated).trans
    (congrArg Except.ok (body_equation x lst))

def result (values : List Val) (value : Val) : Prop :=
  ∃ key xs, values = [.sym key, Val.ofList xs] ∧
    value = Native.memberEqual (.sym key) (Val.ofList xs)

theorem member_domain_witness {values : List Val}
    (admitted : domain "MEMBER-EQ-EXEC" values) :
    ∃ key xs, values = [.sym key, Val.ofList xs] := by
  cases values with
  | nil => simp [domain] at admitted
  | cons x tail =>
    cases tail with
    | nil => simp [domain] at admitted
    | cons lst tail =>
      cases tail with
      | cons y ys => simp [domain] at admitted
      | nil =>
        cases x with
        | sym key => obtain ⟨xs, rfl⟩ := admitted; exact ⟨key, xs, rfl⟩
        | int _ => simp [domain] at admitted
        | str _ => simp [domain] at admitted
        | chr _ => simp [domain] at admitted
        | cons _ _ => simp [domain] at admitted

/-- No emitted-function premise: the subject is the generated global fns. -/
theorem body_correct :
    CanonicalBodyCorrect program domain primitiveDomain fns "MEMBER-EQ-EXEC" result := by
  intro values admitted
  obtain ⟨key, xs, rfl⟩ := member_domain_witness admitted
  refine ⟨memberDefinition, «MEMBER-EQ-EXEC» (.sym key) (Val.ofList xs), rfl, rfl,
    (closed_adequate_emitted key xs).2.1, «MEMBER-EQ-EXEC».fns_eq _ _, ?_, ?_⟩
  · exact eval_export_32 _ _
  · exact ⟨key, xs, rfl, emitted_eq_native _ _⟩

/-- Embed the checked body into a packet program. In addition to closure
 admission inclusion, that packet cannot admit extra unsupported MEMBER inputs. -/
theorem body_correct_in_program {target : CanonicalProgram}
    {targetDomain targetPrimitiveDomain : CallDomain}
    (definitions : ∀ name definition, program name = some definition → target name = some definition)
    (calls : ∀ name values, domain name values → targetDomain name values)
    (primitives : ∀ name values, primitiveDomain name values → targetPrimitiveDomain name values)
    (memberInputs : ∀ values, targetDomain "MEMBER-EQ-EXEC" values → domain "MEMBER-EQ-EXEC" values) :
    CanonicalBodyCorrect target targetDomain targetPrimitiveDomain fns "MEMBER-EQ-EXEC" result := by
  intro values admitted
  obtain ⟨definition, value, resolved, arity, closed, dispatched, interpreted, post⟩ :=
    body_correct values (memberInputs values admitted)
  exact ⟨definition, value, definitions _ _ resolved, arity,
    canonical_export_extend definitions calls primitives closed, dispatched, interpreted, post⟩

#print axioms emitted_eq_native
#print axioms eval_export_32
#print axioms body_correct
#print axioms body_correct_in_program
end Fn2.ACL2.MemberBodyCorrect
end
