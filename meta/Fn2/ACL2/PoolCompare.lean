-- Generated from the canonical admitted loop; proof schema lives in pool_compare.lean.in.
module

public import Fn2.ACL2.Countdown
public import Fn2.ACL2.Translation
public import Mathlib.Tactic
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.List.Control
-- BEGIN world bodies (emit_embed.py): scan
import all Fn2.Instances.LayerAWorld.S34_d0to6
import all Fn2.Instances.LayerAWorld.S17_d1
import all Fn2.Instances.LayerAWorld.S22_d1to7
import all Fn2.Instances.LayerAWorld.S12_d0to10
import all Fn2.Instances.LayerAWorld.S8_d2to12
-- END world bodies

@[expose] public section

namespace Fn2.ACL2.PoolCompare
open Fn2.ACL2 Fn2.Instances.LayerAWorld
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

abbrev State := Val × Val × Val × Val × Val

def step : State → Sum Val State
  | («A», «B», «I», «N», «FN2-POOL») => (if ((if ((«NOT» («NATP» «I»))).truthy then («NOT» («NATP» «I»)) else (if ((«NOT» («NATP» «N»))).truthy then («NOT» («NATP» «N»)) else («NOT» (Prim.lt «I» «N»))))).truthy then (.inl (Val.cons (Val.sym ":EQUAL") (Val.cons («NFIX» «N») Val.nil))) else ((fun («X» : Val) («Y» : Val) («FN2-POOL» : Val) («N» : Val) («B» : Val) («A» : Val) («I» : Val) => (if ((Prim.lt «X» «Y»)).truthy then (.inl (Val.cons (Val.sym ":LESS") (Val.cons «I» Val.nil))) else (if ((Prim.lt «Y» «X»)).truthy then (.inl (Val.cons (Val.sym ":GREATER") (Val.cons «I» Val.nil))) else (.inr («A», «B», (Prim.plus (Val.int 1) «I»), «N», «FN2-POOL»))))) («FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL») («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL») «FN2-POOL» «N» «B» «A» «I»))

def measure : State → Nat
  | (_, _, i, n, _) => n.nfix - i.nfix

def bodyValue («A» «B» «I» «N» «FN2-POOL» : Val) : Val := (if ((if ((«NOT» («NATP» «I»))).truthy then («NOT» («NATP» «I»)) else (if ((«NOT» («NATP» «N»))).truthy then («NOT» («NATP» «N»)) else («NOT» (Prim.lt «I» «N»))))).truthy then (Val.cons (Val.sym ":EQUAL") (Val.cons («NFIX» «N») Val.nil)) else ((fun («X» : Val) («Y» : Val) («FN2-POOL» : Val) («N» : Val) («B» : Val) («A» : Val) («I» : Val) => (if ((Prim.lt «X» «Y»)).truthy then (Val.cons (Val.sym ":LESS") (Val.cons «I» Val.nil)) else (if ((Prim.lt «Y» «X»)).truthy then (Val.cons (Val.sym ":GREATER") (Val.cons «I» Val.nil)) else («FN2-POOL-COMPARE-LOOP» «A» «B» (Prim.plus (Val.int 1) «I») «N» «FN2-POOL»)))) («FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL») («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL») «FN2-POOL» «N» «B» «A» «I»))

theorem decreases (x y : State) (h : step x = .inr y) : measure y < measure x := by
  rcases x with ⟨a,b,i,n,p⟩
  simp only [step] at h
  split_ifs at h <;> cases h
  all_goals
    simp only [measure]
    cases i <;> cases n <;>
      simp_all [«NATP», «NOT», Prim.integerp, Prim.lt, Val.ofBool,
        Val.truthy, Val.isInt, Val.toInt, Val.nil, Val.t, Val.nfix, Prim.plus]
    all_goals split_ifs at * <;> simp_all [Val.nfix, Val.toInt, Prim.plus] <;> omega

theorem go_value (fuel : Nat) (a b i n p : Val) :
    «FN2-POOL-COMPARE-LOOP».go fuel a b i n p =
      Countdown.value Val.nil step fuel (a,b,i,n,p) := by
  induction fuel generalizing a b i n p with
  | zero => rfl
  | succ fuel ih =>
    rw [«FN2-POOL-COMPARE-LOOP».go, Countdown.value_succ]
    simp only [step]
    split_ifs <;> simp_all only [ih]

theorem as_value (a b i n p : Val) :
    «FN2-POOL-COMPARE-LOOP» a b i n p =
      Countdown.value Val.nil step (measure (a,b,i,n,p) + 1) (a,b,i,n,p) := by
  simp only [«FN2-POOL-COMPARE-LOOP», Fn2.ACL2.Fuel.nfix_diff_eq, measure, go_value]

theorem body_equation (a b i n p : Val) :
    bodyValue a b i n p = «FN2-POOL-COMPARE-LOOP» a b i n p := by
  have h := Countdown.value_fixedpoint Val.nil measure step decreases (a,b,i,n,p)
  rw [← as_value] at h
  simp only [step] at h
  unfold bodyValue
  split_ifs at h ⊢ <;> simp_all [← as_value]

/-- Actual emitted function, all arguments and arbitrary pool environment.
There is a result at every sufficient fuel, not merely a stable exhausted NIL. -/
theorem certificate (a b i n p : Val) :
    ∃ result, (∀ fuel, measure (a,b,i,n,p) < fuel →
      Countdown.run step fuel (a,b,i,n,p) = .ok result) ∧
      result = «FN2-POOL-COMPARE-LOOP» a b i n p := by
  obtain ⟨result, hr⟩ := Countdown.certificate measure step decreases (a,b,i,n,p)
  refine ⟨result, hr, ?_⟩
  rw [as_value]
  simp [Countdown.value, hr (measure (a,b,i,n,p) + 1) (by omega)]

theorem positive (p : Val) :
    measure (.int 0,.int 0,.int 0,.int 1,p) < 2 ∧
    Countdown.run step 2 (.int 0,.int 0,.int 0,.int 1,p) =
      .ok (Val.ofList [.sym ":EQUAL",.int 1]) := by
  simp [measure, Countdown.run, step, «NATP», «NOT», «NFIX», Prim.lt, Prim.integerp,
    Prim.plus, Val.isInt, Val.toInt, Val.ofBool, Val.truthy, Val.nfix, Val.ofList, Val.nil, Val.t]

theorem underestimated_fuel_rejected (p : Val) :
    Countdown.run step 1 (.int 0,.int 0,.int 0,.int 1,p) ≠
      .ok («FN2-POOL-COMPARE-LOOP» (.int 0) (.int 0) (.int 0) (.int 1) p) := by
  simp [Countdown.run, step, «NATP», «NOT», Prim.lt, Prim.integerp,
    Prim.plus, Val.isInt, Val.toInt, Val.ofBool, Val.truthy, Val.nil, Val.t]

end Fn2.ACL2.PoolCompare

namespace Fn2.ACL2.PoolCompare
open Fn2.ACL2 Fn2.Instances.LayerAWorld
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def fns : Fns
  | "FN2-POOL-DATAI", [«I», «FN2-POOL»] => some («FN2-POOL-DATAI» «I» «FN2-POOL»)
  | "NOT", [«P»] => some («NOT» «P»)
  | "NFIX", [«X»] => some («NFIX» «X»)
  | "NATP", [«X»] => some («NATP» «X»)
  | "FN2-POOL-COMPARE-LOOP", [«A», «B», «I», «N», «FN2-POOL»] => some («FN2-POOL-COMPARE-LOOP» «A» «B» «I» «N» «FN2-POOL»)
  | _, _ => none
def «FN2-POOL-DATAI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (19)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-POOL-DATAI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 19)), (.var "FN2-POOL")])])
theorem «FN2-POOL-DATAI».decoded : Translation.readTerm 512 «FN2-POOL-DATAI».canonicalBody = some «FN2-POOL-DATAI».body := by rfl
theorem «FN2-POOL-DATAI».canonical_body («I» : Val) («FN2-POOL» : Val) :
    Translation.evalExport 512 «FN2-POOL-DATAI».canonicalBody fns [("I", «I»), ("FN2-POOL", «FN2-POOL»)] = .ok («FN2-POOL-DATAI» «I» «FN2-POOL») := by
  simp only [Translation.evalExport, «FN2-POOL-DATAI».decoded]
  change Translation.eval fns [("I", «I»), ("FN2-POOL", «FN2-POOL»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 19)), (.var "FN2-POOL")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 19) «FN2-POOL»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 19), «FN2-POOL»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
def «NOT».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.symbol [65, 67, 76, 50] [80]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «NOT».body : Term := (.app "IF" [(.var "P"), (.quote Val.nil), (.quote Val.t)])
theorem «NOT».decoded : Translation.readTerm 512 «NOT».canonicalBody = some «NOT».body := by rfl
theorem «NOT».canonical_body («P» : Val) :
    Translation.evalExport 512 «NOT».canonicalBody fns [("P", «P»)] = .ok («NOT» «P») := by
  simp only [Translation.evalExport, «NOT».decoded]
  change Translation.eval fns [("P", «P»)] (.app "IF" [(.var "P"), (.quote Val.nil), (.quote Val.t)]) 512 = _
  refine Translation.eval_if (vc := «P») (va := Val.nil) (vb := Val.t) ?_ ?_ ?_
  ·
    rfl
  ·
    rfl
  ·
    rfl
def «NFIX».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 78, 84, 69, 71, 69, 82, 80]) (.cons (.symbol [65, 67, 76, 50] [88]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «NFIX».body : Term := (.app "IF" [(.app "IF" [(.app "INTEGERP" [(.var "X")]), (.app "NOT" [(.app "<" [(.var "X"), (.quote (Val.int 0))])]), (.quote Val.nil)]), (.var "X"), (.quote (Val.int 0))])
theorem «NFIX».decoded : Translation.readTerm 512 «NFIX».canonicalBody = some «NFIX».body := by rfl
theorem «NFIX».canonical_body («X» : Val) :
    Translation.evalExport 512 «NFIX».canonicalBody fns [("X", «X»)] = .ok («NFIX» «X») := by
  simp only [Translation.evalExport, «NFIX».decoded]
  change Translation.eval fns [("X", «X»)] (.app "IF" [(.app "IF" [(.app "INTEGERP" [(.var "X")]), (.app "NOT" [(.app "<" [(.var "X"), (.quote (Val.int 0))])]), (.quote Val.nil)]), (.var "X"), (.quote (Val.int 0))]) 512 = _
  refine Translation.eval_if (vc := (if ((Prim.integerp «X»)).truthy then («NOT» (Prim.lt «X» (Val.int 0))) else Val.nil)) (va := «X») (vb := (Val.int 0)) ?_ ?_ ?_
  ·
    refine Translation.eval_if (vc := (Prim.integerp «X»)) (va := («NOT» (Prim.lt «X» (Val.int 0)))) (vb := Val.nil) ?_ ?_ ?_
    ·
      refine Translation.eval_app (vs := [«X»]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
    ·
      refine Translation.eval_app (vs := [(Prim.lt «X» (Val.int 0))]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [«X», (Val.int 0)]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
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
    rfl
  ·
    rfl
def «NATP».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 78, 84, 69, 71, 69, 82, 80]) (.cons (.symbol [65, 67, 76, 50] [88]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «NATP».body : Term := (.app "IF" [(.app "INTEGERP" [(.var "X")]), (.app "NOT" [(.app "<" [(.var "X"), (.quote (Val.int 0))])]), (.quote Val.nil)])
theorem «NATP».decoded : Translation.readTerm 512 «NATP».canonicalBody = some «NATP».body := by rfl
theorem «NATP».canonical_body («X» : Val) :
    Translation.evalExport 512 «NATP».canonicalBody fns [("X", «X»)] = .ok («NATP» «X») := by
  simp only [Translation.evalExport, «NATP».decoded]
  change Translation.eval fns [("X", «X»)] (.app "IF" [(.app "INTEGERP" [(.var "X")]), (.app "NOT" [(.app "<" [(.var "X"), (.quote (Val.int 0))])]), (.quote Val.nil)]) 512 = _
  refine Translation.eval_if (vc := (Prim.integerp «X»)) (va := («NOT» (Prim.lt «X» (Val.int 0)))) (vb := Val.nil) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [«X»]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
  ·
    refine Translation.eval_app (vs := [(Prim.lt «X» (Val.int 0))]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«X», (Val.int 0)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
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
def «FN2-POOL-COMPARE-LOOP».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [73]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [73]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [69, 81, 85, 65, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 70, 73, 88]) (.cons (.symbol [65, 67, 76, 50] [78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.symbol [65, 67, 76, 50] [89]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [78]) (.cons (.symbol [65, 67, 76, 50] [66]) (.cons (.symbol [65, 67, 76, 50] [65]) (.cons (.symbol [65, 67, 76, 50] [73]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.symbol [65, 67, 76, 50] [89]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [76, 69, 83, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [89]) (.cons (.symbol [65, 67, 76, 50] [88]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [71, 82, 69, 65, 84, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76, 45, 67, 79, 77, 80, 65, 82, 69, 45, 76, 79, 79, 80]) (.cons (.symbol [65, 67, 76, 50] [65]) (.cons (.symbol [65, 67, 76, 50] [66]) (.cons (.cons (.symbol [65, 67, 76, 50] [66, 73, 78, 65, 82, 89, 45, 43]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [73]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [78]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76, 45, 68, 65, 84, 65, 73]) (.cons (.cons (.symbol [65, 67, 76, 50] [66, 73, 78, 65, 82, 89, 45, 43]) (.cons (.symbol [65, 67, 76, 50] [65]) (.cons (.symbol [65, 67, 76, 50] [73]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76, 45, 68, 65, 84, 65, 73]) (.cons (.cons (.symbol [65, 67, 76, 50] [66, 73, 78, 65, 82, 89, 45, 43]) (.cons (.symbol [65, 67, 76, 50] [66]) (.cons (.symbol [65, 67, 76, 50] [73]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 80, 79, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [78]) (.cons (.symbol [65, 67, 76, 50] [66]) (.cons (.symbol [65, 67, 76, 50] [65]) (.cons (.symbol [65, 67, 76, 50] [73]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-POOL-COMPARE-LOOP».body : Term := (.app "IF" [(.app "IF" [(.app "NOT" [(.app "NATP" [(.var "I")])]), (.app "NOT" [(.app "NATP" [(.var "I")])]), (.app "IF" [(.app "NOT" [(.app "NATP" [(.var "N")])]), (.app "NOT" [(.app "NATP" [(.var "N")])]), (.app "NOT" [(.app "<" [(.var "I"), (.var "N")])])])]), (.app "CONS" [(.quote (Val.sym ":EQUAL")), (.app "CONS" [(.app "NFIX" [(.var "N")]), (.quote Val.nil)])]), (.lam ["X", "Y", "FN2-POOL", "N", "B", "A", "I"] (.app "IF" [(.app "<" [(.var "X"), (.var "Y")]), (.app "CONS" [(.quote (Val.sym ":LESS")), (.app "CONS" [(.var "I"), (.quote Val.nil)])]), (.app "IF" [(.app "<" [(.var "Y"), (.var "X")]), (.app "CONS" [(.quote (Val.sym ":GREATER")), (.app "CONS" [(.var "I"), (.quote Val.nil)])]), (.app "FN2-POOL-COMPARE-LOOP" [(.var "A"), (.var "B"), (.app "BINARY-+" [(.quote (Val.int 1)), (.var "I")]), (.var "N"), (.var "FN2-POOL")])])]) [(.app "FN2-POOL-DATAI" [(.app "BINARY-+" [(.var "A"), (.var "I")]), (.var "FN2-POOL")]), (.app "FN2-POOL-DATAI" [(.app "BINARY-+" [(.var "B"), (.var "I")]), (.var "FN2-POOL")]), (.var "FN2-POOL"), (.var "N"), (.var "B"), (.var "A"), (.var "I")])])
theorem «FN2-POOL-COMPARE-LOOP».decoded : Translation.readTerm 512 «FN2-POOL-COMPARE-LOOP».canonicalBody = some «FN2-POOL-COMPARE-LOOP».body := by rfl
theorem «FN2-POOL-COMPARE-LOOP».canonical_body («A» : Val) («B» : Val) («I» : Val) («N» : Val) («FN2-POOL» : Val) :
    Translation.evalExport 512 «FN2-POOL-COMPARE-LOOP».canonicalBody fns [("A", «A»), ("B", «B»), ("I", «I»), ("N", «N»), ("FN2-POOL", «FN2-POOL»)] = .ok («FN2-POOL-COMPARE-LOOP» «A» «B» «I» «N» «FN2-POOL») := by
  simp only [Translation.evalExport, «FN2-POOL-COMPARE-LOOP».decoded]
  rw [← body_equation «A» «B» «I» «N» «FN2-POOL»]
  change Translation.eval fns [("A", «A»), ("B", «B»), ("I", «I»), ("N", «N»), ("FN2-POOL", «FN2-POOL»)] (.app "IF" [(.app "IF" [(.app "NOT" [(.app "NATP" [(.var "I")])]), (.app "NOT" [(.app "NATP" [(.var "I")])]), (.app "IF" [(.app "NOT" [(.app "NATP" [(.var "N")])]), (.app "NOT" [(.app "NATP" [(.var "N")])]), (.app "NOT" [(.app "<" [(.var "I"), (.var "N")])])])]), (.app "CONS" [(.quote (Val.sym ":EQUAL")), (.app "CONS" [(.app "NFIX" [(.var "N")]), (.quote Val.nil)])]), (.lam ["X", "Y", "FN2-POOL", "N", "B", "A", "I"] (.app "IF" [(.app "<" [(.var "X"), (.var "Y")]), (.app "CONS" [(.quote (Val.sym ":LESS")), (.app "CONS" [(.var "I"), (.quote Val.nil)])]), (.app "IF" [(.app "<" [(.var "Y"), (.var "X")]), (.app "CONS" [(.quote (Val.sym ":GREATER")), (.app "CONS" [(.var "I"), (.quote Val.nil)])]), (.app "FN2-POOL-COMPARE-LOOP" [(.var "A"), (.var "B"), (.app "BINARY-+" [(.quote (Val.int 1)), (.var "I")]), (.var "N"), (.var "FN2-POOL")])])]) [(.app "FN2-POOL-DATAI" [(.app "BINARY-+" [(.var "A"), (.var "I")]), (.var "FN2-POOL")]), (.app "FN2-POOL-DATAI" [(.app "BINARY-+" [(.var "B"), (.var "I")]), (.var "FN2-POOL")]), (.var "FN2-POOL"), (.var "N"), (.var "B"), (.var "A"), (.var "I")])]) 512 = _
  refine Translation.eval_if (vc := (if ((«NOT» («NATP» «I»))).truthy then («NOT» («NATP» «I»)) else (if ((«NOT» («NATP» «N»))).truthy then («NOT» («NATP» «N»)) else («NOT» (Prim.lt «I» «N»))))) (va := (Val.cons (Val.sym ":EQUAL") (Val.cons («NFIX» «N») Val.nil))) (vb := (if ((Prim.lt («FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL») («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL»))).truthy then (Val.cons (Val.sym ":LESS") (Val.cons «I» Val.nil)) else (if ((Prim.lt («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL») («FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL»))).truthy then (Val.cons (Val.sym ":GREATER") (Val.cons «I» Val.nil)) else («FN2-POOL-COMPARE-LOOP» «A» «B» (Prim.plus (Val.int 1) «I») «N» «FN2-POOL»)))) ?_ ?_ ?_
  ·
    refine Translation.eval_if (vc := («NOT» («NATP» «I»))) (va := («NOT» («NATP» «I»))) (vb := (if ((«NOT» («NATP» «N»))).truthy then («NOT» («NATP» «N»)) else («NOT» (Prim.lt «I» «N»)))) ?_ ?_ ?_
    ·
      refine Translation.eval_app (vs := [(«NATP» «I»)]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [«I»]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
        ·
          rfl
    ·
      refine Translation.eval_app (vs := [(«NATP» «I»)]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [«I»]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
        ·
          rfl
    ·
      refine Translation.eval_if (vc := («NOT» («NATP» «N»))) (va := («NOT» («NATP» «N»))) (vb := («NOT» (Prim.lt «I» «N»))) ?_ ?_ ?_
      ·
        refine Translation.eval_app (vs := [(«NATP» «N»)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            refine Translation.eval_app (vs := [«N»]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
          ·
            rfl
      ·
        refine Translation.eval_app (vs := [(«NATP» «N»)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            refine Translation.eval_app (vs := [«N»]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
          ·
            rfl
      ·
        refine Translation.eval_app (vs := [(Prim.lt «I» «N»)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            refine Translation.eval_app (vs := [«I», «N»]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
          ·
            rfl
  ·
    refine Translation.eval_app (vs := [(Val.sym ":EQUAL"), (Val.cons («NFIX» «N») Val.nil)]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [(«NFIX» «N»), Val.nil]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [«N»]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          rfl
  ·
    refine Translation.eval_lam (vs := [(«FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL»), («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL»), «FN2-POOL», «N», «B», «A», «I»]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Prim.plus «A» «I»), «FN2-POOL»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            refine Translation.eval_app (vs := [«A», «I»]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [(Prim.plus «B» «I»), «FN2-POOL»]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [«B», «I»]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
    ·
      refine Translation.eval_if (vc := (Prim.lt («FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL») («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL»))) (va := (Val.cons (Val.sym ":LESS") (Val.cons «I» Val.nil))) (vb := (if ((Prim.lt («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL») («FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL»))).truthy then (Val.cons (Val.sym ":GREATER") (Val.cons «I» Val.nil)) else («FN2-POOL-COMPARE-LOOP» «A» «B» (Prim.plus (Val.int 1) «I») «N» «FN2-POOL»))) ?_ ?_ ?_
      ·
        refine Translation.eval_app (vs := [(«FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL»), («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL»)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_app (vs := [(Val.sym ":LESS"), (Val.cons «I» Val.nil)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [«I», Val.nil]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
            ·
              rfl
      ·
        refine Translation.eval_if (vc := (Prim.lt («FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL») («FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL»))) (va := (Val.cons (Val.sym ":GREATER") (Val.cons «I» Val.nil))) (vb := («FN2-POOL-COMPARE-LOOP» «A» «B» (Prim.plus (Val.int 1) «I») «N» «FN2-POOL»)) ?_ ?_ ?_
        ·
          refine Translation.eval_app (vs := [(«FN2-POOL-DATAI» (Prim.plus «B» «I») «FN2-POOL»), («FN2-POOL-DATAI» (Prim.plus «A» «I») «FN2-POOL»)]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          refine Translation.eval_app (vs := [(Val.sym ":GREATER"), (Val.cons «I» Val.nil)]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                refine Translation.eval_app (vs := [«I», Val.nil]) (by decide) (by decide) ?_ (by rfl)
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
              ·
                rfl
        ·
          refine Translation.eval_app (vs := [«A», «B», (Prim.plus (Val.int 1) «I»), «N», «FN2-POOL»]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  refine Translation.eval_app (vs := [(Val.int 1), «I»]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
#print axioms certificate
#print axioms «FN2-POOL-COMPARE-LOOP».canonical_body
end Fn2.ACL2.PoolCompare

end
