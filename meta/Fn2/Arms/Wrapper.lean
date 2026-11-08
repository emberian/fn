import Fn2.Arms.Core

namespace Fn2.Arms.Wrapper
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core

/-- Lift checked accepted/refused branches to successful whole-core
interpretation. The accepted branch must supply an actual successful body run
and exact reconstruction of every answer and child. -/
theorem certificate (w : World) (layout : List String) (k : Kind) (a : Arm)
    (observe : Bool) (args : List Val) (emitted code : Val)
    (arity : args.length = nCore observe + 1)
    (complete : (args.getLastD Val.nil).toList.length = layout.length)
    (snapshot : callFn w (k.name ++ "-SNAPSHOT-READ-CODE")
      [args.headD Val.nil, args.getLastD Val.nil] = .ok code)
    (accepted : code = .sym ":OK" → ∃ slot kind fuel child,
      callFn w "FN2-MACHINE-SLOT" [args.headD Val.nil, args.getLastD Val.nil] = .ok slot ∧
      const w ("*" ++ k.name ++ "-KIND*") = .ok kind ∧
      runArm (coreWorld w layout) (coreKind k layout) a observe
        ([args.headD Val.nil, slot, kind, ordOf w k] ++
          (args.take (nCore observe)).drop 1 ++ (args.getLastD Val.nil).toList) fuel = .ok child ∧
      finish observe layout child = .ok emitted)
    (refused : code ≠ .sym ":OK" →
      refusedEntry w layout observe (args.getLastD Val.nil).toList = .ok emitted) :
    ∃ fuel result, runCore w layout k a observe args fuel = .ok result ∧ result = emitted := by
  by_cases h : code = .sym ":OK"
  · obtain ⟨slot, kind, fuel, child, hs, hk, hr, hf⟩ := accepted h
    refine ⟨fuel, emitted, ?_, rfl⟩
    simp only [runCore, arity, complete, ne_eq, not_true_eq_false, ↓reduceIte,
      snapshot, except_ok_bind, h, beq_self_eq_true, hs, hk, hr, hf]
  · refine ⟨0, emitted, ?_, rfl⟩
    simp only [runCore, arity, complete, ne_eq, not_true_eq_false, ↓reduceIte,
      snapshot, except_ok_bind, beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, refused h]

/-- A missing child cannot be hidden in a narrowed signature. -/
theorem omitted_child_rejected (w : World) (layout : List String) (k : Kind) (a : Arm)
    (observe : Bool) (args : List Val) (fuel : Nat) (result : Val)
    (omitted : (args.getLastD Val.nil).toList.length ≠ layout.length) :
    runCore w layout k a observe args fuel ≠ .ok result := by
  intro h
  exact omitted (runCore_cases w layout k a observe args fuel result h).2.1

end Fn2.Arms.Wrapper
