module

public import Fn2.ACL2.Val

@[expose] public section
namespace Fn2.ACL2.PrimitiveContracts

/-- The integer-result EXPT fragment needs no rational-number library. -/
theorem expt_nonnegative (b : Int) (n : Nat) :
    Native.expt (.int b) (.int n) = .int (b ^ n) := by
  cases n with
  | zero => simp [Native.expt, Val.toInt]
  | succ n =>
    by_cases hb : b = 0
    · simp [Native.expt, Val.toInt, hb, Int.pow_succ, show (n : Int) + 1 ≠ 0 by omega]
    · simp [Native.expt, Val.toInt, hb, Int.pow_succ, show (n : Int) + 1 ≠ 0 by omega]

end Fn2.ACL2.PrimitiveContracts
end
