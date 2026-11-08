module

public import Fn2.ACL2.Fuel
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-! A decreasing loop produces a result at adequate fuel. Exhaustion is a
distinct error, so stability of an exhausted computation cannot certify it. -/
namespace Fn2.ACL2.Countdown

def run (step : α → Sum β α) : Nat → α → Except Unit β
  | 0, _ => .error ()
  | fuel + 1, x => match step x with
    | .inl result => .ok result
    | .inr next => run step fuel next

theorem adequate (measure : α → Nat) (step : α → Sum β α)
    (decreases : ∀ x y, step x = .inr y → measure y < measure x)
    (fuel : Nat) (x : α) (enough : measure x < fuel) :
    ∃ result, run step fuel x = .ok result := by
  induction fuel generalizing x with
  | zero => omega
  | succ fuel ih =>
    cases h : step x with
    | inl result => exact ⟨result, by simp [run, h]⟩
    | inr next =>
      obtain ⟨result, hr⟩ := ih next (by have := decreases x next h; omega)
      exact ⟨result, by simpa [run, h] using hr⟩

theorem stable (step : α → Sum β α) (fuel more : Nat) (x : α) (result : β)
    (success : run step fuel x = .ok result) :
    run step (fuel + more) x = .ok result := by
  induction fuel generalizing x with
  | zero => simp [run] at success
  | succ fuel ih =>
    rw [show fuel + 1 + more = (fuel + more) + 1 by omega]
    cases h : step x with
    | inl value => simpa [run, h] using success
    | inr next =>
      simpa [run, h] using ih next (by simpa [run, h] using success)

theorem certificate (measure : α → Nat) (step : α → Sum β α)
    (decreases : ∀ x y, step x = .inr y → measure y < measure x) (x : α) :
    ∃ result, ∀ fuel, measure x < fuel → run step fuel x = .ok result := by
  obtain ⟨result, hr⟩ := adequate measure step decreases (measure x + 1) x (by omega)
  refine ⟨result, fun fuel hf => ?_⟩
  have hs := stable step (measure x + 1) (fuel - (measure x + 1)) x result hr
  simpa only [Nat.add_sub_of_le (by omega : measure x + 1 ≤ fuel)] using hs

/-- A supplied semantic solution is unique above the measure. This connects
the fueled translation to an independently admitted defining equation. -/
theorem equals_solution (measure : α → Nat) (step : α → Sum β α)
    (decreases : ∀ x y, step x = .inr y → measure y < measure x)
    (solution : α → β)
    (equation : ∀ x, solution x = match step x with
      | .inl result => result | .inr next => solution next)
    (fuel : Nat) (x : α) (enough : measure x < fuel) :
    run step fuel x = .ok (solution x) := by
  induction fuel generalizing x with
  | zero => omega
  | succ fuel ih =>
    rw [equation x]
    cases h : step x with
    | inl result => simp [run, h]
    | inr next =>
      simpa [run, h] using ih next (by have := decreases x next h; omega)

def value (default : β) (step : α → Sum β α) (fuel : Nat) (x : α) : β :=
  match run step fuel x with | .ok result => result | .error _ => default

theorem value_succ (default : β) (step : α → Sum β α) (fuel : Nat) (x : α) :
    value default step (fuel + 1) x = match step x with
      | .inl result => result | .inr next => value default step fuel next := by
  cases h : step x <;> simp [value, run, h]

theorem value_fixedpoint (default : β) (measure : α → Nat) (step : α → Sum β α)
    (decreases : ∀ x y, step x = .inr y → measure y < measure x) (x : α) :
    value default step (measure x + 1) x = match step x with
      | .inl result => result
      | .inr next => value default step (measure next + 1) next := by
  rw [value_succ]
  cases h : step x with
  | inl result => rfl
  | inr next =>
    have hd := decreases x next h
    obtain ⟨result, hr⟩ := adequate measure step decreases (measure next + 1) next (by omega)
    have hs := stable step (measure next + 1) (measure x - (measure next + 1)) next result hr
    rw [Nat.add_sub_of_le (by omega : measure next + 1 ≤ measure x)] at hs
    simp [value, hr, hs]

def witnessStep : Nat → Sum Nat Nat
  | 0 => .inl 7
  | n + 1 => .inr n

theorem witness_decreases (n m : Nat) (h : witnessStep n = .inr m) : m < n := by
  cases n <;> simp [witnessStep] at h
  omega

theorem positive :
    (∀ n m, witnessStep n = .inr m → m < n) ∧
    run witnessStep 4 3 = .ok 7 := ⟨witness_decreases, rfl⟩

theorem underestimated_fuel_rejected : run witnessStep 3 3 ≠ .ok 7 := by
  simp [run, witnessStep]

theorem missing_decrease_rejected :
    (∀ fuel, run (fun n : Nat => (Sum.inr n : Sum Nat Nat)) fuel 0 = .error ()) := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

end Fn2.ACL2.Countdown

end
