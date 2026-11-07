/-!
# Fn2.Distinct: distinctness of a long list by a bit set, for the kernel

`decide` on `List.Nodup` compares every pair: on the registry's 1519 identities that is a million
comparisons, which the kernel's reduction holds in memory (over 40 GB). `bitsDistinct` maps the
list to natural keys and checks them against a bit set in one pass, every step a `Nat` operation
the kernel computes on literals; `nodup_of_bitsDistinct` turns the check into `Nodup` of the
list itself (any key function: distinct keys imply distinct elements).
-/

namespace Fn2.Distinct

/-- The keys are pairwise distinct and none is set in `acc`. -/
def bitsDistinct : List Nat → Nat → Bool
  | [], _ => true
  | k :: ks, acc => !acc.testBit k && bitsDistinct ks (acc ||| 1 <<< k)

theorem bitsDistinct_sound : ∀ (l : List Nat) (acc : Nat), bitsDistinct l acc = true →
    l.Nodup ∧ ∀ k ∈ l, acc.testBit k = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | k :: ks, acc, h => by
    simp only [bitsDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hk, hks⟩ := bitsDistinct_sound ks _ h.2
    have hbit : ∀ j, (acc ||| 1 <<< k).testBit j = (acc.testBit j || decide (k = j)) := by
      intro j; simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hk⟩, ?_⟩
    · have := hks k hm; rw [hbit] at this; simp at this
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact h.1
      · have := hks j hj; rw [hbit] at this; simp at this; exact this.1

/-- A list whose keys pass the bit-set check has no duplicate. -/
theorem nodup_of_bitsDistinct {α : Type} (key : α → Nat) (l : List α)
    (h : bitsDistinct (l.map key) 0 = true) : l.Nodup :=
  List.Pairwise.of_map key (fun _ _ hne heq => hne (congrArg key heq)) (bitsDistinct_sound _ 0 h).1

/-- A teeth check: the bit set refuses a repeated key and accepts distinct ones. -/
example : bitsDistinct [3, 70000, 5, 3] 0 = false ∧ bitsDistinct [3, 70000, 5] 0 = true := by
  decide +kernel

end Fn2.Distinct
