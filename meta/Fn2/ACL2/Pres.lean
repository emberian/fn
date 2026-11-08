module

public import Fn2.ACL2.Val
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-!
# Fn2.ACL2.Pres: the list facts the projection lemmas rewrite by

`meta/emit/emit_pres.py` states, for a translated function `F` and a path of literal `NTH`
indices, that the projection of `F`'s result along the path is a projection of one of its
arguments, and proves each by unfolding `F` once and rewriting with these facts and the facts of
`F`'s callees (`Fn2.Instances.LayerAPres`). `UPDATE-NTH` here is ACL2's: it pads a short list with
`NIL`, so reading another index reads what was there (`NIL` past the end) and reading the written
index reads the value written, at every list.
-/

namespace Fn2.ACL2.Pres
open Fn2.ACL2

theorem nth_ite (n : Val) (c : Prop) [Decidable c] (a b : Val) :
    Native.nth n (if c then a else b) = if c then Native.nth n a else Native.nth n b := by
  split <;> rfl

theorem nth_cons_zero (a l : Val) : Native.nth (Val.int 0) (Val.cons a l) = a := rfl

theorem nth_cons_succ (i : Int) (a l : Val) (h : 0 < i) :
    Native.nth (Val.int i) (Val.cons a l) = Native.nth (Val.int (i - 1)) l := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, i = (n : Int) + 1 := ⟨(i - 1).toNat, by omega⟩
  simp only [Native.nth, Val.nfix, Val.toInt]
  rw [show ((n : Int) + 1).toNat = n + 1 by omega, show ((n : Int) + 1 - 1).toNat = n by omega]
  rfl

theorem nthN_updateNthN_same : ∀ (n : Nat) (v l : Val),
    Native.nthN n (Native.updateNthN n v l) = v
  | 0, _, _ => rfl
  | n + 1, v, l => by
    simp only [Native.updateNthN, Native.nthN]
    exact nthN_updateNthN_same n v l.cdr

theorem nthN_atom (m : Nat) (l : Val) (h : l.isCons = false) : Native.nthN m l = Val.nil := by
  cases l <;> first | rfl | (cases m <;> rfl) | simp [Val.isCons] at h

theorem nthN_succ (m : Nat) (l : Val) : Native.nthN (m + 1) l = Native.nthN m l.cdr := by
  cases l with
  | cons a d => rfl
  | _ => simp only [Val.cdr]; rw [nthN_atom _ _ rfl, nthN_atom _ _ rfl]

theorem nthN_zero (l : Val) : Native.nthN 0 l = l.car := by
  cases l <;> rfl

theorem nthN_updateNthN_ne : ∀ (m n : Nat) (v l : Val), m ≠ n →
    Native.nthN m (Native.updateNthN n v l) = Native.nthN m l
  | 0, 0, _, _, h => absurd rfl h
  | m + 1, 0, v, l, _ => by
    simp only [Native.updateNthN, Native.nthN]; rw [nthN_succ]
  | 0, n + 1, v, l, _ => by
    simp only [Native.updateNthN, Native.nthN]; rw [nthN_zero]
  | m + 1, n + 1, v, l, h => by
    simp only [Native.updateNthN, Native.nthN]
    rw [nthN_updateNthN_ne m n v l.cdr (by omega), nthN_succ]

theorem nth_upd_same (i : Int) (v l : Val) :
    Native.nth (Val.int i) (Native.updateNth (Val.int i) v l) = v :=
  nthN_updateNthN_same _ v l

theorem nth_upd_ne (i j : Int) (v l : Val) (h : i.toNat ≠ j.toNat) :
    Native.nth (Val.int i) (Native.updateNth (Val.int j) v l) = Native.nth (Val.int i) l :=
  nthN_updateNthN_ne _ _ v l h

theorem consp_ite (c : Prop) [Decidable c] (a b : Val) :
    Prim.consp (if c then a else b) = if c then Prim.consp a else Prim.consp b := by
  split <;> rfl

theorem consp_cons (a l : Val) : Prim.consp (Val.cons a l) = Val.t := rfl

end Fn2.ACL2.Pres

end
