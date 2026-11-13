module

public import Fn2.Arms.Wrapper
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.List.Control

@[expose] public section

/-!
# Fn2.Arms.Combinators: compositional proof combinators for mechanical arm certificates

Proved once over arbitrary worlds, kinds, and symbolic child tuples `kids : Fin n → Val` without
unfolding concrete 57-child worlds during kernel unification:

* **indexed child tuples**: `tupleImage`, `tupleStobjs`, `patchKids`, `IsListN`, and `kidsOfVal`
  avoid expanding `Fin 57 → Val` into 57 free variables while equating interpreter `stobj`/`setStobj`
  operations directly with ACL2 `Native.nth`/`Native.updateNth` over `fn2-core`;
* **reflected column-write canonicalizer**: `fieldWrite`, `applyFieldWrites`, and `sortFieldWrites`
  align pending-write batches with ACL2's generated column-write order in a single rewrite;
* **unified `put` and `flush` combinators**: evaluate checked writes and phase updates into a single
  conditional without duplicating continuation proofs;
* **syntax-directed `Term.eval` / `ev` / `readNext` combinators**: separate closed syntax reading
  from environment-dependent evaluation;
* **`@CORE` operation adapters and step/terminal combinators**: collapse/spread 57-child core
  signatures and step through `:let`, `:set`, `:next`, `:do`, `:issue`, `:if`, `:cond`, `:case`,
  `:wake-row`, `:park`, `:stop`, `:goto`, and terminals in `O(1)` kernel steps per AST node.
-/

namespace Fn2.Arms.Combinators
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core

set_option autoImplicit false

deriving instance DecidableEq for Except
deriving instance DecidableEq for Call
deriving instance DecidableEq for Answers
deriving instance DecidableEq for Op

mutual
def termBeq : Term → Term → Bool
  | .var x, .var y => x == y
  | .quote x, .quote y => x == y
  | .app f as, .app g bs => f == g && termListBeq as bs
  | .lam fs b as, .lam gs c bs => fs == gs && termBeq b c && termListBeq as bs
  | _, _ => false

def termListBeq : List Term → List Term → Bool
  | [], [] => true
  | a :: as, b :: bs => termBeq a b && termListBeq as bs
  | _, _ => false
end

mutual
theorem termBeq_eq : ∀ (t1 t2 : Term), termBeq t1 t2 = true → t1 = t2
  | .var x, .var y, h => by simp [termBeq] at h; exact congrArg Term.var h
  | .quote x, .quote y, h => by simp [termBeq] at h; exact congrArg Term.quote h
  | .app f as, .app g bs, h => by
    simp only [termBeq, Bool.and_eq_true] at h
    rw [beq_iff_eq.mp h.1, termListBeq_eq as bs h.2]
  | .lam fs b as, .lam gs c bs, h => by
    simp only [termBeq, Bool.and_eq_true] at h
    rw [beq_iff_eq.mp h.1.1, termBeq_eq b c h.1.2, termListBeq_eq as bs h.2]
  | .var _, .quote _, h | .var _, .app _ _, h | .var _, .lam _ _ _, h
  | .quote _, .var _, h | .quote _, .app _ _, h | .quote _, .lam _ _ _, h
  | .app _ _, .var _, h | .app _ _, .quote _, h | .app _ _, .lam _ _ _, h
  | .lam _ _ _, .var _, h | .lam _ _ _, .quote _, h | .lam _ _ _, .app _ _, h => by
    simp [termBeq] at h

theorem termListBeq_eq : ∀ (as bs : List Term), termListBeq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [termListBeq, Bool.and_eq_true] at h
    rw [termBeq_eq a b h.1, termListBeq_eq as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [termListBeq] at h
end

def exceptTermOk (r : Except String Term) (t : Term) : Bool :=
  match r with
  | .ok t' => termBeq t' t
  | .error _ => false

theorem exceptTermOk_eq {r : Except String Term} {t : Term} (h : exceptTermOk r t = true) :
    r = .ok t := by
  cases r with
  | error _ => cases h
  | ok t' => exact congrArg Except.ok (termBeq_eq t' t h)

/-! ### Computable list-index & nodup witnesses -/

def findIdx? (name : String) : List String → Option Nat
  | [] => none
  | x :: xs => if x == name then some 0 else (findIdx? name xs).map (· + 1)

def nodupB : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

theorem findIdx?_lt {name : String} {xs : List String} {idx : Nat}
    (h : findIdx? name xs = some idx) : idx < xs.length := by
  induction xs generalizing idx with
  | nil => simp [findIdx?] at h
  | cons x xs ih =>
    simp only [findIdx?] at h
    split at h
    · simp at h; subst h; simp
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      have := ih hj
      simp; omega

theorem nodupB_append {xs ys : List String} (h : nodupB (xs ++ ys) = true) :
    nodupB xs = true ∧ nodupB ys = true ∧ (∀ x ∈ xs, ys.contains x = false) := by
  induction xs with
  | nil => exact ⟨rfl, h, fun _ hx => nomatch hx⟩
  | cons x xs ih =>
    simp only [List.cons_append, nodupB, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_append, Bool.or_eq_false_iff] at h
    obtain ⟨⟨hx1, hx2⟩, hrest⟩ := h
    obtain ⟨h1, h2, h3⟩ := ih hrest
    refine ⟨by simp only [nodupB, hx1, h1, Bool.not_false, Bool.and_self], h2, ?_⟩
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx2
    · exact h3 z hz

/-! ### Indexed child tuples (`Fin n → Val`) -/

def tupleImage {n : Nat} (kids : Fin n → Val) : Val :=
  Val.ofList (List.ofFn kids)

def tupleStobjs {n : Nat} (tuple : List String) (kids : Fin n → Val) : List (String × Val) :=
  tuple.zip (List.ofFn kids)

def patchKids {n : Nat} (kids : Fin n → Val) (idx : Nat) (v : Val) : Fin n → Val :=
  fun i => if i.val = idx then v else kids i

@[simp] theorem patchKids_same {n : Nat} (kids : Fin n → Val) (idx : Nat) (v : Val) (hi : idx < n) :
    patchKids kids idx v ⟨idx, hi⟩ = v := by
  simp [patchKids]

theorem patchKids_ne {n : Nat} (kids : Fin n → Val) (idx j : Nat) (v : Val) (hj : j < n) (hne : j ≠ idx) :
    patchKids kids idx v ⟨j, hj⟩ = kids ⟨j, hj⟩ := by
  simp [patchKids, hne]

theorem patchKids_self {n : Nat} (kids : Fin n → Val) (idx : Nat) (hi : idx < n) :
    patchKids kids idx (kids ⟨idx, hi⟩) = kids := by
  funext ⟨j, hj⟩
  simp only [patchKids]
  split
  · rename_i heq; subst heq; rfl
  · rfl

theorem patchKids_idem {n : Nat} (kids : Fin n → Val) (idx : Nat) (v1 v2 : Val) :
    patchKids (patchKids kids idx v1) idx v2 = patchKids kids idx v2 := by
  funext ⟨j, hj⟩
  simp only [patchKids]
  split <;> rfl

theorem patchKids_comm {n : Nat} (kids : Fin n → Val) (i j : Nat) (vi vj : Val) (hne : i ≠ j) :
    patchKids (patchKids kids i vi) j vj = patchKids (patchKids kids j vj) i vi := by
  funext ⟨k, hk⟩
  simp only [patchKids]
  by_cases hkj : k = j
  · subst hkj; simp [Ne.symm hne]
  · by_cases hki : k = i
    · subst hki; simp [hkj]
    · simp [hkj, hki]

theorem nthN_ofList (xs : List Val) (i : Nat) (hi : i < xs.length) :
    Native.nthN i (Val.ofList xs) = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

theorem updateNthN_ofList (xs : List Val) (i : Nat) (v : Val) (hi : i < xs.length) :
    Native.updateNthN i v (Val.ofList xs) = Val.ofList (xs.set i v) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [Native.updateNthN, Val.ofList, Val.car, Val.cdr, List.set_cons_succ]
      exact congrArg (Val.cons x) (ih i (by simpa using hi))

theorem nth_tupleImage {n : Nat} (kids : Fin n → Val) (idx : Nat) (hi : idx < n) :
    Native.nth (.int idx) (tupleImage kids) = kids ⟨idx, hi⟩ := by
  have hl : idx < (List.ofFn kids).length := by simp [hi]
  simp only [tupleImage, Native.nth, Val.nfix, Val.toInt, Int.toNat_natCast]
  rw [nthN_ofList (List.ofFn kids) idx hl, List.getElem_ofFn]

theorem ofFn_patchKids {n : Nat} (kids : Fin n → Val) (idx : Nat) (v : Val) :
    (List.ofFn kids).set idx v = List.ofFn (patchKids kids idx v) := by
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
    simp only [patchKids]
    by_cases h : idx = j
    · subst h; simp
    · have h' : j ≠ idx := Ne.symm h
      simp [h, h']

theorem tupleImage_patchKids {n : Nat} (kids : Fin n → Val) (idx : Nat) (v : Val) (hi : idx < n) :
    tupleImage (patchKids kids idx v) = Native.updateNth (.int idx) v (tupleImage kids) := by
  have hl : idx < (List.ofFn kids).length := by simp [hi]
  simp only [tupleImage, Native.updateNth, Val.nfix, Val.toInt, Int.toNat_natCast]
  rw [updateNthN_ofList (List.ofFn kids) idx v hl, ofFn_patchKids]

theorem updateNth_nth_tupleImage {n : Nat} (kids : Fin n → Val) (idx : Nat) (hi : idx < n) :
    Native.updateNth (.int idx) (Native.nth (.int idx) (tupleImage kids)) (tupleImage kids) =
      tupleImage kids := by
  rw [nth_tupleImage kids idx hi, ← tupleImage_patchKids kids idx _ hi, patchKids_self kids idx hi]

theorem find_zip_of_findIdx {ks : List String} {vs : List Val} {name : String} {idx : Nat}
    (hlen : ks.length = vs.length) (hidx : findIdx? name ks = some idx)
    (hi : idx < vs.length := by rw [← hlen]; exact findIdx?_lt hidx) :
    (ks.zip vs).find? (·.1 == name) = some (name, vs[idx]) := by
  induction ks generalizing vs idx with
  | nil => simp [findIdx?] at hidx
  | cons k ks ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [findIdx?] at hidx
      by_cases hk : (k == name) = true
      · simp only [hk, ↓reduceIte, Option.some.injEq] at hidx
        subst hidx
        have hkn : k = name := beq_iff_eq.mp hk
        subst hkn
        simp
      · have hkf : (k == name) = false := Bool.eq_false_iff.mpr hk
        simp only [hkf, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hidx
        obtain ⟨j, hj, rfl⟩ := hidx
        simp only [List.zip_cons_cons, List.find?_cons, hkf]
        exact ih (by simpa using hlen) hj (by simpa using hi)

theorem map_zip_not_mem (ks : List String) (vs : List Val) (name : String) (v : Val)
    (hc : ks.contains name = false) :
    (ks.zip vs).map (fun p => if p.1 == name then (name, v) else p) = ks.zip vs := by
  induction ks generalizing vs with
  | nil => rfl
  | cons k ks ih =>
    cases vs with
    | nil => rfl
    | cons w vs =>
      simp only [List.contains_cons, Bool.or_eq_false_iff] at hc
      have hkf : (k == name) = false := by
        cases hnk : (name == k)
        · exact beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp hnk))
        · rw [hc.1] at hnk; cases hnk
      simp only [List.zip_cons_cons, List.map_cons, hkf, Bool.false_eq_true, ↓reduceIte]
      exact congrArg ((k, w) :: ·) (ih vs hc.2)

theorem map_zip_set_of_findIdx {ks : List String} {vs : List Val} {name : String} {idx : Nat} (v : Val)
    (hlen : ks.length = vs.length) (hnd : nodupB ks = true) (hidx : findIdx? name ks = some idx) :
    (ks.zip vs).map (fun p => if p.1 == name then (name, v) else p) = ks.zip (vs.set idx v) := by
  induction ks generalizing vs idx with
  | nil => simp [findIdx?] at hidx
  | cons k ks ih =>
    cases vs with
    | nil => simp at hlen
    | cons w vs =>
      simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at hnd
      simp only [findIdx?] at hidx
      by_cases hk : (k == name) = true
      · simp only [hk, ↓reduceIte, Option.some.injEq] at hidx
        subst hidx
        have hkn : k = name := beq_iff_eq.mp hk
        subst hkn
        simp only [List.zip_cons_cons, List.map_cons, beq_self_eq_true, ↓reduceIte, List.set_cons_zero]
        exact congrArg ((k, v) :: ·) (map_zip_not_mem ks vs k v hnd.1)
      · have hkf : (k == name) = false := Bool.eq_false_iff.mpr hk
        simp only [hkf, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hidx
        obtain ⟨j, hj, rfl⟩ := hidx
        simp only [List.zip_cons_cons, List.map_cons, hkf, Bool.false_eq_true, ↓reduceIte, List.set_cons_succ]
        exact congrArg ((k, w) :: ·) (ih (by simpa using hlen) hnd.2 hj)

theorem find_tupleStobjs {n : Nat} (tuple : List String) (kids : Fin n → Val)
    (name : String) (idx : Nat) (hi : idx < n)
    (hlen : tuple.length = n) (hidx : findIdx? name tuple = some idx) :
    (tupleStobjs tuple kids).find? (·.1 == name) = some (name, kids ⟨idx, hi⟩) := by
  have hl : tuple.length = (List.ofFn kids).length := by simp [hlen]
  have hf := find_zip_of_findIdx hl hidx (by simp [hi])
  simpa [tupleStobjs] using hf

theorem stobj_tupleStobjs {n : Nat} (tuple : List String) (kids : Fin n → Val)
    (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int)
    (name : String) (idx : Nat) (hi : idx < n)
    (hlen : tuple.length = n) (hidx : findIdx? name tuple = some idx) :
    stobj ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩ name =
      .ok (kids ⟨idx, hi⟩) := by
  simp [stobj, find_tupleStobjs tuple kids name idx hi hlen hidx]

theorem env_get_tupleStobjs {n : Nat} (tuple : List String) (kids : Fin n → Val)
    (vars : Env) (name : String) (idx : Nat) (hi : idx < n)
    (hvars : vars.get? name = none) (hlen : tuple.length = n) (hidx : findIdx? name tuple = some idx) :
    (vars ++ tupleStobjs tuple kids).get? name = some (kids ⟨idx, hi⟩) := by
  have hvf : vars.find? (·.1 == name) = none := by
    cases hf : vars.find? (·.1 == name) <;> simp_all [Env.get?]
  simp [Env.get?, List.find?_append, hvf, find_tupleStobjs tuple kids name idx hi hlen hidx]

theorem setStobj_tupleStobjs {n : Nat} (tuple : List String) (kids : Fin n → Val)
    (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int)
    (name : String) (idx : Nat) (v : Val)
    (hlen : tuple.length = n) (hnd : nodupB tuple = true) (hidx : findIdx? name tuple = some idx) :
    setStobj ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩ name v =
      ⟨tupleStobjs tuple (patchKids kids idx v), vars, pending, next, nextDone, woken, loopWork⟩ := by
  have hl : tuple.length = (List.ofFn kids).length := by simp [hlen]
  simp only [setStobj, tupleStobjs, map_zip_set_of_findIdx v hl hnd hidx, ofFn_patchKids]

theorem mapM_stobj_zip (ks : List String) (vs : List Val) (st : St)
    (hlen : ks.length = vs.length) (hnd : nodupB ks = true)
    (hsub : ∀ k v, (ks.zip vs).find? (·.1 == k) = some (k, v) → stobj st k = .ok v) :
    ks.mapM (stobj st) = .ok vs := by
  induction ks generalizing vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons k ks ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at hnd
      have hk0 : stobj st k = .ok v := hsub k v (by simp)
      have hrest : ks.mapM (stobj st) = .ok vs := by
        apply ih vs (by simpa using hlen) hnd.2
        intro k' v' hf
        apply hsub k' v'
        have hmem : k' ∈ ks := by
          have hb := List.find?_some hf
          have hm := List.mem_of_find?_eq_some hf
          exact (beq_iff_eq.mp hb) ▸ (List.of_mem_zip hm).1
        have hne : (k == k') = false := by
          cases hc : (k == k')
          · rfl
          · have heq := beq_iff_eq.mp hc; subst heq
            have : ks.contains k = true := List.contains_iff_mem.mpr hmem
            rw [hnd.1] at this; cases this
        simp [hne, hf]
      simp [List.mapM_cons, hk0, hrest]

theorem tupleVals_tupleStobjs {n : Nat} (f : Frame) (tuple : List String) (kids : Fin n → Val)
    (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int)
    (htup : f.kind.tuple = tuple) (hlen : tuple.length = n) (hnd : nodupB tuple = true) :
    tupleVals f ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩ =
      .ok (List.ofFn kids) := by
  unfold tupleVals
  rw [htup]
  apply mapM_stobj_zip tuple (List.ofFn kids) _ (by simp [hlen]) hnd
  intro k v hf
  simp [stobj, tupleStobjs, hf]

theorem chargeResult_tupleStobjs {n : Nat} (f : Frame) (tuple : List String) (kids : Fin n → Val)
    (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (b s d r : Val)
    (htup : f.kind.tuple = tuple) (hlen : tuple.length = n) (hnd : nodupB tuple = true) :
    chargeResult f ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, (0, 0, 0)⟩ b s d r =
      .ok (.done (Val.ofList ([b, s, d, r] ++ List.ofFn kids))) := by
  simp [chargeResult, tupleVals_tupleStobjs f tuple kids vars pending next nextDone woken (0, 0, 0) htup hlen hnd]

theorem wakeResult_tupleStobjs {n : Nat} (f : Frame) (tuple : List String) (kids : Fin n → Val)
    (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int) (v : Val)
    (htup : f.kind.tuple = tuple) (hlen : tuple.length = n) (hnd : nodupB tuple = true) :
    wakeResult f ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩ v =
      .ok (.done (Val.ofList (v :: List.ofFn kids))) := by
  simp [wakeResult, tupleVals_tupleStobjs f tuple kids vars pending next nextDone woken loopWork htup hlen hnd]

theorem finish_arm_tupleImage {n : Nat} (tuple : List String) (kids : Fin n → Val)
    (b s d r : Val) (hlen : tuple.length = n) :
    finish false tuple (Val.ofList ([b, s, d, r] ++ List.ofFn kids)) =
      .ok (Val.ofList [b, s, d, r, tupleImage kids]) := by
  have hl : ([b, s, d, r] ++ List.ofFn kids).length = 4 + tuple.length := by simp [hlen]; omega
  unfold finish
  rw [toList_ofList', hl]
  simp [nRes, tupleImage]

theorem finish_observe_tupleImage {n : Nat} (tuple : List String) (kids : Fin n → Val)
    (w : Val) (hlen : tuple.length = n) :
    finish true tuple (Val.ofList (w :: List.ofFn kids)) =
      .ok (Val.ofList [w, tupleImage kids]) := by
  have hl : (w :: List.ofFn kids).length = 1 + tuple.length := by simp [hlen]; omega
  unfold finish
  rw [toList_ofList', hl]
  simp [nRes, tupleImage]

theorem refusedEntry_tupleImage {n : Nat} (w : World) (tuple : List String) (observe : Bool)
    (kids : Fin n → Val) (ctrlIdx : Nat) (reason stopped noneVal emptyVal : Val)
    (hctrl : tuple.idxOf "FN2-CONTROL" = ctrlIdx) (hci : ctrlIdx < n)
    (hreason : const w (if observe then "*FN2-STOP-REASON-MACHINE-OBSERVATION*"
      else "*FN2-STOP-REASON-MACHINE-PHASE*") = .ok reason)
    (hstop : callFn w "FN2-CONTROL-RECORD-STOP" [reason, Native.nth (.int ctrlIdx) (tupleImage kids)] = .ok stopped)
    (hnone : const w "*FN2-NONE*" = .ok noneVal)
    (hempty : const w "*FN2-WORK-EMPTY*" = .ok emptyVal) :
    refusedEntry w tuple observe (tupleImage kids).toList =
      .ok (if observe then
        Val.ofList [noneVal, Native.updateNth (.int ctrlIdx) stopped (tupleImage kids)]
      else
        Val.ofList [.int 0, emptyVal, .int 0, Val.nil,
          Native.updateNth (.int ctrlIdx) stopped (tupleImage kids)]) := by
  have htl : (tupleImage kids).toList = List.ofFn kids := toList_ofList' _
  have hgd : (List.ofFn kids).getD ctrlIdx Val.nil = Native.nth (.int ctrlIdx) (tupleImage kids) := by
    rw [nth_tupleImage kids ctrlIdx hci, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hci]
  have hset : Val.ofList ((List.ofFn kids).set ctrlIdx stopped) =
      Native.updateNth (.int ctrlIdx) stopped (tupleImage kids) := by
    rw [ofFn_patchKids, ← tupleImage_patchKids kids ctrlIdx stopped hci, tupleImage]
  simp only [refusedEntry, coreStop, htl, hctrl, hreason, hgd, hstop, except_ok_bind]
  cases observe <;> simp [hnone, hempty, hset]

theorem omitted_child_rejected_arm (w : World) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (result : Val)
    (omitted : args.length ≠ (if observe then 10 else 5) + k.tuple.length) :
    runArm w k a observe args fuel ≠ .ok result := by
  intro h
  unfold runArm at h
  cases hcf : k.childForm
  · simp [hcf, bind, Except.bind] at h
  · have hnl : (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
        "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).length =
        (if observe then 10 else 5) := by cases observe <;> rfl
    have hne : (args.length != (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
        "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).length + k.tuple.length) = true := by
      rw [hnl]; exact bne_iff_ne.mpr omitted
    simp [hcf, hne, bind, Except.bind, pure, Except.pure] at h

/-! ### Fixed-length proper-list witnesses (`IsListN`) and `@CORE` adapters -/

def IsListN (n : Nat) (v : Val) : Prop :=
  v.toList.length = n ∧ Val.ofList v.toList = v

def kidsOfVal (n : Nat) (v : Val) : Fin n → Val :=
  fun i => Native.nth (.int i.val) v

theorem isListN_ofList {n : Nat} (xs : List Val) (h : xs.length = n) :
    IsListN n (Val.ofList xs) :=
  ⟨by simp [toList_ofList', h], by simp [toList_ofList']⟩

theorem isListN_tupleImage {n : Nat} (kids : Fin n → Val) :
    IsListN n (tupleImage kids) :=
  isListN_ofList (List.ofFn kids) List.length_ofFn

theorem isListN_nil : IsListN 0 Val.nil := ⟨rfl, rfl⟩

theorem isListN_cons {n : Nat} (a d : Val) (hd : IsListN n d) :
    IsListN (n + 1) (.cons a d) := by
  refine ⟨by simp [Val.toList, hd.1], ?_⟩
  simp [Val.toList, Val.ofList, hd.2]

theorem isListN_ite {n : Nat} (c : Prop) [Decidable c] (a b : Val)
    (ha : c → IsListN n a) (hb : ¬c → IsListN n b) :
    IsListN n (if c then a else b) := by
  by_cases hc : c
  · simpa [hc] using ha hc
  · simpa [hc] using hb hc

theorem isListN_updateNth {n : Nat} (idx : Nat) (x v : Val) (hi : idx < n) (hv : IsListN n v) :
    IsListN n (Native.updateNth (.int idx) x v) := by
  have hl : idx < v.toList.length := by have := hv.1; omega
  conv => arg 2; rw [← hv.2]
  simp only [Native.updateNth, Val.nfix, Val.toInt, Int.toNat_natCast]
  rw [updateNthN_ofList v.toList idx x hl]
  exact isListN_ofList _ (by simp [hv.1])

theorem ofFn_kidsOfVal {n : Nat} (v : Val) (hv : IsListN n v) :
    List.ofFn (kidsOfVal n v) = v.toList := by
  apply List.ext_getElem
  · simp [hv.1]
  · intro i hi1 hi2
    rw [List.getElem_ofFn]
    simp only [kidsOfVal]
    conv => lhs; arg 2; rw [← hv.2]
    simpa [Native.nth, Val.nfix, Val.toInt, Int.toNat_natCast] using nthN_ofList v.toList i hi2

theorem tupleImage_kidsOfVal {n : Nat} (v : Val) (hv : IsListN n v) :
    tupleImage (kidsOfVal n v) = v := by
  simp [tupleImage, ofFn_kidsOfVal v hv, hv.2]

theorem toList_eq_map_nth {m : Nat} (v : Val) (hv : IsListN m v) :
    v.toList = (List.range m).map (fun (j : Nat) => Native.nth (.int j) v) := by
  apply List.ext_getElem
  · simp [hv.1]
  · intro j hj1 hj2
    simp only [List.getElem_map, List.getElem_range]
    conv => rhs; arg 2; rw [← hv.2]
    simp only [Native.nth, Val.nfix, Val.toInt, Int.toNat_natCast]
    exact (nthN_ofList v.toList j hj1).symm

theorem nth_zero_eq_car (v : Val) : Native.nth (.int 0) v = v.car := by
  cases v <;> rfl

theorem nth_succ_eq_cdr (k : Nat) (v : Val) :
    Native.nth (.int (k + 1 : Nat)) v = Native.nth (.int k) v.cdr := by
  cases v with
  | cons a d => simp [Native.nth, Native.nthN, Val.nfix, Val.toInt, Int.toNat_natCast, Val.cdr]
  | _ => simp [Native.nth, Native.nthN, Val.nfix, Val.toInt, Int.toNat_natCast, Val.cdr, nthN_atom k Val.nil rfl]

def keyOrOwner (w : World) (k : Kind) (st : St) (fm : String) (keys : List (String × Expr)) :
    Except String Val :=
  match keys.find? (·.1 == ":" ++ fm) with
  | some (_, e) => ev w k st e
  | none =>
    if fm == "OKIND" then var st "KIND"
    else if fm == "OSLOT" then var st "ID"
    else if fm == "OGEN" then var st "ROW-GENERATION"
    else throw s!"no argument for the formal {fm}"

/-- Value-level `actuals` for `@CORE` operations, placing `coreVal` directly at `some "FN2-CORE"`. -/
def coreActuals (w : World) (k : Kind) (st : St) (coreVal : Val) :
    List String → List (Option String) → List Expr → List (String × Expr) → Except String (List Val)
  | [], _, pos, _ => if pos.isEmpty then .ok [] else .error "too many arguments"
  | _ :: fs, some s :: ss, pos, keys => do
    let v ← if s == "FN2-CORE" then pure coreVal else stobj st s
    let rest ← coreActuals w k st coreVal fs ss pos keys
    pure (v :: rest)
  | fm :: fs, none :: ss, pos, keys =>
    match pos with
    | p :: ps => do
      let v ← ev w k st p
      let rest ← coreActuals w k st coreVal fs ss ps keys
      pure (v :: rest)
    | [] => do
      let v ← keyOrOwner w k st fm keys
      let rest ← coreActuals w k st coreVal fs ss [] keys
      pure (v :: rest)
  | _ :: _, [], _, _ => .error "stobjs-in shorter than formals"

theorem actuals_append_tuple (w : World) (k : Kind) (st : St)
    (tuple fs : List String) (ss : List (Option String))
    (pos : List Expr) (keys : List (String × Expr)) (ts rest : List Val)
    (hts : tuple.mapM (stobj st) = .ok ts)
    (hrest : actuals w k st fs ss pos keys = .ok rest) :
    actuals w k st (tuple ++ fs) (tuple.map some ++ ss) pos keys = .ok (ts ++ rest) := by
  induction tuple generalizing ts with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hts
    subst hts; simpa using hrest
  | cons t tuple ih =>
    simp only [List.mapM_cons] at hts
    obtain ⟨tv, htv, htr⟩ := bind_ok' hts
    obtain ⟨ts', hts', heq⟩ := bind_ok' htr
    simp only [pure, Except.pure, Except.ok.injEq] at heq; subst heq
    simp only [List.cons_append, List.map_cons, actuals, htv, except_ok_bind,
      ih ts' hts', pure, Except.pure]

theorem actuals_collapse_core {n : Nat} (w : World) (tuple : List String) (k : Kind)
    (kids : Fin n → Val) (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int)
    (formals : List String) (coreIn : List (Option String))
    (pos : List Expr) (keys : List (String × Expr)) (cargs : List Val)
    (hlen : tuple.length = n) (hnd : nodupB tuple = true) (hfin : formals.length = coreIn.length)
    (hc : coreActuals (coreWorld w tuple) (coreKind k tuple)
      ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩
      (tupleImage kids) formals coreIn pos keys = .ok cargs) :
    ∃ args,
      actuals (coreWorld w tuple) (coreKind k tuple)
        ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩
        (expandF tuple formals coreIn) (expandS tuple coreIn) pos keys = .ok args ∧
      collapse tuple.length coreIn args = some cargs := by
  let st : St := ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩
  have hmap : tuple.mapM (stobj st) = .ok (List.ofFn kids) := by
    apply mapM_stobj_zip tuple (List.ofFn kids) st (by simp [hlen]) hnd
    intro c v hf; simp [st, stobj, tupleStobjs, hf]
  induction formals generalizing coreIn pos cargs with
  | nil =>
    cases coreIn with
    | nil =>
      simp only [coreActuals] at hc
      by_cases hp : pos.isEmpty = true
      · simp only [hp, ↓reduceIte, Except.ok.injEq] at hc; subst hc
        exact ⟨[], by simp [expandF, expandS, actuals, hp], rfl⟩
      · simp [hp] at hc
    | cons _ _ => simp at hfin
  | cons fm fs ih =>
    cases coreIn with
    | nil => simp at hfin
    | cons s ss =>
      have hfin' : fs.length = ss.length := by simpa using hfin
      cases s with
      | none =>
        have hexF : expandF tuple (fm :: fs) (none :: ss) = fm :: expandF tuple fs ss := rfl
        have hexS : expandS tuple (none :: ss) = none :: expandS tuple ss := rfl
        cases pos with
        | cons p ps =>
          simp only [coreActuals] at hc
          obtain ⟨v, hv, hr⟩ := bind_ok' hc
          obtain ⟨rest, hrest, heq⟩ := bind_ok' hr
          simp only [pure, Except.pure, Except.ok.injEq] at heq; subst heq
          obtain ⟨args', ha', hcol'⟩ := ih ss ps rest hfin' hrest
          refine ⟨v :: args', ?_, ?_⟩
          · rw [hexF, hexS]
            simp only [actuals, hv, except_ok_bind, ha', pure, Except.pure]
          · simp [collapse, hcol']
        | nil =>
          simp only [coreActuals] at hc
          obtain ⟨v, hv, hr⟩ := bind_ok' hc
          obtain ⟨rest, hrest, heq⟩ := bind_ok' hr
          simp only [pure, Except.pure, Except.ok.injEq] at heq; subst heq
          obtain ⟨args', ha', hcol'⟩ := ih ss [] rest hfin' hrest
          refine ⟨v :: args', ?_, ?_⟩
          · rw [hexF, hexS]
            have hact0 : actuals (coreWorld w tuple) (coreKind k tuple) st
                (fm :: expandF tuple fs ss) (none :: expandS tuple ss) [] keys =
                (do let y ← keyOrOwner (coreWorld w tuple) (coreKind k tuple) st fm keys
                    let rest ← actuals (coreWorld w tuple) (coreKind k tuple) st (expandF tuple fs ss) (expandS tuple ss) [] keys
                    pure (y :: rest)) := by
              conv => lhs; unfold actuals
              unfold keyOrOwner
              cases keys.find? (·.1 == ":" ++ fm) with
              | some kv => obtain ⟨_, _⟩ := kv; rfl
              | none =>
                cases (fm == "OKIND") <;> cases (fm == "OSLOT") <;> cases (fm == "OGEN") <;>
                  simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            rw [hact0, hv, except_ok_bind, ha']
            rfl
          · simp [collapse, hcol']
      | some sn =>
        by_cases hsn : sn = "FN2-CORE"
        · subst hsn
          simp only [coreActuals, beq_self_eq_true, ↓reduceIte, except_pure_bind] at hc
          obtain ⟨rest, hrest, heq⟩ := bind_ok' hc
          simp only [pure, Except.pure, Except.ok.injEq] at heq; subst heq
          obtain ⟨args', ha', hcol'⟩ := ih ss pos rest hfin' hrest
          refine ⟨List.ofFn kids ++ args', ?_, ?_⟩
          · simp only [expandF, expandS, List.zip_cons_cons, List.flatMap_cons, beq_self_eq_true,
              ↓reduceIte]
            exact actuals_append_tuple _ _ st tuple _ _ pos keys _ _ hmap ha'
          · have hlt : ¬((List.ofFn kids ++ args').length < tuple.length) := by simp [hlen]
            have htk : (List.ofFn kids ++ args').take tuple.length = List.ofFn kids := by
              rw [hlen]; simp
            have hdr : (List.ofFn kids ++ args').drop tuple.length = args' := by
              rw [hlen]; simp
            unfold collapse
            rw [if_neg hlt]
            simp [htk, hdr, hcol', tupleImage]
        · have hsnf : (sn == "FN2-CORE") = false := beq_eq_false_iff_ne.mpr hsn
          have hsnf' : (some sn == some "FN2-CORE") = false := by simp [hsn]
          have hexF : expandF tuple (fm :: fs) (some sn :: ss) = fm :: expandF tuple fs ss := by
            simp [expandF, hsn]
          have hexS : expandS tuple (some sn :: ss) = some sn :: expandS tuple ss := by
            simp [expandS, hsn]
          simp only [coreActuals, hsnf, Bool.false_eq_true, ↓reduceIte] at hc
          obtain ⟨v, hv, hr⟩ := bind_ok' hc
          obtain ⟨rest, hrest, heq⟩ := bind_ok' hr
          simp only [pure, Except.pure, Except.ok.injEq] at heq; subst heq
          obtain ⟨args', ha', hcol'⟩ := ih ss pos rest hfin' hrest
          refine ⟨v :: args', ?_, ?_⟩
          · rw [hexF, hexS]
            simp only [actuals, hv, except_ok_bind, ha', pure, Except.pure]
          · simp [collapse, hsnf', hcol']

def bindVarsList (vars : List String) (vals : List Val) (env : Env) : Env :=
  match vars, vals with
  | [], _ | _, [] => env
  | v :: vs, x :: xs => bindVarsList vs xs ((v, x) :: env)

theorem bindVarsList_nil_right (vars : List String) (env : Env) :
    bindVarsList vars [] env = env := by
  cases vars <;> rfl

theorem bindVarsList_nil_left (vals : List Val) (env : Env) :
    bindVarsList [] vals env = env := by
  cases vals <;> rfl

theorem bindOuts_go_none (st : St) (k : Nat) (os : List (Option String))
    (vars : List String) (vals rs : List Val) (hlen : vals.length = k) :
    bindOuts.go st (List.replicate k none ++ os) vars (vals ++ rs) =
      bindOuts.go { st with vars := bindVarsList vars vals st.vars } os (vars.drop k) rs := by
  induction vals generalizing st k vars with
  | nil =>
    subst hlen
    simp [bindVarsList_nil_right]
  | cons x xs ih =>
    cases k with
    | zero => simp at hlen
    | succ k =>
      cases vars with
      | nil =>
        simp only [List.replicate_succ, List.cons_append, bindOuts.go, bindVarsList_nil_left, List.drop_nil]
        simpa [bindVarsList_nil_left, List.drop_nil] using ih st k [] (by simpa using hlen)
      | cons v vs =>
        simp only [List.replicate_succ, List.cons_append, bindOuts.go, bindVarsList, List.drop_succ_cons]
        exact ih { st with vars := (v, x) :: st.vars } k vs (by simpa using hlen)

theorem bindOuts_go_zip_prefix (pre suf : List String) (vpre vs vsuf : List Val)
    (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int) (bvars : List String)
    (hp : pre.length = vpre.length) (hs0 : suf.length = vs.length) (hs1 : suf.length = vsuf.length)
    (hnd : nodupB (pre ++ suf) = true) :
    bindOuts.go ⟨pre.zip vpre ++ suf.zip vs, vars, pending, next, nextDone, woken, loopWork⟩
      (suf.map some) bvars vsuf =
      .ok ⟨pre.zip vpre ++ suf.zip vsuf, vars, pending, next, nextDone, woken, loopWork⟩ := by
  induction suf generalizing pre vpre vs vsuf with
  | nil =>
    cases vs with
    | cons _ _ => simp at hs0
    | nil =>
      cases vsuf with
      | cons _ _ => simp at hs1
      | nil => rfl
  | cons k ks ih =>
    cases vs with
    | nil => simp at hs0
    | cons v0 vs0 =>
      cases vsuf with
      | nil => simp at hs1
      | cons v' vsuf' =>
        obtain ⟨_, hnd_kks, hdisj⟩ := nodupB_append hnd
        simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at hnd_kks
        have hpre_k : pre.contains k = false := by
          cases hc : pre.contains k
          · rfl
          · have hm : k ∈ pre := List.contains_iff_mem.mp hc
            have := hdisj k hm
            simp at this
        have hset : setStobj ⟨pre.zip vpre ++ (k :: ks).zip (v0 :: vs0), vars, pending, next, nextDone, woken, loopWork⟩ k v' =
            ⟨(pre ++ [k]).zip (vpre ++ [v']) ++ ks.zip vs0, vars, pending, next, nextDone, woken, loopWork⟩ := by
          simp only [setStobj, List.map_append, map_zip_not_mem pre vpre k v' hpre_k,
            List.zip_cons_cons, List.map_cons, beq_self_eq_true, ↓reduceIte,
            map_zip_not_mem ks vs0 k v' hnd_kks.1, List.zip_append hp, List.append_assoc]
          rfl
        simp only [List.map_cons, bindOuts.go, hset]
        have hnd' : nodupB ((pre ++ [k]) ++ ks) = true := by simpa [List.append_assoc] using hnd
        have hex := ih (pre ++ [k]) (vpre ++ [v']) vs0 vsuf' (by simp [hp]) (by simpa using hs0) (by simpa using hs1) hnd'
        simpa [List.zip_append hp, List.append_assoc] using hex

theorem bindOuts_go_tuple {n : Nat} (tuple : List String) (kids kids' : Fin n → Val)
    (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int) (bvars : List String)
    (hlen : tuple.length = n) (hnd : nodupB tuple = true) :
    bindOuts.go ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩
      (tuple.map some) bvars (List.ofFn kids') =
      .ok ⟨tupleStobjs tuple kids', vars, pending, next, nextDone, woken, loopWork⟩ := by
  simpa [tupleStobjs] using
    bindOuts_go_zip_prefix [] tuple [] (List.ofFn kids) (List.ofFn kids')
      vars pending next nextDone woken loopWork bvars rfl (by simp [hlen]) (by simp [hlen]) (by simpa using hnd)

theorem spread_replicate_core {n : Nat} (k : Nat) (hk : 0 < k) (res : Val)
    (hres : IsListN (k + 1) res) (hcore : IsListN n (Native.nth (.int k) res)) :
    spread (List.replicate k none ++ [some "FN2-CORE"]) res =
      Val.ofList ((List.range k).map (fun (j : Nat) => Native.nth (.int j) res) ++
        List.ofFn (kidsOfVal n (Native.nth (.int k) res))) := by
  have htl : res.toList = (List.range k).map (fun (j : Nat) => Native.nth (.int j) res) ++ [Native.nth (.int k) res] := by
    rw [toList_eq_map_nth res hres, List.range_succ, List.map_append, List.map_singleton]
  have hne1 : ∀ x, List.replicate k none ++ [some "FN2-CORE"] ≠ [x] := by
    intro x h; have := congrArg List.length h; simp at this; omega
  cases hs : List.replicate k none ++ [some "FN2-CORE"] with
  | nil => simp at hs
  | cons a rest =>
    cases rest with
    | nil => exfalso; exact hne1 a hs
    | cons b rest' =>
      rw [← hs]
      unfold spread
      split
      · rename_i x hx; exfalso; exact hne1 x hx
      · rw [htl, ofFn_kidsOfVal _ hcore]
        have hlen1 : (List.replicate k (none : Option String)).length =
            ((List.range k).map (fun (j : Nat) => Native.nth (.int j) res)).length := by simp
        rw [List.zip_append hlen1, List.flatMap_append]
        have hleft : ∀ (m : Nat) (xs : List Val), xs.length = m →
            ((List.replicate m (none : Option String)).zip xs).flatMap
              (fun (s, r) => if s == some "FN2-CORE" then r.toList else [r]) = xs := by
          intro m xs hxm
          induction xs generalizing m with
          | nil => subst hxm; simp
          | cons y ys ihy =>
            cases m with
            | zero => simp at hxm
            | succ m =>
              simp only [List.replicate_succ, List.zip_cons_cons, List.flatMap_cons]
              exact congrArg (y :: ·) (ihy m (by simpa using hxm))
        rw [hleft k _ (by simp)]
        simp

theorem bindOuts_spread_core_multi {n : Nat} (tuple : List String)
    (kids : Fin n → Val) (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int)
    (k : Nat) (hk : 0 < k) (hk2 : 2 ≤ tuple.length) (bvars : List String) (res : Val)
    (hlen : tuple.length = n) (hnd : nodupB tuple = true)
    (hres : IsListN (k + 1) res) (hcore : IsListN n (Native.nth (.int k) res)) :
    bindOuts ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩
      (expandS tuple (List.replicate k none ++ [some "FN2-CORE"])) bvars
      (spread (List.replicate k none ++ [some "FN2-CORE"]) res) =
    .ok ⟨tupleStobjs tuple (kidsOfVal n (Native.nth (.int k) res)),
      bindVarsList bvars ((List.range k).map (fun (j : Nat) => Native.nth (.int j) res)) vars,
      pending, next, nextDone, woken, loopWork⟩ := by
  have hexp : expandS tuple (List.replicate k none ++ [some "FN2-CORE"]) =
      List.replicate k none ++ tuple.map some := by
    simp only [expandS, List.flatMap_append, List.flatMap_singleton, beq_self_eq_true, ↓reduceIte]
    congr 1
    clear hk hres hcore
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.replicate_succ, List.flatMap_cons]
      exact congrArg (none :: ·) ih
  rw [hexp, spread_replicate_core k hk res hres hcore]
  have hge2 : 2 ≤ (List.replicate k none ++ tuple.map some).length := by simp; omega
  unfold bindOuts
  split
  · rename_i s hs; have := congrArg List.length hs; simp at this; omega
  · rename_i hs; have := congrArg List.length hs; simp at this; omega
  · rw [toList_ofList', bindOuts_go_none _ k _ bvars _ _ (by simp),
      bindOuts_go_tuple tuple kids _ _ pending next nextDone woken loopWork _ hlen hnd]

theorem bindOuts_spread_core_single {n : Nat} (tuple : List String)
    (kids : Fin n → Val) (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int)
    (hk2 : 2 ≤ tuple.length) (bvars : List String) (res : Val)
    (hlen : tuple.length = n) (hnd : nodupB tuple = true)
    (hcore : IsListN n res) :
    bindOuts ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩
      (expandS tuple [some "FN2-CORE"]) bvars (spread [some "FN2-CORE"] res) =
    .ok ⟨tupleStobjs tuple (kidsOfVal n res), vars, pending, next, nextDone, woken, loopWork⟩ := by
  have hexp : expandS tuple [some "FN2-CORE"] = tuple.map some := by simp [expandS]
  have hsp : spread [some "FN2-CORE"] res = res := rfl
  rw [hexp, hsp]
  unfold bindOuts
  split
  · rename_i s hs; have := congrArg List.length hs; simp at this; omega
  · rename_i hs; have := congrArg List.length hs; simp at this; omega
  · rw [← ofFn_kidsOfVal res hcore]
    exact bindOuts_go_tuple tuple kids (kidsOfVal n res) vars pending next nextDone woken loopWork bvars hlen hnd

/-- Call a `@CORE` operation end-to-end (`callOp` in `coreWorld`). -/
theorem callOp_core_adapter {n : Nat} (w : World) (tuple : List String) (k : Kind)
    (kids : Fin n → Val) (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nextDone woken : Bool) (loopWork : Int × Int × Int)
    (c : Call) (o : Op) (keys : List (String × Expr)) (cargs : List Val) (res : Val)
    (hlen : tuple.length = n) (hnd : nodupB tuple = true)
    (hfind : w.ops.find? (·.name == c.op) = some o)
    (hncal : o.callee = none) (hcf_ne : o.coreFormals.isEmpty = false)
    (hfin : o.coreFormals.length = o.coreIn.length)
    (hnat : nativeCallNames.contains (adapterName o.name) = false)
    (hend : (adapterName o.name).endsWith "@CORE" = true)
    (hfpad : w.ops.find? (fun o' => adapterName o'.name == adapterName o.name) = some o)
    (hkeys : expandOwner (coreWorld w tuple) (coreKind k tuple) c.keys = .ok keys)
    (hact : coreActuals (coreWorld w tuple) (coreKind k tuple)
      ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩
      (tupleImage kids) o.coreFormals o.coreIn c.args keys = .ok cargs)
    (hfns : w.fns o.name cargs = some res) :
    callOp (coreWorld w tuple) (coreKind k tuple)
      ⟨tupleStobjs tuple kids, vars, pending, next, nextDone, woken, loopWork⟩ c =
      .ok (coreOp tuple o, spread o.coreOut res) := by
  have hfind_core : findOp (coreWorld w tuple) c.op = .ok (coreOp tuple o) := by
    unfold findOp coreWorld
    have hmap : ∀ (os : List Op), os.find? (·.name == c.op) = some o →
        (os.map (coreOp tuple)).find? (·.name == c.op) = some (coreOp tuple o) := by
      intro os hos
      induction os with
      | nil => simp at hos
      | cons x xs ih =>
        have hname : (coreOp tuple x).name = x.name := by
          unfold coreOp; cases x.callee <;> simp; split <;> rfl
        simp only [List.find?_cons, List.map_cons, hname] at hos ⊢
        split at hos
        · simp only [Option.some.injEq] at hos; subst hos; rfl
        · exact ih hos
    rw [hmap w.ops hfind]
  have hcop : coreOp tuple o =
      { o with callee := some (adapterName o.name),
               formals := expandF tuple o.coreFormals o.coreIn,
               stobjsIn := expandS tuple o.coreIn,
               stobjsOut := expandS tuple o.coreOut } := by
    simp [coreOp, hncal, hcf_ne]
  obtain ⟨args, hargs, hcol⟩ :=
    actuals_collapse_core w tuple k kids vars pending next nextDone woken loopWork
      o.coreFormals o.coreIn c.args keys cargs hlen hnd hfin hact
  have hcfns : (coreWorld w tuple).fns (adapterName o.name) args = some (spread o.coreOut res) := by
    simp [coreWorld, coreFns, hend, hfpad, hcol, hfns]
  unfold callOp
  rw [hfind_core, hcop]
  simp only [except_ok_bind, hkeys, hargs, callFn_of_fns _ _ _ _ hnat hcfns, except_pure_bind]
  rw [← hcop]
  rfl

/-! ### Reflected column-write canonicalizer -/

def fieldWrite (colIdx : Nat) (slot v st : Val) : Val :=
  Native.updateNth (.int colIdx) (Native.updateNth slot v (Native.nth (.int colIdx) st)) st

def applyFieldWrites (slot st : Val) : List (Nat × Val) → Val
  | [] => st
  | (c, v) :: rest => applyFieldWrites slot (fieldWrite c slot v st) rest

def insFieldWrite (c : Nat) (v : Val) : List (Nat × Val) → List (Nat × Val)
  | [] => [(c, v)]
  | (c', v') :: rest =>
    if c < c' then (c, v) :: (c', v') :: rest
    else if c == c' then (c', v') :: rest
    else (c', v') :: insFieldWrite c v rest

def sortFieldWrites : List (Nat × Val) → List (Nat × Val)
  | [] => []
  | (c, v) :: rest => insFieldWrite c v (sortFieldWrites rest)

theorem updateNthN_idem (k : Nat) (v1 v2 l : Val) :
    Native.updateNthN k v2 (Native.updateNthN k v1 l) = Native.updateNthN k v2 l := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => simp [Native.updateNthN, Val.car, Val.cdr, ih]

theorem updateNth_idem (s v1 v2 l : Val) :
    Native.updateNth s v2 (Native.updateNth s v1 l) = Native.updateNth s v2 l :=
  updateNthN_idem s.nfix v1 v2 l

theorem fieldWrite_idem (c : Nat) (slot v1 v2 st : Val) :
    fieldWrite c slot v2 (fieldWrite c slot v1 st) = fieldWrite c slot v2 st := by
  simp only [fieldWrite, nth_updateNth_same, updateNth_idem]

theorem fieldWrite_commute (i j : Nat) (slot v w st : Val) (h : i ≠ j) :
    fieldWrite i slot v (fieldWrite j slot w st) =
      fieldWrite j slot w (fieldWrite i slot v st) :=
  updateNth_array_commute i j slot v w st h

theorem applyFieldWrites_ins (c : Nat) (v slot st : Val) (ys : List (Nat × Val)) :
    applyFieldWrites slot st (insFieldWrite c v ys) =
      applyFieldWrites slot (fieldWrite c slot v st) ys := by
  induction ys generalizing st with
  | nil => rfl
  | cons p ys ih =>
    obtain ⟨c', v'⟩ := p
    simp only [insFieldWrite]
    by_cases hlt : c < c'
    · simp [hlt, applyFieldWrites]
    · simp only [hlt, ↓reduceIte]
      by_cases heq : (c == c') = true
      · have hc : c = c' := beq_iff_eq.mp heq
        subst hc
        simp [applyFieldWrites, fieldWrite_idem]
      · have hne : c ≠ c' := fun h => heq (beq_iff_eq.mpr h)
        have heqf : (c == c') = false := Bool.eq_false_iff.mpr heq
        simp only [heqf, Bool.false_eq_true, ↓reduceIte, applyFieldWrites]
        rw [ih, fieldWrite_commute c c' slot v v' st hne]

theorem applyFieldWrites_sort (slot st : Val) (ws : List (Nat × Val)) :
    applyFieldWrites slot st (sortFieldWrites ws) = applyFieldWrites slot st ws := by
  induction ws generalizing st with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨c, v⟩ := p
    simp only [sortFieldWrites, applyFieldWrites]
    rw [applyFieldWrites_ins, ih]

/-! ### Unified `put` and `flush` combinators -/

theorem put_eq_ite (w : World) (f : Frame) (st : St) (pairs : List (String × Val))
    (slot id table dir control rows drows table' dir' reason stopped : Val) (cond : Bool)
    (hslot : var st "SLOT" = .ok slot) (hid : var st "ID" = .ok id)
    (ht : stobj st f.kind.name = .ok table) (hd : stobj st "FN2-MACHINES" = .ok dir)
    (hc : stobj st "FN2-CONTROL" = .ok control)
    (hrows : callFn w (f.kind.name ++ "-ROWS") [table] = .ok rows)
    (hdrows : callFn w "FN2-MACHINES-ROWS" [dir] = .ok drows)
    (hcond : (natLt slot rows && ((pairs.filter fun p => directoryFields.contains p.1).isEmpty ||
        natLt id drows) && pairs.all fun (n, v) => match f.kind.columns.find? (·.1 == n) with
          | some (_, ty) => ty.fits v
          | none => false) = cond)
    (htab : (pairs.filter fun p => !directoryFields.contains p.1).foldlM
        (fun t (n, v) => callFn w (f.kind.name ++ "-SET-" ++ n) [slot, v, t]) table = .ok table')
    (hdir : (pairs.filter fun p => directoryFields.contains p.1).foldlM
        (fun d (n, v) => callFn w ("FN2-MACHINES-SET-" ++ n) [id, v, d]) dir = .ok dir')
    (hreason : const w "*FN2-STOP-REASON-MACHINE-WRITE*" = .ok reason)
    (hstop : callFn w "FN2-CONTROL-RECORD-STOP" [reason, control] = .ok stopped) :
    put w f st pairs = .ok (if cond then
      setStobj (setStobj st f.kind.name table') "FN2-MACHINES" dir'
    else
      setStobj st "FN2-CONTROL" stopped) := by
  by_cases hc_b : cond = true
  · rw [if_pos hc_b, put_pass w f st pairs slot id table dir control rows drows
      hslot hid ht hd hc hrows hdrows (hcond.trans hc_b)]
    have htab' : (pairs.filter fun p => !directoryFields.contains p.1).foldlM
        (fun t p => callFn w (f.kind.name ++ "-SET-" ++ p.1) [slot, p.2, t]) table = .ok table' := htab
    have hdir' : (pairs.filter fun p => directoryFields.contains p.1).foldlM
        (fun d p => callFn w ("FN2-MACHINES-SET-" ++ p.1) [id, p.2, d]) dir = .ok dir' := hdir
    rw [htab', except_ok_bind, hdir']
    rfl
  · have hcf : cond = false := Bool.eq_false_iff.mpr hc_b
    rw [if_neg hc_b, put_fail w f st pairs slot id table dir control rows drows
      hslot hid ht hd hc hrows hdrows (hcond.trans hcf)]
    simp [hreason, hstop]

theorem flush_nonempty_none (w : World) (f : Frame) (st : St)
    (pairs : List (String × Val)) (st' : St)
    (hn : st.next = none)
    (hpairs : (st.pending.mapM fun (n, e) => do pure (n, ← ev w f.kind st e)) = .ok pairs)
    (hne : pairs.isEmpty = false)
    (hput : put w f st pairs = .ok st') :
    flush w f st = .ok { st' with pending := [], next := none, nextDone := st.nextDone } := by
  unfold flush
  rw [hpairs, except_ok_bind]
  simp only [hn, hne, Bool.false_eq_true, ↓reduceIte, hput, except_ok_bind,
    Bool.or_false, Option.isSome_none, pure, Except.pure]

theorem flush_next_some (w : World) (f : Frame) (st : St)
    (nExpr : Expr) (nTerm : Term) (phVal : Val) (pairs : List (String × Val)) (st' : St)
    (hn : st.next = some nExpr)
    (hpairs : (st.pending.mapM fun (n, e) => do pure (n, ← ev w f.kind st e)) = .ok pairs)
    (hrn : readNext w f.kind nExpr = .ok nTerm)
    (hen : nTerm.eval w.fns (st.vars ++ st.stobjs) = .ok phVal)
    (hput : put w f st (pairs ++ [("PHASE", phVal)]) = .ok st') :
    flush w f st = .ok { st' with pending := [], next := none, nextDone := true } := by
  have hne : (pairs ++ [("PHASE", phVal)]).isEmpty = false := by cases pairs <;> rfl
  unfold flush
  rw [hpairs, except_ok_bind]
  simp only [hn, hrn, hen, except_ok_bind, hne, Bool.false_eq_true, ↓reduceIte,
    hput, Option.isSome_some, Bool.or_true, pure, Except.pure]

/-! ### Syntax-directed `Term.eval`, `ev`, and `evOpt` combinators -/

def evalArgs (fns : Fns) (env : Env) : List Term → Except String (List Val)
  | [] => .ok []
  | t :: ts => do
    let v ← Term.eval fns env t
    let vs ← evalArgs fns env ts
    pure (v :: vs)

theorem attach_mapM_eq_evalArgs (fns : Fns) (env : Env) (args : List Term) :
    args.attach.mapM (fun ⟨a, _⟩ => Term.eval fns env a) = evalArgs fns env args := by
  induction args with
  | nil => rfl
  | cons a as ih =>
    simp only [List.attach_cons, List.mapM_cons, evalArgs]
    rw [List.mapM_map]
    change (do let v ← Term.eval fns env a; let vs ← as.attach.mapM (fun (x : { x // x ∈ as }) => Term.eval fns env x.1); pure (v :: vs)) = _
    rw [ih]

theorem evalArgs_nil (fns : Fns) (env : Env) : evalArgs fns env [] = .ok [] := rfl

theorem evalArgs_cons (fns : Fns) (env : Env) (t : Term) (ts : List Term) (v : Val) (vs : List Val)
    (hv : Term.eval fns env t = .ok v) (hvs : evalArgs fns env ts = .ok vs) :
    evalArgs fns env (t :: ts) = .ok (v :: vs) := by
  simp [evalArgs, hv, hvs]

theorem eval_var (fns : Fns) (env : Env) (x : String) (v : Val) (h : env.get? x = some v) :
    Term.eval fns env (.var x) = .ok v := by
  simp [Term.eval, h]

theorem eval_var_st (w : World) (st : St) (x : String) (v : Val) (h : var st x = .ok v) :
    Term.eval w.fns (st.vars ++ st.stobjs) (.var x) = .ok v :=
  eval_var w.fns _ x v (var_env_bound st x v h)

theorem eval_quote (fns : Fns) (env : Env) (v : Val) :
    Term.eval fns env (.quote v) = .ok v := by
  simp [Term.eval]

theorem eval_if (fns : Fns) (env : Env) (c a b : Term) (vc va vb : Val)
    (hc : Term.eval fns env c = .ok vc)
    (ha : vc.truthy = true → Term.eval fns env a = .ok va)
    (hb : vc.truthy = false → Term.eval fns env b = .ok vb) :
    Term.eval fns env (.app "IF" [c, a, b]) = .ok (if vc.truthy then va else vb) := by
  rw [Term.eval.eq_3, hc, except_ok_bind]
  by_cases ht : vc.truthy = true
  · simp [ht, ha ht]
  · have htf : vc.truthy = false := Bool.eq_false_iff.mpr ht
    simp [htf, hb htf]

theorem eval_return_last (fns : Fns) (env : Env) (a b c : Term) (vc : Val)
    (hc : Term.eval fns env c = .ok vc) :
    Term.eval fns env (.app "RETURN-LAST" [a, b, c]) = .ok vc := by
  rw [Term.eval.eq_4]; exact hc

theorem eval_app_callFn (w : World) (env : Env) (f : String) (args : List Term)
    (vs : List Val) (v : Val)
    (hnif : f = "IF" → args.length ≠ 3)
    (hnrl : f = "RETURN-LAST" → args.length ≠ 3)
    (hargs : evalArgs w.fns env args = .ok vs)
    (hcall : callFn w f vs = .ok v) :
    Term.eval w.fns env (.app f args) = .ok v := by
  rw [Term.eval.eq_5 w.fns env f args
    (by intro c a b hf hargs'; exact hnif hf (by simp [hargs']))
    (by intro a b c hf hargs'; exact hnrl hf (by simp [hargs']))]
  rw [attach_mapM_eq_evalArgs, hargs, except_ok_bind]
  unfold callFn at hcall
  cases hn : nativeCall f vs with
  | some nv => rw [hn] at hcall; exact hcall
  | none =>
    rw [hn] at hcall
    cases hf : w.fns f vs with
    | some fv => rw [hf] at hcall; exact hcall
    | none => rw [hf] at hcall; cases hcall

theorem eval_lam (fns : Fns) (env : Env) (formals : List String) (body : Term)
    (actuals : List Term) (vs : List Val) (v : Val)
    (hargs : evalArgs fns env actuals = .ok vs)
    (hbody : Term.eval fns (formals.zip vs) body = .ok v) :
    Term.eval fns env (.lam formals body actuals) = .ok v := by
  rw [Term.eval.eq_6, attach_mapM_eq_evalArgs, hargs, except_ok_bind, hbody]

theorem ev_of_readExpr (w : World) (k : Kind) (st : St) (e : Expr) (t : Term) (v : Val)
    (hr : readExpr w k e = .ok t)
    (he : Term.eval w.fns (st.vars ++ st.stobjs) t = .ok v) :
    ev w k st e = .ok v := by
  simp [ev, hr, he]

theorem evOpt_none (w : World) (k : Kind) (st : St) (dflt : Val) :
    evOpt w k st none dflt = .ok dflt := rfl

theorem evOpt_some (w : World) (k : Kind) (st : St) (e : Expr) (dflt v : Val)
    (h : ev w k st e = .ok v) :
    evOpt w k st (some e) dflt = .ok v := h

/-! ### `runArm` and step/terminal combinators -/

theorem runArm_eq (w : World) (k : Kind) (a : Arm) (observe : Bool)
    (pre kids : List Val) (reads : Env) (d : ArmDecl) (fuel : Nat) (v : Val)
    (hcf : k.childForm = true)
    (hpre : pre.length = (if observe then 10 else 5))
    (hkids : kids.length = k.tuple.length)
    (hreads : rowReads w k (k.tuple.zip kids) (pre.headD Val.nil) ((pre.drop 1).headD Val.nil) = .ok reads)
    (hdecl : a.read = .ok d)
    (hrun : run w
      { kind := k, observe := observe, refusal := d.onRefusal,
        base := (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
          "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).zip pre }
      fuel { stobjs := k.tuple.zip kids,
             vars := reads ++ (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
               "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).zip pre }
      d.steps = .ok (.done v)) :
    runArm w k a observe (pre ++ kids) fuel = .ok v := by
  have hnl : (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
      "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).length = pre.length := by
    rw [hpre]; cases observe <;> rfl
  have hlen : ((pre ++ kids).length != (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
      "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).length + k.tuple.length) = false := by
    rw [List.length_append, hnl, hkids]; exact bne_self_eq_false _
  have htk : (pre ++ kids).take (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
      "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).length = pre := by
    rw [hnl]; simp
  have hdr : (pre ++ kids).drop (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
      "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).length = kids := by
    rw [hnl]; simp
  have hhd : (pre ++ kids).headD Val.nil = pre.headD Val.nil := by
    cases pre with
    | nil => cases observe <;> simp at hpre
    | cons _ _ => rfl
  have hhd1 : ((pre ++ kids).drop 1).headD Val.nil = (pre.drop 1).headD Val.nil := by
    cases pre with
    | nil => cases observe <;> simp at hpre
    | cons _ ps =>
      cases ps with
      | nil => cases observe <;> simp at hpre
      | cons _ _ => rfl
  unfold runArm
  simp only [hcf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlen, htk, hdr, hhd, hhd1,
    hreads, hdecl, except_ok_bind, hrun]
  rfl

theorem run_let (w : World) (f : Frame) (fuel : Nat) (st : St)
    (v : String) (e : Expr) (rest : List Step) (x : Val)
    (hev : ev w f.kind st e = .ok x) :
    run w f (fuel + 1) st (.let_ v e :: rest) =
      run w f fuel { st with vars := (v, x) :: st.vars } rest := by
  simp [run, hev]

theorem run_set (w : World) (f : Frame) (fuel : Nat) (st : St)
    (pairs : List (String × Expr)) (rest : List Step)
    (hdup : (pairs.any fun p => st.pending.any (·.1 == p.1)) = false) :
    run w f (fuel + 1) st (.set pairs :: rest) =
      run w f fuel { st with pending := st.pending ++ pairs } rest := by
  simp [run, pend, hdup]

theorem run_next (w : World) (f : Frame) (fuel : Nat) (st : St)
    (ph : Expr) (rest : List Step)
    (hn : st.next = none) (hnd : st.nextDone = false) :
    run w f (fuel + 1) st (.next ph :: rest) =
      run w f fuel { st with next := some ph } rest := by
  simp [run, hn, hnd]

theorem run_if (w : World) (f : Frame) (fuel : Nat) (st : St)
    (c : Expr) (a b rest : List Step) (vc : Val) (res : Res)
    (hc : ev w f.kind st c = .ok vc)
    (ha : vc.truthy = true → run w f fuel st a = .ok res)
    (hb : vc.truthy = false → run w f fuel st b = .ok res) :
    run w f (fuel + 1) st (.if_ c a b :: rest) = .ok res := by
  simp only [run, hc, except_ok_bind]
  by_cases ht : vc.truthy = true
  · simp [ht, ha ht]
  · have htf : vc.truthy = false := Bool.eq_false_iff.mpr ht
    simp [htf, hb htf]

theorem run_cond_cons (w : World) (f : Frame) (fuel : Nat) (st : St)
    (c : Expr) (steps : List Step) (more : List (Expr × List Step)) (rest : List Step)
    (vc : Val) (res : Res)
    (hc : ev w f.kind st c = .ok vc)
    (ha : vc.truthy = true → run w f fuel st steps = .ok res)
    (hb : vc.truthy = false → run w f (fuel + 1) st (.cond more :: rest) = .ok res) :
    run w f (fuel + 1) st (.cond ((c, steps) :: more) :: rest) = .ok res := by
  dsimp only [run, List.findM?]
  rw [hc, except_ok_bind, except_pure_bind]
  by_cases ht : vc.truthy = true
  · rw [ht]; simp only [except_pure_bind]; exact ha ht
  · have htf : vc.truthy = false := Bool.eq_false_iff.mpr ht
    rw [htf]
    have hb' := hb htf
    dsimp only [run] at hb'
    exact hb'

theorem run_case_step (w : World) (f : Frame) (fuel : Nat) (st : St)
    (key : Expr) (arms : List (Option (List Val) × List Step)) (rest : List Step) (kv : Val)
    (hk : ev w f.kind st key = .ok kv) :
    run w f (fuel + 1) st (.case_ key arms :: rest) =
      match arms.find? (fun (cs, _) => match cs with | some l => codeIn kv l | none => true) with
      | some (_, steps) => run w f fuel st steps
      | none => .error ":case without :otherwise" := by
  simp only [run, hk, except_ok_bind]
  rfl

theorem run_wakeRow (w : World) (f : Frame) (fuel : Nat) (st : St)
    (e : Expr) (rest : List Step) (v dir ctrl r : Val)
    (hw : st.woken = false)
    (hev : ev w f.kind st e = .ok v)
    (hd : stobj st "FN2-MACHINES" = .ok dir)
    (hc : stobj st "FN2-CONTROL" = .ok ctrl)
    (hcall : callFn w "FN2-MACHINES-WAKE-ROW" [v, dir, ctrl] = .ok r) :
    run w f (fuel + 1) st (.wakeRow e :: rest) =
      run w f fuel { (setStobj (setStobj st "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car)
        with woken := true } rest := by
  simp [run, hw, hev, hd, hc, hcall]

theorem run_charge (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (b s d r : Option Expr) (rest : List Step) (vb vs vd vr : Val)
    (hfl : flush w f st = .ok st')
    (hb : evOpt w f.kind st' b (.int 0) = .ok vb)
    (hs : evOpt w f.kind st' s (.int 0) = .ok vs)
    (hd : evOpt w f.kind st' d (.int 0) = .ok vd)
    (hr : evOpt w f.kind st' r Val.nil = .ok vr) :
    run w f (fuel + 1) st (.charge b s d r :: rest) = chargeResult f st' vb vs vd vr := by
  simp [run, hfl, hb, hs, hd, hr]

theorem run_idle (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (rest : List Step) (empty : Val)
    (hfl : flush w f st = .ok st')
    (he : const w "*FN2-WORK-EMPTY*" = .ok empty) :
    run w f (fuel + 1) st (.idle :: rest) = chargeResult f st' (.int 0) empty (.int 0) Val.nil := by
  simp [run, hfl, he]

theorem run_yield (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (rest : List Step) (empty : Val)
    (hfl : flush w f st = .ok st')
    (he : const w "*FN2-WORK-EMPTY*" = .ok empty) :
    run w f (fuel + 1) st (.yield :: rest) = chargeResult f st' (.int 0) empty (.int 0) Val.t := by
  simp [run, hfl, he]

theorem run_wait (w : World) (f : Frame) (fuel : Nat) (st stp st' : St)
    (b s : Option Expr) (rest : List Step) (wcomp mbox vb vs : Val)
    (hc : const w "*FN2-WAIT-COMPLETION*" = .ok wcomp)
    (hpend : pend st [("PENDING", Expr.q (.int 1)), ("WAIT-REASON", Expr.q wcomp)] = .ok stp)
    (hfl : flush w f stp = .ok st')
    (hm : const w "*FN2-WORK-MAILBOX*" = .ok mbox)
    (hb : evOpt w f.kind st' b (.int 0) = .ok vb)
    (hs : evOpt w f.kind st' s mbox = .ok vs) :
    run w f (fuel + 1) st (.wait b s :: rest) = chargeResult f st' vb vs (.int 1) Val.nil := by
  simp [run, hc, hpend, hfl, hm, hb, hs]

theorem run_halt (w : World) (f : Frame) (fuel : Nat) (st stp st' : St)
    (rest : List Step) (wnone mbox : Val)
    (hc : const w "*FN2-WAIT-NONE*" = .ok wnone)
    (hpend : pend st [("STOPPED", Expr.q (.int 1)), ("WAIT-REASON", Expr.q wnone)] = .ok stp)
    (hfl : flush w f stp = .ok st')
    (hm : const w "*FN2-WORK-MAILBOX*" = .ok mbox) :
    run w f (fuel + 1) st (.halt :: rest) = chargeResult f st' (.int 0) mbox (.int 0) Val.nil := by
  simp [run, hc, hpend, hfl, hm]

theorem run_stop_kind (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (reason : String) (steps : Option Expr) (rest : List Step)
    (idx : Nat) (kindVal ctrl stopped : Val)
    (hn : st.next = none)
    (hfl : flush w f st = .ok st')
    (hc : stobj st' "FN2-CONTROL" = .ok ctrl)
    (hi : f.kind.stops.idxOf? reason = some idx)
    (hk : var st' "KIND" = .ok kindVal)
    (hs : callFn w "FN2-CONTROL-RECORD-KIND-STOP" [kindVal, .int idx, ctrl] = .ok stopped) :
    run w f (fuel + 1) st (.stop reason steps :: rest) =
      stopEnd w f (setStobj st' "FN2-CONTROL" stopped) steps := by
  simp [run, hn, hfl, hc, hi, hk, hs]

theorem run_stop_global' (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (reason : String) (steps : Option Expr) (rest : List Step)
    (ctrl reasonCode stopped : Val)
    (hn : st.next = none)
    (hfl : flush w f st = .ok st')
    (hc : stobj st' "FN2-CONTROL" = .ok ctrl)
    (hi : f.kind.stops.idxOf? reason = none)
    (hr : const w ("*FN2-STOP-REASON-" ++ reason ++ "*") = .ok reasonCode)
    (hs : callFn w "FN2-CONTROL-RECORD-STOP" [reasonCode, ctrl] = .ok stopped) :
    run w f (fuel + 1) st (.stop reason steps :: rest) =
      stopEnd w f (setStobj st' "FN2-CONTROL" stopped) steps := by
  simp [run, hn, hfl, hc, hi, hr, hs]

theorem stopEnd_arm (w : World) (f : Frame) (st : St) (steps : Option Expr)
    (empty vs : Val) (ho : f.observe = false)
    (he : const w "*FN2-WORK-EMPTY*" = .ok empty)
    (hs : evOpt w f.kind st steps empty = .ok vs) :
    stopEnd w f st steps = chargeResult f st (.int 0) vs (.int 0) Val.nil := by
  simp [stopEnd, ho, he, hs]

theorem stopEnd_observe (w : World) (f : Frame) (st : St) (steps : Option Expr)
    (noneVal : Val) (ho : f.observe = true)
    (hn : const w "*FN2-NONE*" = .ok noneVal) :
    stopEnd w f st steps = wakeResult f st noneVal := by
  simp [stopEnd, ho, hn]

theorem run_wake (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (rest : List Step) (id : Val)
    (hw : st.woken = false)
    (hfl : flush w f st = .ok st')
    (hid : var st' "ID" = .ok id) :
    run w f (fuel + 1) st (.wake :: rest) = wakeResult f st' id := by
  simp [run, hw, hfl, hid]

theorem run_nowake (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (rest : List Step) (noneVal : Val)
    (hfl : flush w f st = .ok st')
    (hn : const w "*FN2-NONE*" = .ok noneVal) :
    run w f (fuel + 1) st (.nowake :: rest) = wakeResult f st' noneVal := by
  simp [run, hfl, hn]

theorem run_park_pool (w : World) (f : Frame) (fuel : Nat) (st stp st' : St)
    (cls : Expr) (kind : Option String) (steps : Option Expr) (keys : List (String × Expr))
    (rest : List Step) (mbox id dir ctrl r vs : Val)
    (hm : const w "*FN2-WORK-MAILBOX*" = .ok mbox)
    (hpend : pend st [("CURSOR", cls)] = .ok stp)
    (hfl : flush w f stp = .ok st')
    (hid : var st' "ID" = .ok id)
    (hd : stobj st' "FN2-MACHINES" = .ok dir)
    (hc : stobj st' "FN2-CONTROL" = .ok ctrl)
    (hcall : callFn w "FN2-MACHINES-PARK-POOL" [id, dir, ctrl] = .ok r)
    (hs : evOpt w f.kind (setStobj (setStobj st' "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car) steps mbox = .ok vs) :
    run w f (fuel + 1) st (.park "POOL" (some cls) kind steps keys :: rest) =
      chargeResult f (setStobj (setStobj st' "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car)
        (.int 0) vs (.int 0) Val.nil := by
  simp [run, hm, hpend, hfl, hid, hd, hc, hcall, hs]

theorem run_park_wait_col (w : World) (f : Frame) (fuel : Nat) (st stp st' : St)
    (wait : String) (arg : Option Expr) (kind : Option String) (steps : Option Expr)
    (keys : List (String × Expr)) (rest : List Step) (mbox wval vs : Val)
    (hnop : wait ≠ "OPERATION" ∧ wait ≠ "ADMISSION" ∧ wait ≠ "TAKEN" ∧ wait ≠ "POOL")
    (hw : w.waits.find? (·.kind == wait) = some ⟨wait, none⟩)
    (hm : const w "*FN2-WORK-MAILBOX*" = .ok mbox)
    (hc : const w ("*FN2-WAIT-" ++ wait ++ "*") = .ok wval)
    (hpend : pend st [("WAIT-REASON", Expr.q wval)] = .ok stp)
    (hfl : flush w f stp = .ok st')
    (hs : evOpt w f.kind st' steps mbox = .ok vs) :
    run w f (fuel + 1) st (.park wait arg kind steps keys :: rest) =
      chargeResult f st' (.int 0) vs (.int 0) Val.nil := by
  rcases hnop with ⟨h1, h2, h3, h4⟩
  dsimp only [run]
  rw [hm, except_ok_bind]
  split
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · simp [hw, hc, hpend, hfl, hs]

theorem run_park_viaOp (w : World) (f : Frame) (fuel : Nat) (st st' stb : St)
    (wait : String) (arg : Option Expr) (kind : Option String) (steps : Option Expr)
    (keys : List (String × Expr)) (rest : List Step)
    (opName : String) (opArgs : List Expr) (o : Op) (r mbox vs : Val)
    (hm : const w "*FN2-WORK-MAILBOX*" = .ok mbox)
    (hroute : (wait = "OPERATION" ∧ opName = "FN2-MACHINE-PARK" ∧ opArgs = [.sym "ID"]) ∨
              (wait = "ADMISSION" ∧ opName = "FN2-MACHINE-PARK-ADMISSION" ∧ opArgs = .sym "ID" :: arg.toList) ∨
              (wait = "TAKEN" ∧ opName = "FN2-MACHINE-PARK-TAKEN-" ++ kind.getD "" ∧ opArgs = [.sym "ID"]) ∨
              (wait ≠ "OPERATION" ∧ wait ≠ "ADMISSION" ∧ wait ≠ "TAKEN" ∧ wait ≠ "POOL" ∧
               w.waits.find? (·.kind == wait) = some ⟨wait, some opName⟩ ∧ opArgs = [.sym "ID"]))
    (hfl : flush w f st = .ok st')
    (hcall : callOp w f.kind st' ⟨opName, opArgs, keys⟩ = .ok (o, r))
    (hbind : bindOuts st' o.stobjsOut [] r = .ok stb)
    (hs : evOpt w f.kind stb steps mbox = .ok vs) :
    run w f (fuel + 1) st (.park wait arg kind steps keys :: rest) =
      chargeResult f stb (.int 0) vs (.int 0) Val.nil := by
  rcases hroute with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h1, h2, h3, h4, hw, rfl⟩
  · simp [run, hm, hfl, hcall, hbind, hs]
  · simp only [run, hm, except_ok_bind, List.singleton_append, hfl, hcall, hbind, hs]
  · simp [run, hm, hfl, hcall, hbind, hs]
  · dsimp only [run]
    rw [hm, except_ok_bind]
    split
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · simp [hw, hfl, hcall, hbind, hs]

theorem run_do_none (w : World) (f : Frame) (fuel : Nat) (st st' stb : St)
    (vars : List String) (c : Call) (ag : Bool) (acc : List Val) (else_ : List Expr)
    (cases : List (Option (List Val) × List Step)) (rest : List Step)
    (op : Op) (r : Val)
    (hfl : flush w f st = .ok st')
    (hfind : findOp w c.op = .ok op)
    (hcall : callOp w f.kind st' c = .ok (op, r))
    (hbind : bindOuts st' op.stobjsOut vars r = .ok stb)
    (hans : op.answers = .none) :
    run w f (fuel + 1) st (.do_ vars c ag acc none else_ cases :: rest) =
      run w f fuel stb rest := by
  simp [run, hfl, hfind, hcall, hbind, hans]

theorem run_do_answers (w : World) (f : Frame) (fuel : Nat) (st st' stb : St)
    (v : String) (vs : List String) (c : Call) (ag : Bool) (acc : List Val)
    (else_ : List Expr) (cases : List (Option (List Val) × List Step)) (rest : List Step)
    (op : Op) (r code : Val)
    (hfl : flush w f st = .ok st')
    (hfind : findOp w c.op = .ok op)
    (hcall : callOp w f.kind st' c = .ok (op, r))
    (hbind : bindOuts st' op.stobjsOut (v :: vs) r = .ok stb)
    (hnans : op.answers ≠ .none)
    (hcode : var stb v = .ok code) :
    run w f (fuel + 1) st (.do_ (v :: vs) c ag acc none else_ cases :: rest) =
      let caseCodes := cases.flatMap fun (cs, _) => cs.getD []
      let ok := Val.kw "OK"
      let accList := if ag then acc
        else match op.answers with
          | .list l => if caseCodes.contains ok || !l.contains ok then [] else [ok]
          | _ => if caseCodes.contains ok then [] else [ok]
      if codeIn code accList then run w f fuel stb rest
      else match cases.find? (fun (cs, _) => match cs with | some l => codeIn code l | none => false) with
        | some (_, steps) => run w f fuel stb steps
        | none => match cases.find? (·.1.isNone) with
          | some (_, steps) => run w f fuel stb steps
          | none =>
            if !f.refusal.isEmpty then run w f fuel stb (faultRoute op.answers op.faults code f.refusal)
            else run w f fuel stb [.stop "MACHINE-CONTRACT" none] := by
  cases hans : op.answers
  · exact absurd hans hnans
  · simp only [run, hfl, hfind, hcall, hbind, hans, hcode, except_ok_bind, except_pure_bind,
      Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [run, hfl, hfind, hcall, hbind, hans, hcode, except_ok_bind, except_pure_bind,
      Bool.false_eq_true, ↓reduceIte]; rfl

def doRoute (w : World) (f : Frame) (fuel : Nat) (st : St)
    (vars : List String) (ag : Bool) (acc : List Val)
    (cases : List (Option (List Val) × List Step)) (rest : List Step)
    (op : Op) : Except String Res :=
  match op.answers with
  | .none => run w f fuel st rest
  | answers => do
    let code ← match vars with
      | v :: _ => var st v
      | [] => throw ":do of an operation with answers binds no code"
    let caseCodes := cases.flatMap fun (cs, _) => cs.getD []
    let ok := Val.kw "OK"
    let accList := if ag then acc
      else match answers with
        | .list l => if caseCodes.contains ok || !l.contains ok then [] else [ok]
        | _ => if caseCodes.contains ok then [] else [ok]
    if codeIn code accList then run w f fuel st rest
    else match cases.find? (fun (cs, _) => match cs with | some l => codeIn code l | none => false) with
      | some (_, steps) => run w f fuel st steps
      | none => match cases.find? (·.1.isNone) with
        | some (_, steps) => run w f fuel st steps
        | none =>
          if !f.refusal.isEmpty then run w f fuel st (faultRoute answers op.faults code f.refusal)
          else run w f fuel st [.stop "MACHINE-CONTRACT" none]

theorem run_do_when (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (vars : List String) (c : Call) (ag : Bool) (acc : List Val)
    (wExpr : Expr) (else_ : List Expr) (cases : List (Option (List Val) × List Step))
    (rest : List Step) (op : Op) (vw : Val) (res : Res)
    (hfl : flush w f st = .ok st')
    (hp : st'.pending = [])
    (hn : st'.next = none)
    (hfind : findOp w c.op = .ok op)
    (hw : ev w f.kind st' wExpr = .ok vw)
    (ht : vw.truthy = true → run w f (fuel + 1) st' (.do_ vars c ag acc none else_ cases :: rest) = .ok res)
    (hf : vw.truthy = false → ∀ (evs : List Val), else_.mapM (ev w f.kind st') = .ok evs →
      doRoute w f fuel { st' with vars := vars.zip evs ++ st'.vars } vars ag acc cases rest op = .ok res)
    (hevs : vw.truthy = false → ∃ evs, else_.mapM (ev w f.kind st') = .ok evs) :
    run w f (fuel + 1) st (.do_ vars c ag acc (some wExpr) else_ cases :: rest) = .ok res := by
  have hfl_id : flush w f st' = .ok st' := flush_empty w f st' hp hn
  by_cases hb : vw.truthy = true
  · have ht' := ht hb
    simp only [run, hfl_id, hfind, except_ok_bind, except_pure_bind, Bool.false_eq_true, ↓reduceIte] at ht'
    simp only [run, hfl, hfind, hw, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, except_ok_bind, except_pure_bind]
    exact ht'
  · have hbf : vw.truthy = false := Bool.eq_false_iff.mpr hb
    obtain ⟨evs, hevs'⟩ := hevs hbf
    simp only [run, hfl, hfind, hw, hbf, Bool.not_false, ↓reduceIte, hevs', except_ok_bind, except_pure_bind]
    exact hf hbf evs hevs'

theorem run_issue (w : World) (f : Frame) (fuel : Nat) (st st' stb : St)
    (c : Call) (ok refused rest : List Step) (op : Op) (r code : Val)
    (hfl : flush w f st = .ok st')
    (hcall : callOp w f.kind st' c = .ok (op, r))
    (hbind : bindOuts st' op.stobjsOut ["FN2-ISSUE-CODE", "FN2-ISSUE-OP", "FN2-ISSUE-OPGEN"] r = .ok stb)
    (hcode : var stb "FN2-ISSUE-CODE" = .ok code) :
    run w f (fuel + 1) st (.issue c ok refused :: rest) =
      if code == Val.kw "OK" then run w f fuel stb ok
      else if code == Val.kw "EXHAUSTED" then
        run w f fuel stb (refused ++ [.park "OPERATION" none none none])
      else run w f fuel stb (refused ++ (if f.refusal.isEmpty then [.halt] else f.refusal)) := by
  simp [run, hfl, hcall, hbind, hcode]

theorem run_goto (w : World) (f : Frame) (fuel : Nat) (st st' : St)
    (name : String) (rest : List Step) (sub : Arm) (id slot : Val) (reads : Env) (d : ArmDecl)
    (hfl : flush w f st = .ok st')
    (hsub : f.kind.subarms.find? (·.tag == name) = some sub)
    (hid : var st' "ID" = .ok id)
    (hslot : var st' "SLOT" = .ok slot)
    (hreads : rowReads w f.kind st'.stobjs id slot = .ok reads)
    (hdecl : sub.read = .ok d) :
    run w f (fuel + 1) st (.goto name :: rest) =
      run w { f with refusal := d.onRefusal } fuel
        { stobjs := st'.stobjs, vars := reads ++ f.base } d.steps := by
  simp [run, hfl, hsub, hid, hslot, hreads, hdecl]

/-! ### Additional world-independent dispatch, binding, and tuple combinators -/

theorem const_coreWorld (w : World) (tuple : List String) (c : String) :
    const (coreWorld w tuple) c = const w c := rfl

theorem callFn_of_native (w : World) (f : String) (args : List Val) (v : Val)
    (h : nativeCall f args = some v) :
    callFn w f args = .ok v := by
  simp [callFn, h]

theorem callFn_core_plain (w : World) (tuple : List String) (f : String) (args : List Val)
    (h : f.endsWith "@CORE" = false) :
    callFn (coreWorld w tuple) f args = callFn w f args := by
  simp [callFn, coreWorld, coreFns, h]

theorem callFn_core_of_fns (w : World) (tuple : List String) (f : String) (args : List Val) (v : Val)
    (hend : f.endsWith "@CORE" = false)
    (hn : nativeCallNames.contains f = false)
    (hf : w.fns f args = some v) :
    callFn (coreWorld w tuple) f args = .ok v :=
  (callFn_core_plain w tuple f args hend).trans (callFn_of_fns w f args v hn hf)

theorem callFn_core_link {n : Nat} (w : World) (tuple : List String)
    (f fn : String) (pre : List Val) (kids : Fin n → Val) (v : Val)
    (hlen : tuple.length = n)
    (hnat : nativeCallNames.contains f = false)
    (hend : f.endsWith "@CORE" = true)
    (hnop : w.ops.find? (fun o => adapterName o.name == f) = none)
    (hstrip : String.ofList (f.toList.take (f.length - 5)) = fn)
    (hfns : w.fns fn (pre ++ [tupleImage kids]) = some v) :
    callFn (coreWorld w tuple) f (pre ++ List.ofFn kids) = .ok v := by
  have hlt : ¬((pre ++ List.ofFn kids).length < tuple.length) := by simp [hlen]
  have hsub : (pre ++ List.ofFn kids).length - tuple.length = pre.length := by simp [hlen]
  have htk : (pre ++ List.ofFn kids).take pre.length = pre := by simp
  have hdr : Val.ofList ((pre ++ List.ofFn kids).drop pre.length) = tupleImage kids := by
    simp [tupleImage]
  have hcf : (coreWorld w tuple).fns f (pre ++ List.ofFn kids) = some v := by
    simp only [coreWorld, coreFns, hend, ↓reduceIte, hnop, hlt, hsub, htk, hdr, hstrip, hfns]
  exact callFn_of_fns (coreWorld w tuple) f (pre ++ List.ofFn kids) v hnat hcf

theorem collapse_replicate_core {n : Nat} (pre : List Val) (kids : Fin n → Val) :
    collapse n (List.replicate pre.length none ++ [some "FN2-CORE"]) (pre ++ List.ofFn kids) =
      some (pre ++ [tupleImage kids]) := by
  induction pre with
  | nil =>
    have htk : (List.ofFn kids).take n = List.ofFn kids := List.take_of_length_le (by simp)
    have hdr : (List.ofFn kids).drop n = [] := List.drop_eq_nil_of_le (by simp)
    simp only [List.replicate, List.nil_append, collapse,
      beq_self_eq_true, ↓reduceIte, List.length_ofFn, Nat.lt_irrefl, htk, hdr,
      Option.map_some, tupleImage]
  | cons a as ih => simp [List.replicate_succ, collapse, ih]

theorem callFn_core_pure_op {n : Nat} (w : World) (tuple : List String)
    (f : String) (o : Op) (pre : List Val) (kids : Fin n → Val) (v : Val)
    (hlen : tuple.length = n)
    (hnat : nativeCallNames.contains f = false)
    (hend : f.endsWith "@CORE" = true)
    (hop : w.ops.find? (fun o' => adapterName o'.name == f) = some o)
    (hcin : o.coreIn = List.replicate pre.length none ++ [some "FN2-CORE"])
    (hcout : o.coreOut = [none])
    (hfns : w.fns o.name (pre ++ [tupleImage kids]) = some v) :
    callFn (coreWorld w tuple) f (pre ++ List.ofFn kids) = .ok v := by
  have hcf : (coreWorld w tuple).fns f (pre ++ List.ofFn kids) = some v := by
    simp only [coreWorld, coreFns, hend, ↓reduceIte, hop, hcin, hlen,
      collapse_replicate_core pre kids, hfns, Option.map_some, hcout, spread]
  exact callFn_of_fns (coreWorld w tuple) f (pre ++ List.ofFn kids) v hnat hcf

theorem findOp_of_find (w : World) (name : String) (o : Op)
    (hfind : w.ops.find? (·.name == name) = some o) :
    findOp w name = .ok o := by
  simp [findOp, hfind]

theorem findOp_coreWorld (w : World) (tuple : List String) (name : String) (o : Op)
    (hfind : w.ops.find? (·.name == name) = some o) :
    findOp (coreWorld w tuple) name = .ok (coreOp tuple o) := by
  unfold findOp coreWorld
  have hmap : ∀ (os : List Op), os.find? (·.name == name) = some o →
      (os.map (coreOp tuple)).find? (·.name == name) = some (coreOp tuple o) := by
    intro os hos
    induction os with
    | nil => simp at hos
    | cons x xs ih =>
      have hname : (coreOp tuple x).name = x.name := by
        unfold coreOp; cases x.callee <;> simp; split <;> rfl
      simp only [List.find?_cons, List.map_cons, hname] at hos ⊢
      split at hos
      · simp only [Option.some.injEq] at hos; subst hos; rfl
      · exact ih hos
  rw [hmap w.ops hfind]

theorem callOp_callee (w : World) (k : Kind) (st : St) (c : Call)
    (o : Op) (callee : String) (keys : List (String × Expr)) (args : List Val) (r : Val)
    (hfind : findOp w c.op = .ok o)
    (hcal : o.callee = some callee)
    (hkeys : expandOwner w k c.keys = .ok keys)
    (hargs : actuals w k st o.formals o.stobjsIn c.args keys = .ok args)
    (hcall : callFn w callee args = .ok r) :
    callOp w k st c = .ok (o, r) := by
  simp [callOp, hfind, hcal, hkeys, hargs, hcall]

theorem keyOrOwner_found (w : World) (k : Kind) (st : St) (fm : String)
    (keys : List (String × Expr)) (kw : String) (e : Expr) (v : Val)
    (hf : keys.find? (·.1 == ":" ++ fm) = some (kw, e))
    (hev : ev w k st e = .ok v) :
    keyOrOwner w k st fm keys = .ok v := by
  simp [keyOrOwner, hf, hev]

theorem keyOrOwner_okind (w : World) (k : Kind) (st : St) (keys : List (String × Expr)) (v : Val)
    (hf : keys.find? (·.1 == ":OKIND") = none) (hv : var st "KIND" = .ok v) :
    keyOrOwner w k st "OKIND" keys = .ok v := by
  simp [keyOrOwner, hf, hv]

theorem keyOrOwner_oslot (w : World) (k : Kind) (st : St) (keys : List (String × Expr)) (v : Val)
    (hf : keys.find? (·.1 == ":OSLOT") = none) (hv : var st "ID" = .ok v) :
    keyOrOwner w k st "OSLOT" keys = .ok v := by
  simp [keyOrOwner, hf, hv]

theorem keyOrOwner_ogen (w : World) (k : Kind) (st : St) (keys : List (String × Expr)) (v : Val)
    (hf : keys.find? (·.1 == ":OGEN") = none) (hv : var st "ROW-GENERATION" = .ok v) :
    keyOrOwner w k st "OGEN" keys = .ok v := by
  simp [keyOrOwner, hf, hv]

theorem actuals_nil (w : World) (k : Kind) (st : St) (ss : List (Option String))
    (keys : List (String × Expr)) :
    actuals w k st [] ss [] keys = .ok [] := rfl

theorem actuals_stobj (w : World) (k : Kind) (st : St)
    (fm : String) (fs : List String) (s : String) (ss : List (Option String))
    (pos : List Expr) (keys : List (String × Expr)) (v : Val) (rest : List Val)
    (hs : stobj st s = .ok v)
    (hr : actuals w k st fs ss pos keys = .ok rest) :
    actuals w k st (fm :: fs) (some s :: ss) pos keys = .ok (v :: rest) := by
  simp [actuals, hs, hr]

theorem actuals_pos (w : World) (k : Kind) (st : St)
    (fm : String) (fs : List String) (ss : List (Option String))
    (p : Expr) (ps : List Expr) (keys : List (String × Expr)) (v : Val) (rest : List Val)
    (hv : ev w k st p = .ok v)
    (hr : actuals w k st fs ss ps keys = .ok rest) :
    actuals w k st (fm :: fs) (none :: ss) (p :: ps) keys = .ok (v :: rest) := by
  simp [actuals, hv, hr]

theorem actuals_key (w : World) (k : Kind) (st : St)
    (fm : String) (fs : List String) (ss : List (Option String))
    (keys : List (String × Expr)) (v : Val) (rest : List Val)
    (hv : keyOrOwner w k st fm keys = .ok v)
    (hr : actuals w k st fs ss [] keys = .ok rest) :
    actuals w k st (fm :: fs) (none :: ss) [] keys = .ok (v :: rest) := by
  have hact0 : actuals w k st (fm :: fs) (none :: ss) [] keys =
      (do let y ← keyOrOwner w k st fm keys
          let rest ← actuals w k st fs ss [] keys
          pure (y :: rest)) := by
    conv => lhs; unfold actuals
    unfold keyOrOwner
    cases keys.find? (·.1 == ":" ++ fm) with
    | some kv => obtain ⟨_, _⟩ := kv; rfl
    | none =>
      cases (fm == "OKIND") <;> cases (fm == "OSLOT") <;> cases (fm == "OGEN") <;>
        simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  rw [hact0, hv, except_ok_bind, hr]
  rfl

theorem coreActuals_nil (w : World) (k : Kind) (st : St) (coreVal : Val)
    (ss : List (Option String)) (keys : List (String × Expr)) :
    coreActuals w k st coreVal [] ss [] keys = .ok [] := rfl

theorem coreActuals_core (w : World) (k : Kind) (st : St) (coreVal : Val)
    (fm : String) (fs : List String) (ss : List (Option String))
    (pos : List Expr) (keys : List (String × Expr)) (rest : List Val)
    (hr : coreActuals w k st coreVal fs ss pos keys = .ok rest) :
    coreActuals w k st coreVal (fm :: fs) (some "FN2-CORE" :: ss) pos keys = .ok (coreVal :: rest) := by
  simp [coreActuals, hr]

theorem coreActuals_stobj (w : World) (k : Kind) (st : St) (coreVal : Val)
    (fm : String) (fs : List String) (s : String) (ss : List (Option String))
    (pos : List Expr) (keys : List (String × Expr)) (v : Val) (rest : List Val)
    (hne : (s == "FN2-CORE") = false)
    (hs : stobj st s = .ok v)
    (hr : coreActuals w k st coreVal fs ss pos keys = .ok rest) :
    coreActuals w k st coreVal (fm :: fs) (some s :: ss) pos keys = .ok (v :: rest) := by
  simp [coreActuals, hne, hs, hr]

theorem coreActuals_pos (w : World) (k : Kind) (st : St) (coreVal : Val)
    (fm : String) (fs : List String) (ss : List (Option String))
    (p : Expr) (ps : List Expr) (keys : List (String × Expr)) (v : Val) (rest : List Val)
    (hv : ev w k st p = .ok v)
    (hr : coreActuals w k st coreVal fs ss ps keys = .ok rest) :
    coreActuals w k st coreVal (fm :: fs) (none :: ss) (p :: ps) keys = .ok (v :: rest) := by
  simp [coreActuals, hv, hr]

theorem coreActuals_key (w : World) (k : Kind) (st : St) (coreVal : Val)
    (fm : String) (fs : List String) (ss : List (Option String))
    (keys : List (String × Expr)) (v : Val) (rest : List Val)
    (hv : keyOrOwner w k st fm keys = .ok v)
    (hr : coreActuals w k st coreVal fs ss [] keys = .ok rest) :
    coreActuals w k st coreVal (fm :: fs) (none :: ss) [] keys = .ok (v :: rest) := by
  simp [coreActuals, hv, hr]

theorem bindOuts_single_stobj (st : St) (s : String) (vars : List String) (res : Val) :
    bindOuts st [some s] vars res = .ok (setStobj st s res) := rfl

theorem bindOuts_single_val (st : St) (vars : List String) (res : Val) :
    bindOuts st [none] vars res = .ok (match vars with
      | v :: _ => { st with vars := (v, res) :: st.vars }
      | [] => st) := by
  cases vars <;> rfl

theorem bindOuts_multi {m : Nat} (st : St) (outs : List (Option String))
    (vars : List String) (res : Val)
    (hm : 2 ≤ m) (hlen : outs.length = m) (hres : IsListN m res) :
    bindOuts st outs vars res =
      bindOuts.go st outs vars ((List.range m).map (fun (j : Nat) => Native.nth (.int j) res)) := by
  cases outs with
  | nil => simp at hlen; omega
  | cons a rest =>
    cases rest with
    | nil => simp at hlen; omega
    | cons b rest' =>
      simp only [bindOuts, toList_eq_map_nth res hres]

theorem bindOuts_go_nil (st : St) (vars : List String) (rs : List Val) :
    bindOuts.go st [] vars rs = .ok st := rfl

theorem bindOuts_go_some (st : St) (s : String) (os : List (Option String))
    (vars : List String) (r : Val) (rs : List Val) :
    bindOuts.go st (some s :: os) vars (r :: rs) = bindOuts.go (setStobj st s r) os vars rs := rfl

theorem bindOuts_go_none_cons (st : St) (os : List (Option String))
    (v : String) (vs : List String) (r : Val) (rs : List Val) :
    bindOuts.go st (none :: os) (v :: vs) (r :: rs) =
      bindOuts.go { st with vars := (v, r) :: st.vars } os vs rs := rfl

theorem bindOuts_go_none_nil (st : St) (os : List (Option String)) (r : Val) (rs : List Val) :
    bindOuts.go st (none :: os) [] (r :: rs) = bindOuts.go st os [] rs := rfl

theorem env_get_of_findIdx (env : Env) (ks : List String) (x : String) (idx : Nat) (v : Val)
    (hks : env.map (·.1) = ks)
    (hidx : findIdx? x ks = some idx)
    (hval : (env.map (·.2))[idx]? = some v) :
    env.get? x = some v := by
  induction env generalizing ks idx with
  | nil => subst hks; simp [findIdx?] at hidx
  | cons p env ih =>
    obtain ⟨k, w⟩ := p
    subst hks
    simp only [List.map_cons, findIdx?] at hidx hval
    by_cases hk : (k == x) = true
    · simp only [hk, ↓reduceIte, Option.some.injEq] at hidx
      subst hidx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hval
      subst hval
      simp [Env.get?, hk]
    · have hkf : (k == x) = false := Bool.eq_false_iff.mpr hk
      simp only [hkf, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hidx
      obtain ⟨j, hj, rfl⟩ := hidx
      simp only [List.getElem?_cons_succ] at hval
      simpa [Env.get?, hkf] using ih (env.map (·.1)) j rfl hj hval

theorem var_of_findIdx (st : St) (ks : List String) (x : String) (idx : Nat) (v : Val)
    (hks : st.vars.map (·.1) = ks)
    (hidx : findIdx? x ks = some idx)
    (hval : (st.vars.map (·.2))[idx]? = some v) :
    var st x = .ok v := by
  simp [var, env_get_of_findIdx st.vars ks x idx v hks hidx hval]

theorem env_get_none_of_keys (vars : Env) (ks : List String) (x : String)
    (hks : vars.map (·.1) = ks)
    (hmem : ks.contains x = false) :
    vars.get? x = none := by
  induction vars generalizing ks with
  | nil => rfl
  | cons p vars ih =>
    obtain ⟨k, w⟩ := p
    subst hks
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at hmem
    have hkf : (k == x) = false := by
      cases hnk : (x == k)
      · exact beq_eq_false_iff_ne.mpr (Ne.symm (beq_eq_false_iff_ne.mp hnk))
      · rw [hmem.1] at hnk; cases hnk
    simpa [Env.get?, hkf] using ih (vars.map (·.1)) rfl hmem.2

theorem evalArgs_append (fns : Fns) (env : Env) (as bs : List Term) (vas vbs : List Val)
    (ha : evalArgs fns env as = .ok vas) (hb : evalArgs fns env bs = .ok vbs) :
    evalArgs fns env (as ++ bs) = .ok (vas ++ vbs) := by
  induction as generalizing vas with
  | nil =>
    simp only [evalArgs, Except.ok.injEq] at ha
    subst ha; simpa using hb
  | cons a as ih =>
    simp only [evalArgs] at ha
    obtain ⟨v, hv, hr⟩ := bind_ok' ha
    obtain ⟨vs, hvs, heq⟩ := bind_ok' hr
    simp only [pure, Except.pure, Except.ok.injEq] at heq; subst heq
    simp [evalArgs, hv, ih vs hvs]

theorem evalArgs_zip_vars (fns : Fns) (ks : List String) (vs : List Val) (env : Env)
    (hlen : ks.length = vs.length) (hnd : nodupB ks = true)
    (hget : ∀ k v, (ks.zip vs).find? (·.1 == k) = some (k, v) → env.get? k = some v) :
    evalArgs fns env (ks.map Term.var) = .ok vs := by
  induction ks generalizing vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons k ks ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at hnd
      have hk0 : env.get? k = some v := hget k v (by simp)
      have hrest : evalArgs fns env (ks.map Term.var) = .ok vs := by
        apply ih vs (by simpa using hlen) hnd.2
        intro k' v' hf
        apply hget k' v'
        have hmem : k' ∈ ks := by
          have hb := List.find?_some hf
          have hm := List.mem_of_find?_eq_some hf
          exact (beq_iff_eq.mp hb) ▸ (List.of_mem_zip hm).1
        have hne : (k == k') = false := by
          cases hc : (k == k')
          · rfl
          · have heq := beq_iff_eq.mp hc; subst heq
            have : ks.contains k = true := List.contains_iff_mem.mpr hmem
            rw [hnd.1] at this; cases this
        simp [hne, hf]
      simp [evalArgs, eval_var fns env k v hk0, hrest]

theorem evalArgs_tuple_vars {n : Nat} (fns : Fns) (tuple : List String)
    (kids : Fin n → Val) (vars : Env) (varNames : List String)
    (hlen : tuple.length = n) (hnd : nodupB tuple = true)
    (hv : vars.map (·.1) = varNames)
    (hdisj : (varNames.any (fun x => tuple.contains x)) = false) :
    evalArgs fns (vars ++ tupleStobjs tuple kids) (tuple.map Term.var) =
      .ok (List.ofFn kids) := by
  apply evalArgs_zip_vars fns tuple (List.ofFn kids) _ (by simp [hlen]) hnd
  intro k v hf
  have hmem : k ∈ tuple := by
    have hb := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    exact (beq_iff_eq.mp hb) ▸ (List.of_mem_zip hm).1
  have hnmem : varNames.contains k = false := by
    cases hc : varNames.contains k
    · rfl
    · have hk_in : k ∈ varNames := List.contains_iff_mem.mp hc
      have ht_in : tuple.contains k = true := List.contains_iff_mem.mpr hmem
      have hany : (varNames.any (fun x => tuple.contains x)) = true :=
        List.any_eq_true.mpr ⟨k, hk_in, ht_in⟩
      rw [hdisj] at hany; cases hany
  have hvn : vars.get? k = none := env_get_none_of_keys vars varNames k hv hnmem
  have hvf : vars.find? (·.1 == k) = none := by
    cases hfx : vars.find? (·.1 == k) <;> simp_all [Env.get?]
  simp [Env.get?, List.find?_append, hvf, tupleStobjs, hf]

theorem rowReads_tupleStobjs {n : Nat} (w : World) (k : Kind) (tuple : List String)
    (kids : Fin n → Val) (id slot : Val) (ownIdx dirIdx : Nat)
    (hown : ownIdx < n) (hdir : dirIdx < n) (hlen : tuple.length = n)
    (hf_own : findIdx? k.name tuple = some ownIdx)
    (hf_dir : findIdx? "FN2-MACHINES" tuple = some dirIdx)
    (read : String → Val)
    (hread : ∀ c ∈ k.columns.map (·.1),
      callFn w (if directoryFields.contains c then "FN2-MACHINES-" ++ c else k.name ++ "-" ++ c)
        (if directoryFields.contains c then [id, kids ⟨dirIdx, hdir⟩] else [slot, kids ⟨ownIdx, hown⟩]) =
        .ok (read c)) :
    rowReads w k (tupleStobjs tuple kids) id slot =
      .ok (k.columns.map fun (c, _) => ("ROW-" ++ c, read c)) :=
  rowReads_eq w k (tupleStobjs tuple kids) id slot (kids ⟨ownIdx, hown⟩) (kids ⟨dirIdx, hdir⟩)
    (find_tupleStobjs tuple kids k.name ownIdx hown hlen hf_own)
    (find_tupleStobjs tuple kids "FN2-MACHINES" dirIdx hdir hlen hf_dir)
    read hread

theorem runArm_tupleStobjs {n : Nat} (w : World) (k : Kind) (tuple : List String)
    (a : Arm) (observe : Bool) (pre : List Val) (kids : Fin n → Val)
    (reads : Env) (d : ArmDecl) (fuel : Nat) (v : Val)
    (hcf : k.childForm = true) (htup : k.tuple = tuple) (hlen : tuple.length = n)
    (hpre : pre.length = (if observe then 10 else 5))
    (hreads : rowReads w k (tupleStobjs tuple kids) (pre.headD Val.nil) ((pre.drop 1).headD Val.nil) = .ok reads)
    (hdecl : a.read = .ok d)
    (hrun : run w
      { kind := k, observe := observe, refusal := d.onRefusal,
        base := (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
          "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).zip pre }
      fuel { stobjs := tupleStobjs tuple kids,
             vars := reads ++ (if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
               "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]).zip pre }
      d.steps = .ok (.done v)) :
    runArm w k a observe (pre ++ List.ofFn kids) fuel = .ok v := by
  apply runArm_eq w k a observe pre (List.ofFn kids) reads d fuel v hcf hpre (by simp [htup, hlen])
  · simpa [htup, tupleStobjs] using hreads
  · exact hdecl
  · simpa [htup, tupleStobjs] using hrun

theorem run_cond_true (w : World) (f : Frame) (fuel : Nat) (st : St)
    (c : Expr) (steps : List Step) (more : List (Expr × List Step)) (rest : List Step)
    (vc : Val) (hc : ev w f.kind st c = .ok vc) (ht : vc.truthy = true) :
    run w f (fuel + 1) st (.cond ((c, steps) :: more) :: rest) = run w f fuel st steps := by
  dsimp only [run, List.findM?]
  rw [hc, except_ok_bind, except_pure_bind, ht]
  simp only [except_pure_bind]

theorem codeIn_eq_memberEqual_truthy (code : Val) (codes : List Val) :
    codeIn code codes = (Native.memberEqual code (Val.ofList codes)).truthy := by
  induction codes with
  | nil => rfl
  | cons a cs ih =>
    simp only [codeIn, List.contains_cons, Val.ofList, Native.memberEqual]
    by_cases h : (code == a) = true
    · simp [h, Val.truthy]
    · have hf : (code == a) = false := Bool.eq_false_iff.mpr h
      simp [hf, ← ih, codeIn]

theorem codeIn_singleton_eq_equal_truthy (code k : Val) :
    codeIn code [k] = (Prim.equal code k).truthy := by
  simp only [codeIn, List.contains_cons, List.contains_nil, Bool.or_false, Prim.equal]
  by_cases h : code = k
  · subst h; simp [Val.ofBool, Val.truthy, Val.t]
  · simp [beq_eq_false_iff_ne.mpr h, Val.ofBool, Val.truthy, Val.nil]

end Fn2.Arms.Combinators

end
