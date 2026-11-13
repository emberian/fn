#!/usr/bin/env python3
"""Mechanical whole-arm Lean proof generator for served machine certificates.

Emits shared certificate combinator/operation modules and per-root whole-arm
interpretation proofs in `meta/Fn2/Instances/ServedCertificates/`:
  - `ServedCommon.lean`: primitive/boolean/write-guard normalizers & `isListB`.
  - `ServedOps.lean`: bottom-up `isListB` / `IsListN` theorems for multi-return
    callees and countdown loops (`Fn2.ACL2.Fuel`).
  - `Kind<ki>Subarms.lean` & `Kind<ki>CoreSubarms.lean`: compositional subarm
    `run` theorems in topological `:goto` DAG order for child-form kinds.
  - `Kind<ki>Common.lean`: entry snapshot & `<KN>-WRITE+...` batch-write lemmas
    for core-form kinds.
  - `Root<ri>Proof.lean`: `validated`, `accepted_entry_positive`, and
    `omitted_child_rejected` for each generated root.
"""
from pathlib import Path
import re
from emit_lean import (
    Atom, Str, List, as_list, is_nil, is_lambda, lean_str, ident, val, show,
    as_module, CORE_STRING_BODIES,
)
from emit_embed import alist_value, calls_of

DIRECTORY_FIELDS = ("READY-PREV", "READY-NEXT", "WAIT-REASON")

VOCAB_ARITY = {
    "NOT": 1, "NULL": 1, "ATOM": 1, "CONSP": 1, "SYMBOLP": 1, "STRINGP": 1,
    "CHARACTERP": 1, "INTEGERP": 1, "RATIONALP": 1, "ACL2-NUMBERP": 1,
    "NATP": 1, "POSP": 1, "ZP": 1, "ZIP": 1, "EVENP": 1, "ODDP": 1,
    "NFIX": 1, "IFIX": 1, "CAR": 1, "CDR": 1, "CAAR": 1, "CADR": 1, "CDAR": 1,
    "CDDR": 1, "CADDR": 1, "CDDDR": 1, "CADDDR": 1, "FIRST": 1, "SECOND": 1,
    "THIRD": 1, "FOURTH": 1, "LEN": 1, "LENGTH": 1, "LOGNOT": 1, "ACL2-COUNT": 1,
    "CHAR-CODE": 1, "CODE-CHAR": 1, "SYMBOL-NAME": 1, "SYMBOL-PACKAGE-NAME": 1,
    "CONS": 2, "EQUAL": 2, "<": 2, "BINARY-+": 2, "BINARY-*": 2, "UNARY--": 1,
    "FLOOR": 2, "CEILING": 2, "MOD": 2, "REM": 2, "TRUNCATE": 2,
    "NONNEGATIVE-INTEGER-QUOTIENT": 2, "ASH": 2, "EXPT": 2,
    "BINARY-LOGAND": 2, "BINARY-LOGIOR": 2, "BINARY-LOGXOR": 2, "BINARY-LOGEQV": 2,
    "LOGORC1": 2, "LOGBITP": 2, "LOGHEAD": 2, "LOGTAIL": 2, "UNSIGNED-BYTE-P": 2,
    "SIGNED-BYTE-P": 2, "INTEGER-RANGE-P": 3, "MIN": 2, "MAX": 2,
    "NTH": 2, "MV-NTH": 2, "UPDATE-NTH": 3, "MEMBER-EQUAL": 2, "MEMBER-EQL": 2,
    "ASSOC-EQUAL": 2, "COERCE": 2, "INTERN-IN-PACKAGE-OF-SYMBOL": 2,
}

NATIVE_IMPL_EXPR = {
    "EQUAL": lambda a: f"(Prim.equal {a[0]} {a[1]})",
    "CONS": lambda a: f"(Val.cons {a[0]} {a[1]})",
    "CAR": lambda a: f"(Val.car {a[0]})",
    "CDR": lambda a: f"(Val.cdr {a[0]})",
    "CONSP": lambda a: f"(Prim.consp {a[0]})",
    "INTEGERP": lambda a: f"(Prim.integerp {a[0]})",
    "ACL2-NUMBERP": lambda a: f"(Prim.acl2Numberp {a[0]})",
    "RATIONALP": lambda a: f"(Prim.rationalp {a[0]})",
    "COERCE": lambda a: f"(Prim.coerce {a[0]} {a[1]})",
    "SYMBOLP": lambda a: f"(Prim.symbolp {a[0]})",
    "STRINGP": lambda a: f"(Prim.stringp {a[0]})",
    "CHARACTERP": lambda a: f"(Prim.characterp {a[0]})",
    "<": lambda a: f"(Prim.lt {a[0]} {a[1]})",
    "BINARY-+": lambda a: f"(Prim.plus {a[0]} {a[1]})",
    "BINARY-*": lambda a: f"(Prim.times {a[0]} {a[1]})",
    "UNARY--": lambda a: f"(Prim.neg {a[0]})",
    "BINARY-LOGAND": lambda a: f"(Native.logand {a[0]} {a[1]})",
    "BINARY-LOGIOR": lambda a: f"(Native.logior {a[0]} {a[1]})",
    "BINARY-LOGXOR": lambda a: f"(Native.logxor {a[0]} {a[1]})",
    "BINARY-LOGEQV": lambda a: f"(Native.logeqv {a[0]} {a[1]})",
    "LOGNOT": lambda a: f"(Native.lognot {a[0]})",
    "LOGORC1": lambda a: f"(Native.logorc1 {a[0]} {a[1]})",
    "FLOOR": lambda a: f"(Native.floor {a[0]} {a[1]})",
    "CEILING": lambda a: f"(Native.ceiling {a[0]} {a[1]})",
    "CHAR-CODE": lambda a: f"(Prim.charCode {a[0]})",
    "CODE-CHAR": lambda a: f"(Prim.codeChar {a[0]})",
    "MOD": lambda a: f"(Native.mod {a[0]} {a[1]})",
    "EVENP": lambda a: f"(Native.evenp {a[0]})",
    "NONNEGATIVE-INTEGER-QUOTIENT": lambda a: f"(Native.niq {a[0]} {a[1]})",
    "EXPT": lambda a: f"(Native.expt {a[0]} {a[1]})",
    "ASH": lambda a: f"(Native.ash {a[0]} {a[1]})",
    "LEN": lambda a: f"(Native.len {a[0]})",
    "NTH": lambda a: f"(Native.nth {a[0]} {a[1]})",
    "MV-NTH": lambda a: f"(Native.nth {a[0]} {a[1]})",
    "UPDATE-NTH": lambda a: f"(Native.updateNth {a[0]} {a[1]} {a[2]})",
    "MEMBER-EQUAL": lambda a: f"(Native.memberEqual {a[0]} {a[1]})",
    "ACL2-COUNT": lambda a: f"(Val.int (Val.acl2Count {a[0]}))",
}


def plist_dict(xs):
    xs = list(xs)
    return {str(xs[i]): xs[i + 1] for i in range(0, len(xs) - 1, 2)}


def plist_has(xs, key):
    xs = list(xs)
    for i in range(0, len(xs) - 1, 2):
        if str(xs[i]) == key:
            return True
    return False


def plist_get(xs, key, default=None):
    xs = list(xs)
    for i in range(0, len(xs) - 1, 2):
        if str(xs[i]) == key:
            return xs[i + 1]
    return default


def sym_str(x):
    if isinstance(x, Atom):
        s = str(x)
        if s == "NIL":
            return "NIL"
        if s == "T":
            return "T"
        if not s.lstrip("-").isdigit():
            return s
    return None


def is_sym(x):
    return sym_str(x) is not None


def val_kw(s):
    return Atom(s if s.startswith(":") else ":" + s)


# ---------------------------------------------------------------------------
# Shared Lean modules: ServedCommon.lean and ServedOps.lean
# ---------------------------------------------------------------------------

SERVED_COMMON_BODY = """import Fn2.Arms.Combinators
import Fn2.Arms.Wrapper
import Fn2.ACL2.Fuel
import Fn2.ACL2.Pres
import Fn2.Instances.ServedMetadata
import Fn2.Instances.LayerAEqns1
import Fn2.Instances.LayerAEqns2
import Fn2.Instances.LayerAEqns3
import Fn2.Instances.LayerAEqns4

set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Fn2.Instances.ServedCertificates.ServedCommon
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core Fn2.Instances.ServedKinds Fn2.Instances.LayerAWorld

structure ArmOut (n : Nat) where
  ans : List Val
  kids : Fin n → Val

def ArmOut.toChild {n : Nat} (o : ArmOut n) : Val :=
  Val.ofList (o.ans ++ List.ofFn o.kids)

def ArmOut.toCore {n : Nat} (o : ArmOut n) : Val :=
  Val.ofList (o.ans ++ [Combinators.tupleImage o.kids])

def ArmOut.toSub {n : Nat} (retIdxs : List (Fin n)) (single : Bool) (o : ArmOut n) : Val :=
  let xs := o.ans ++ retIdxs.map o.kids
  if single then xs.headD Val.nil else Val.ofList xs

@[simp] theorem ArmOut.toChild_ite {n : Nat} (c : Prop) [Decidable c] (a b : ArmOut n) :
    (if c then a else b).toChild = if c then a.toChild else b.toChild := by
  split <;> rfl

@[simp] theorem ArmOut.toCore_ite {n : Nat} (c : Prop) [Decidable c] (a b : ArmOut n) :
    (if c then a else b).toCore = if c then a.toCore else b.toCore := by
  split <;> rfl

@[simp] theorem ArmOut.toSub_ite {n : Nat} (retIdxs : List (Fin n)) (single : Bool)
    (c : Prop) [Decidable c] (a b : ArmOut n) :
    (if c then a else b).toSub retIdxs single =
      if c then a.toSub retIdxs single else b.toSub retIdxs single := by
  split <;> rfl

@[simp] theorem ArmOut.ans_ite {n : Nat} (c : Prop) [Decidable c] (a b : ArmOut n) :
    (if c then a else b).ans = if c then a.ans else b.ans := by
  split <;> rfl

@[simp] theorem ArmOut.kids_ite {n : Nat} (c : Prop) [Decidable c] (a b : ArmOut n) :
    (if c then a else b).kids = if c then a.kids else b.kids := by
  split <;> rfl

theorem finish_armOut_false {n : Nat} (tuple : List String) (o : ArmOut n)
    (ht : tuple.length = n) (ha : o.ans.length = 4) :
    finish false tuple o.toChild = .ok o.toCore := by
  rcases o with ⟨ans, kids⟩
  rcases ans with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> simp at ha
  exact Combinators.finish_arm_tupleImage tuple kids a0 a1 a2 a3 ht

theorem finish_armOut_true {n : Nat} (tuple : List String) (o : ArmOut n)
    (ht : tuple.length = n) (ha : o.ans.length = 1) :
    finish true tuple o.toChild = .ok o.toCore := by
  rcases o with ⟨ans, kids⟩
  rcases ans with _ | ⟨a0, _ | _⟩ <;> simp at ha
  exact Combinators.finish_observe_tupleImage tuple kids a0 ht

theorem omitted_child_subarm_rejected (w : World) (k : Kind) (a : Arm)
    (observe : Bool) (args : List Val) (fuel : Nat) (result : Val)
    (omitted : ((args.length != (if observe then 10 else 5) + k.tuple.length) = true)) :
    runArm w k a observe args fuel ≠ .ok result :=
  Combinators.omitted_child_rejected_arm w k a observe args fuel result (bne_iff_ne.mp omitted)


def isListB : Nat → Val → Bool
  | 0, .nil => true
  | n + 1, .cons _ d => isListB n d
  | _, _ => false

theorem isListN_of_isListB : ∀ {n : Nat} {v : Val}, isListB n v = true → Combinators.IsListN n v
  | 0, .cons _ _, h | 0, .int _, h | 0, .chr _, h | 0, .str _, h => by simp [isListB] at h
  | 0, .sym s, h => by
    by_cases hs : s = "NIL"
    · subst hs; exact Combinators.isListN_nil
    · simp [isListB, Val.nil, hs] at h
  | n + 1, .cons a d, h => Combinators.isListN_cons a d (isListN_of_isListB h)
  | _ + 1, .int _, h | _ + 1, .chr _, h | _ + 1, .str _, h | _ + 1, .sym _, h => by
    simp [isListB] at h

theorem isListB_ofList : ∀ (xs : List Val), isListB xs.length (Val.ofList xs) = true
  | [] => rfl
  | _ :: xs => isListB_ofList xs

theorem isListB_of_isListN {n : Nat} {v : Val} (h : Combinators.IsListN n v) : isListB n v = true := by
  have key := isListB_ofList v.toList
  rw [h.1, h.2] at key
  exact key

@[simp] theorem isListB_zero_nil : isListB 0 Val.nil = true := by rfl
@[simp] theorem isListB_succ_cons (n : Nat) (a d : Val) :
    isListB (n + 1) (Val.cons a d) = isListB n d := by rfl

theorem isListB_ite (n : Nat) (c : Prop) [Decidable c] (a b : Val) :
    isListB n (if c then a else b) = if c then isListB n a else isListB n b := by
  split <;> rfl

theorem isListB_upd (n : Nat) (idx : Int) (x v : Val)
    (hi : 0 ≤ idx ∧ idx < (n : Int)) (hv : isListB n v = true) :
    isListB n (Native.updateNth (.int idx) x v) = true := by
  have hidx : (.int idx : Val) = .int idx.toNat := by
    congr 1; omega
  rw [hidx]
  exact isListB_of_isListN (Combinators.isListN_updateNth idx.toNat x v (by omega) (isListN_of_isListB hv))

theorem isListB_tupleImage {n : Nat} (kids : Fin n → Val) :
    isListB n (Combinators.tupleImage kids) = true := by
  exact isListB_of_isListN (Combinators.isListN_tupleImage kids)

theorem or_false_left {a b : Val} (h : (if a.truthy then a else b).truthy = false) :
    a.truthy = false := by
  cases ha : a.truthy <;> simp [ha] at h ⊢

theorem zp_pred_lt {x : Val} (h : («ZP» x).truthy = false) :
    («NFIX» (Prim.plus (.int (-1)) x)).nfix < («NFIX» x).nfix := by
  cases x with
  | int i =>
    simp only [«ZP», «NFIX», «NOT», Prim.integerp, Prim.lt, Prim.plus, Val.isInt, Val.toInt,
      Val.truthy_ite, Val.truthy_ofBool, Val.truthy_nil, Val.truthy_t] at h ⊢
    by_cases h0 : i ≤ 0
    · have hi0 : ¬(0 < i) := by omega
      simp [hi0] at h
    · have hi0 : 0 < i := by omega
      have hpos : ¬(i < 0) := by omega
      have hm1 : ¬(-1 + i < 0) := by omega
      simp [hi0, hpos, hm1, Val.nfix, Val.toInt]
      omega
  | _ =>
    simp [«ZP», Prim.integerp, Val.isInt] at h

theorem zp_or_pred_lt {x b : Val} (h : (if («ZP» x).truthy then «ZP» x else b).truthy = false) :
    («NFIX» (Prim.plus (.int (-1)) x)).nfix < («NFIX» x).nfix := by
  exact zp_pred_lt (or_false_left h)

theorem nfix_lt_acl2Count_succ (x : Val) :
    («NFIX» x).nfix < (Val.int ↑x.acl2Count).nfix + 1 := by
  cases x with
  | int i =>
    simp only [«NFIX», «NOT», Prim.integerp, Prim.lt, Val.isInt, Val.toInt,
      Val.truthy_ite, Val.truthy_ofBool, Val.truthy_nil, Val.truthy_t, Val.acl2Count]
    by_cases h : i < 0
    · simp [h, Val.nfix, Val.toInt]
    · have h2 : (i.natAbs : Int) = i := Int.natAbs_of_nonneg (by omega)
      simp [h, h2]
  | _ =>
    simp [«NFIX», Prim.integerp, Val.isInt, Val.nfix, Val.toInt]

theorem eq_def (a b : Val) : «EQ» a b = Prim.equal a b := by rfl
theorem eql_def (a b : Val) : «EQL» a b = Prim.equal a b := by rfl
theorem num_eq_def (a b : Val) : «=» a b = Prim.equal a b := by rfl
theorem not_def (x : Val) : «NOT» x = (if x.truthy then Val.nil else Val.t) := by rfl
theorem atom_def (x : Val) : «ATOM» x = (if (Prim.consp x).truthy then Val.nil else Val.t) := by rfl

theorem null_def (x : Val) : «NULL» x = (if x.truthy then Val.nil else Val.t) := by
  cases x with
  | sym s =>
    simp only [«NULL», «EQ», Prim.equal, Val.nil, Val.t, Val.ofBool]
    by_cases hs : s = "NIL"
    · subst hs; simp [Val.truthy]
    · have hb : (Val.sym s == Val.sym "NIL") = false :=
        beq_eq_false_iff_ne.mpr (by intro he; injection he; exact hs ‹_›)
      simp [Val.truthy, hs, hb]
  | _ =>
    simp [«NULL», «EQ», Prim.equal, Val.ofBool, Val.truthy, Val.nil, Val.t]

theorem equal_sym_truthy (x : Val) (s : String) :
    (Prim.equal x (.sym s)).truthy = (x == .sym s) := by
  simp [Prim.equal, Val.truthy_ofBool]

theorem equal_val_truthy (a b : Val) :
    (Prim.equal a b).truthy = (a == b) := by
  simp [Prim.equal, Val.truthy_ofBool]

theorem fits_ite (ty : ColType) (c : Prop) [Decidable c] (a b : Val) :
    ty.fits (if c then a else b) = if c then ty.fits a else ty.fits b := by
  split <;> rfl

theorem fits_enum_int (n : Nat) (i : Int) :
    ColType.fits (.enum n) (.int i) = (decide (0 ≤ i) && decide (i.toNat < n)) := by
  simp only [ColType.fits]
  by_cases h : 0 ≤ i
  · have h3 : i.toNat < n ↔ i < (n : Int) := by omega
    simp [h, h3]
  · simp [h]

theorem and_truthy (a b : Val) :
    (if a.truthy then b else Val.nil).truthy = (a.truthy && b.truthy) := by
  cases a.truthy <;> rfl

theorem ite_bool_false_eq_and (a b : Bool) :
    (if a = true then b else false) = (a && b) := by
  cases a <;> rfl

theorem natp_lt_eq_natLt (a b : Val) :
    ((«NATP» a).truthy && (Prim.lt a b).truthy) = natLt a b := by
  rw [natLt_eq_acl2]
  simp [«NATP», «NOT», Bool.and_assoc]

theorem natp_lt_and_eq_natLt (a b : Val) (r : Bool) :
    ((«NATP» a).truthy && ((Prim.lt a b).truthy && r)) = (natLt a b && r) := by
  rw [← Bool.and_assoc, natp_lt_eq_natLt]

theorem natp_lt_left_and_eq_natLt (l : Bool) (a b : Val) :
    ((l && («NATP» a).truthy) && (Prim.lt a b).truthy) = (l && natLt a b) := by
  rw [Bool.and_assoc, natp_lt_eq_natLt]

theorem ubp_truthy (w : Nat) (x : Val) :
    («UNSIGNED-BYTE-P» (.int w) x).truthy = ColType.fits (.uw w) x := by
  rw [fits_uw_eq_acl2]
  have hw0 : ¬(((w : Nat) : Int) < 0) := by omega
  cases x with
  | int i =>
    simp only [«UNSIGNED-BYTE-P», «INTEGER-RANGE-P», «NOT», Prim.integerp, Prim.lt,
      Val.isInt, Val.toInt, Val.truthy_ite, Val.truthy_ofBool, Val.truthy_nil, Val.truthy_t]
    by_cases hi : i < 0
    · have h0 : ¬(0 ≤ i) := by omega
      simp [hw0, hi, h0]
    · have h0 : 0 ≤ i := by omega
      simp [hw0, hi, h0]
  | _ =>
    simp [«UNSIGNED-BYTE-P», «INTEGER-RANGE-P», «NOT», Prim.integerp, Prim.lt, Val.isInt]

theorem ubp_int_truthy (w : Int) (x : Val) (hw : decide (0 ≤ w) = true) :
    («UNSIGNED-BYTE-P» (.int w) x).truthy = ColType.fits (.uw w.toNat) x := by
  have hw0 : 0 ≤ w := of_decide_eq_true hw
  have hw_eq : w = (w.toNat : Int) := by omega
  have h := ubp_truthy w.toNat x
  rw [← hw_eq] at h
  exact h

theorem enum_truthy (m : Nat) (x : Val) :
    ((«NATP» x).truthy && (Prim.lt x (.int m)).truthy) = ColType.fits (.enum m) x := by
  rw [fits_enum_eq_acl2]
  simp [«NATP», «NOT», Bool.and_assoc]

theorem enum_and_truthy (m : Nat) (x : Val) (r : Bool) :
    ((«NATP» x).truthy && ((Prim.lt x (.int m)).truthy && r)) = (ColType.fits (.enum m) x && r) := by
  rw [← Bool.and_assoc, enum_truthy]

theorem enum_int_truthy (m : Int) (x : Val) (hm : decide (0 ≤ m) = true) :
    ((«NATP» x).truthy && (Prim.lt x (.int m)).truthy) = ColType.fits (.enum m.toNat) x := by
  have hm0 : 0 ≤ m := of_decide_eq_true hm
  have hm_eq : m = (m.toNat : Int) := by omega
  have h := enum_truthy m.toNat x
  rw [← hm_eq] at h
  exact h

theorem enum_int_and_truthy (m : Int) (x : Val) (r : Bool) (hm : decide (0 ≤ m) = true) :
    ((«NATP» x).truthy && ((Prim.lt x (.int m)).truthy && r)) = (ColType.fits (.enum m.toNat) x && r) := by
  rw [← Bool.and_assoc, enum_int_truthy m x hm]

theorem enum_int_left_and_truthy (l : Bool) (m : Int) (x : Val) (hm : decide (0 ≤ m) = true) :
    ((l && («NATP» x).truthy) && (Prim.lt x (.int m)).truthy) = (l && ColType.fits (.enum m.toNat) x) := by
  rw [Bool.and_assoc, enum_int_truthy m x hm]

theorem memberEqual_truthy_codeIn (code : Val) (codes : List Val) :
    (Native.memberEqual code (Val.ofList codes)).truthy = codeIn code codes := by
  exact (Combinators.codeIn_eq_memberEqual_truthy code codes).symm

theorem nth_0_eq_car (v : Val) : Native.nth (.int 0) v = v.car := by
  exact Combinators.nth_zero_eq_car v

theorem nth_1_eq_cdr_car (v : Val) : Native.nth (.int 1) v = v.cdr.car := by
  cases v with
  | cons a d => cases d <;> rfl
  | _ => rfl

theorem callFn_world_of_fns (f : String) (args : List Val) (v : Val)
    (hnat : nativeCallNames.contains f = false)
    (hfns : Fn2.Instances.LayerAWorld.fns f args = some v) :
    callFn world f args = .ok v := by
  simp only [callFn, world, nativeCall_none f args hnat, hfns]

theorem not_truthy_true {x : Val} (h : (if x.truthy then Val.nil else Val.t).truthy = true) :
    x.truthy = false := by
  cases hx : x.truthy <;> simp [hx, Val.truthy_nil, Val.truthy_t] at h ⊢

theorem not_truthy_false {x : Val} (h : (if x.truthy then Val.nil else Val.t).truthy = false) :
    x.truthy = true := by
  cases hx : x.truthy <;> simp [hx, Val.truthy_nil, Val.truthy_t] at h ⊢

deriving instance DecidableEq for Except

theorem tupleStobjs_ite (tuple : List String) {n : Nat} (c : Bool) (a b : Fin n → Val) :
    (if c then Combinators.tupleStobjs tuple a else Combinators.tupleStobjs tuple b) =
      Combinators.tupleStobjs tuple (if c then a else b) := by
  cases c <;> rfl

theorem tupleImage_ite {n : Nat} (c : Bool) (a b : Fin n → Val) :
    (if c then Combinators.tupleImage a else Combinators.tupleImage b) =
      Combinators.tupleImage (if c then a else b) := by
  cases c <;> rfl

theorem st_flush_ite (tuple : List String) {n : Nat} (c : Bool) (a b : Fin n → Val)
    (vars : Env) (pending : List (String × Expr)) (next : Option Expr)
    (nd1 nd2 woken : Bool) (lw : Int × Int × Int) :
    { (if c then (⟨Combinators.tupleStobjs tuple a, vars, pending, next, nd1, woken, lw⟩ : St)
            else ⟨Combinators.tupleStobjs tuple b, vars, pending, next, nd1, woken, lw⟩)
      with pending := [], next := none, nextDone := nd2 } =
      ⟨Combinators.tupleStobjs tuple (if c then a else b), vars, [], none, nd2, woken, lw⟩ := by
  cases c <;> rfl

theorem mapM_pend_nil (w : World) (k : Kind) (st : St) :
    (([] : List (String × Expr)).mapM fun (n, e) => do pure (n, ← ev w k st e)) = .ok [] := by rfl

theorem mapM_pend_cons (w : World) (k : Kind) (st : St)
    (n : String) (e : Expr) (rest : List (String × Expr))
    (v : Val) (tail : List (String × Val))
    (hv : ev w k st e = .ok v)
    (ht : (rest.mapM fun (n, e) => do pure (n, ← ev w k st e)) = .ok tail) :
    (((n, e) :: rest).mapM fun (n, e) => do pure (n, ← ev w k st e)) = .ok ((n, v) :: tail) := by
  simp [List.mapM_cons, hv] at ht ⊢
  simp [ht]

theorem foldlM_set_nil (w : World) (pre : String) (s : Val) (acc : Val) :
    (([] : List (String × Val)).foldlM (fun t (n, v) => callFn w (pre ++ n) [s, v, t]) acc) = .ok acc := by rfl

theorem foldlM_set_cons (w : World) (pre : String) (s : Val) (acc v acc' res : Val)
    (n : String) (rest : List (String × Val))
    (h1 : callFn w (pre ++ n) [s, v, acc] = .ok acc')
    (h2 : rest.foldlM (fun t (n, v) => callFn w (pre ++ n) [s, v, t]) acc' = .ok res) :
    (((n, v) :: rest).foldlM (fun t (n, v) => callFn w (pre ++ n) [s, v, t]) acc) = .ok res := by
  simp [List.foldlM_cons, h1, h2]

theorem mapM_ev_nil (w : World) (k : Kind) (st : St) :
    ([] : List Expr).mapM (ev w k st) = .ok [] := by rfl

theorem mapM_ev_cons (w : World) (k : Kind) (st : St)
    (e : Expr) (es : List Expr) (v : Val) (vs : List Val)
    (hv : ev w k st e = .ok v)
    (hvs : es.mapM (ev w k st) = .ok vs) :
    (e :: es).mapM (ev w k st) = .ok (v :: vs) := by
  simp [List.mapM_cons, hv, hvs]

theorem runCore_arm_eq {n : Nat} (k : Kind) (a : Arm) (id budget : Val) (kids : Fin n → Val)
    (fuel : Nat) (ctrlIdx : Nat) (snap slot kindVal ordVal reasonVal noneVal emptyVal : Val)
    (okOut : ArmOut n)
    (htlen : coreTuple.length = n)
    (hctrl : coreTuple.idxOf "FN2-CONTROL" = ctrlIdx)
    (hci : ctrlIdx < n)
    (hsnap : callFn world (k.name ++ "-SNAPSHOT-READ-CODE") [id, Combinators.tupleImage kids] = .ok snap)
    (hslot : snap = .sym ":OK" →
      callFn world "FN2-MACHINE-SLOT" [id, Combinators.tupleImage kids] = .ok slot)
    (hkind : const world ("*" ++ k.name ++ "-KIND*") = .ok kindVal)
    (hord : ordOf world k = ordVal)
    (hreason : const world "*FN2-STOP-REASON-MACHINE-PHASE*" = .ok reasonVal)
    (hnone : const world "*FN2-NONE*" = .ok noneVal)
    (hempty : const world "*FN2-WORK-EMPTY*" = .ok emptyVal)
    (hrun : snap = .sym ":OK" →
      runArm (coreWorld world coreTuple) (coreKind k coreTuple) a false
        ([id, slot, kindVal, ordVal, budget] ++ List.ofFn kids) fuel = .ok okOut.toChild)
    (hout : snap = .sym ":OK" → okOut.ans.length = 4) :
    runCore world coreTuple k a false [id, budget, Combinators.tupleImage kids] fuel =
      .ok (if snap == .sym ":OK" then okOut.toCore
           else Val.ofList [.int 0, emptyVal, .int 0, Val.nil,
             Combinators.tupleImage (Combinators.patchKids kids ctrlIdx
               («FN2-CONTROL-RECORD-STOP» reasonVal (kids ⟨ctrlIdx, hci⟩)))]) := by
  have htl : (Combinators.tupleImage kids).toList = List.ofFn kids := toList_ofList' _
  have hlen_ok : ¬((Combinators.tupleImage kids).toList.length ≠ coreTuple.length) := by
    rw [htl, List.length_ofFn, htlen]; intro h; exact h rfl
  unfold runCore
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, nCore, Bool.false_eq_true,
    ne_eq, not_true_eq_false, ↓reduceIte,
    List.getLastD_cons, List.getLastD_nil, hlen_ok, List.headD_cons, hsnap, except_ok_bind,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.cons_append, List.nil_append]
  by_cases hb : (snap == .sym ":OK") = true
  · have hs : snap = .sym ":OK" := beq_iff_eq.mp hb
    have hr := hrun hs
    simp only [List.cons_append, List.nil_append] at hr
    simp only [hb, ↓reduceIte, hslot hs, hkind, hord, htl, except_ok_bind, hr,
      finish_armOut_false coreTuple okOut htlen (hout hs)]
  · have hbf : (snap == .sym ":OK") = false := Bool.eq_false_iff.mpr hb
    have hstop : callFn world "FN2-CONTROL-RECORD-STOP"
        [reasonVal, Native.nth (.int ctrlIdx) (Combinators.tupleImage kids)] =
        .ok («FN2-CONTROL-RECORD-STOP» reasonVal (kids ⟨ctrlIdx, hci⟩)) := by
      rw [Combinators.nth_tupleImage kids ctrlIdx hci]
      exact callFn_world_of_fns "FN2-CONTROL-RECORD-STOP" _ _ (by decide +kernel)
        («FN2-CONTROL-RECORD-STOP».fns_eq _ _)
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    rw [Combinators.refusedEntry_tupleImage world coreTuple false kids ctrlIdx
      reasonVal _ noneVal emptyVal hctrl hci hreason hstop hnone hempty,
      ← Combinators.tupleImage_patchKids kids ctrlIdx _ hci]
    rfl

theorem runCore_observe_eq {n : Nat} (k : Kind) (a : Arm)
    (id event outcome reason count aux0 aux1 : Val) (kids : Fin n → Val)
    (fuel : Nat) (ctrlIdx : Nat) (snap slot kindVal ordVal reasonVal noneVal emptyVal : Val)
    (okOut : ArmOut n)
    (htlen : coreTuple.length = n)
    (hctrl : coreTuple.idxOf "FN2-CONTROL" = ctrlIdx)
    (hci : ctrlIdx < n)
    (hsnap : callFn world (k.name ++ "-SNAPSHOT-READ-CODE") [id, Combinators.tupleImage kids] = .ok snap)
    (hslot : snap = .sym ":OK" →
      callFn world "FN2-MACHINE-SLOT" [id, Combinators.tupleImage kids] = .ok slot)
    (hkind : const world ("*" ++ k.name ++ "-KIND*") = .ok kindVal)
    (hord : ordOf world k = ordVal)
    (hreason : const world "*FN2-STOP-REASON-MACHINE-OBSERVATION*" = .ok reasonVal)
    (hnone : const world "*FN2-NONE*" = .ok noneVal)
    (hempty : const world "*FN2-WORK-EMPTY*" = .ok emptyVal)
    (hrun : snap = .sym ":OK" →
      runArm (coreWorld world coreTuple) (coreKind k coreTuple) a true
        ([id, slot, kindVal, ordVal, event, outcome, reason, count, aux0, aux1] ++ List.ofFn kids)
        fuel = .ok okOut.toChild)
    (hout : snap = .sym ":OK" → okOut.ans.length = 1) :
    runCore world coreTuple k a true
        [id, event, outcome, reason, count, aux0, aux1, Combinators.tupleImage kids] fuel =
      .ok (if snap == .sym ":OK" then okOut.toCore
           else Val.ofList [noneVal,
             Combinators.tupleImage (Combinators.patchKids kids ctrlIdx
               («FN2-CONTROL-RECORD-STOP» reasonVal (kids ⟨ctrlIdx, hci⟩)))]) := by
  have htl : (Combinators.tupleImage kids).toList = List.ofFn kids := toList_ofList' _
  have hlen_ok : ¬((Combinators.tupleImage kids).toList.length ≠ coreTuple.length) := by
    rw [htl, List.length_ofFn, htlen]; intro h; exact h rfl
  unfold runCore
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, nCore,
    ne_eq, not_true_eq_false, ↓reduceIte,
    List.getLastD_cons, List.getLastD_nil, hlen_ok, List.headD_cons, hsnap, except_ok_bind,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.cons_append, List.nil_append]
  by_cases hb : (snap == .sym ":OK") = true
  · have hs : snap = .sym ":OK" := beq_iff_eq.mp hb
    have hr := hrun hs
    simp only [List.cons_append, List.nil_append] at hr
    simp only [hb, ↓reduceIte, hslot hs, hkind, hord, htl, except_ok_bind, hr,
      finish_armOut_true coreTuple okOut htlen (hout hs)]
  · have hbf : (snap == .sym ":OK") = false := Bool.eq_false_iff.mpr hb
    have hstop : callFn world "FN2-CONTROL-RECORD-STOP"
        [reasonVal, Native.nth (.int ctrlIdx) (Combinators.tupleImage kids)] =
        .ok («FN2-CONTROL-RECORD-STOP» reasonVal (kids ⟨ctrlIdx, hci⟩)) := by
      rw [Combinators.nth_tupleImage kids ctrlIdx hci]
      exact callFn_world_of_fns "FN2-CONTROL-RECORD-STOP" _ _ (by decide +kernel)
        («FN2-CONTROL-RECORD-STOP».fns_eq _ _)
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    rw [Combinators.refusedEntry_tupleImage world coreTuple true kids ctrlIdx
      reasonVal _ noneVal emptyVal hctrl hci hreason hstop hnone hempty,
      ← Combinators.tupleImage_patchKids kids ctrlIdx _ hci]
    rfl

end Fn2.Instances.ServedCertificates.ServedCommon
"""


def emit_served_common(out_dir, fill_world_bodies, widx):
    src = fill_world_bodies(
        as_module(SERVED_COMMON_BODY, expose=True, import_all=CORE_STRING_BODIES, bodies="scan"),
        widx,
    )
    (out_dir / "ServedCommon.lean").write_text(src)


# ---------------------------------------------------------------------------
# Bottom-up IsListN / isListB analyzer for ServedOps.lean
# ---------------------------------------------------------------------------

class TupleShapeAnalyzer:
    """Proves `isListB m (F x0 ... xk) = true` bottom-up over ACL2 logical bodies."""

    def __init__(self, fn_defs, widx):
        self.fn_defs = fn_defs  # name -> (formals, body, stobjs_out, just)
        self.mod_of = widx["mod_of"] if widx else {}
        self.memo = {}     # (name, m) -> bool
        self.busy = set()
        self.order = []    # list of (name, m, deps, rec_info)

    def check_expr(self, t, m, f_self=None, rec_m=None):
        """Return set of `(callee, m)` deps if `t` always evaluates to an `m`-list, else None."""
        if m == 0:
            if isinstance(t, List) and len(t) == 2 and str(t[0]) == "QUOTE" and is_nil(t[1]):
                return set()
            if str(t) == "NIL":
                return set()
            return None
        if not isinstance(t, List) or len(t) == 0:
            return None
        if is_lambda(t[0]):
            # Beta-redex: body determines outer tuple shape unless body is just a formal bound to an m-list!
            formals = [str(v) for v in as_list(t[0][1])]
            actuals = list(t[1:])
            body = t[0][2]
            if isinstance(body, Atom) and str(body) in formals:
                idx = formals.index(str(body))
                return self.check_expr(actuals[idx], m, f_self, rec_m)
            # Substitute any formal bound directly to an actual if body is a formal? Handled above;
            # otherwise walk body with a formal->actual map for direct variable returns:
            return self._check_with_env(body, m, dict(zip(formals, actuals)), f_self, rec_m)
        return self._check_with_env(t, m, {}, f_self, rec_m)

    def _check_with_env(self, t, m, env, f_self, rec_m):
        if m == 0:
            if str(t) == "NIL" or (isinstance(t, List) and len(t) == 2 and str(t[0]) == "QUOTE" and is_nil(t[1])):
                return set()
            if isinstance(t, Atom) and str(t) in env:
                return self._check_with_env(env[str(t)], 0, {}, f_self, rec_m)
            return None
        if isinstance(t, Atom):
            if str(t) in env:
                return self._check_with_env(env[str(t)], m, {}, f_self, rec_m)
            return None
        if not isinstance(t, List) or len(t) == 0:
            return None
        if is_lambda(t[0]):
            formals = [str(v) for v in as_list(t[0][1])]
            actuals = list(t[1:])
            sub_env = {k: self._subst_simple(v, env) for k, v in zip(formals, actuals)}
            merged = dict(env)
            merged.update(sub_env)
            return self._check_with_env(t[0][2], m, merged, f_self, rec_m)
        head = str(t[0])
        args = list(t[1:])
        if head == "RETURN-LAST":
            return self._check_with_env(args[2], m, env, f_self, rec_m)
        if head == "IF":
            d1 = self._check_with_env(args[1], m, env, f_self, rec_m)
            if d1 is None:
                return None
            d2 = self._check_with_env(args[2], m, env, f_self, rec_m)
            if d2 is None:
                return None
            return d1 | d2
        if head == "CONS":
            return self._check_with_env(args[1], m - 1, env, f_self, rec_m)
        if head == "QUOTE":
            vals = as_list(args[0]) if isinstance(args[0], List) else ([] if is_nil(args[0]) else None)
            return set() if (vals is not None and len(vals) == m) else None
        if head == f_self and rec_m == m:
            return {("SELF", m)}
        if head in self.fn_defs and head in self.mod_of:
            if self.ensure(head, m):
                return {(head, m)}
        return None

    def _subst_simple(self, expr, env):
        if isinstance(expr, Atom) and str(expr) in env:
            return env[str(expr)]
        return expr

    def _countdown_info(self, fn_name):
        formals, body, _, just = self.fn_defs[fn_name]
        if just is None:
            return None
        # Check if LayerAWorld emitted a `(NFIX <formal>).nfix + 1` countdown on formal index 0
        if not formals:
            return None
        v0 = formals[0]
        # Verify recursive calls in body pass `(BINARY-+ '-1 <v0>)` or `(BINARY-+ '-1 (NFIX <v0>))`
        ok = [False]
        bad = [False]

        def walk(x):
            if not isinstance(x, List) or not x:
                return
            if str(x[0]) == "QUOTE":
                return
            if is_lambda(x[0]):
                walk(x[0][2])
                for a in x[1:]:
                    walk(a)
                return
            if str(x[0]) == fn_name:
                ok[0] = True
                a0 = show(x[1])
                if a0 not in (
                    f"(BINARY-+ '-1 {v0})",
                    f"(BINARY-+ '-1 (NFIX {v0}))",
                    f"(BINARY-+ (QUOTE -1) {v0})",
                    f"(BINARY-+ (QUOTE -1) (NFIX {v0}))",
                ):
                    bad[0] = True
            for a in x[1:]:
                walk(a)

        walk(body)
        if ok[0] and not bad[0]:
            return 0
        return None

    def ensure(self, fn_name, m):
        key = (fn_name, m)
        if key in self.memo:
            return self.memo[key]
        if fn_name not in self.fn_defs or fn_name not in self.mod_of or key in self.busy:
            return False
        self.busy.add(key)
        formals, body, _, just = self.fn_defs[fn_name]
        # Check if recursive
        calls_self = fn_name in self._raw_calls(body)
        if calls_self:
            mi = self._countdown_info(fn_name)
            if mi is None:
                self.busy.discard(key)
                self.memo[key] = False
                return False
            deps = self.check_expr(body, m, f_self=fn_name, rec_m=m)
            self.busy.discard(key)
            if deps is None:
                self.memo[key] = False
                return False
            deps.discard(("SELF", m))
            self.memo[key] = True
            self.order.append((fn_name, m, sorted(deps), mi))
            return True
        deps = self.check_expr(body, m)
        self.busy.discard(key)
        if deps is None:
            self.memo[key] = False
            return False
        self.memo[key] = True
        self.order.append((fn_name, m, sorted(deps), None))
        return True

    def _raw_calls(self, t):
        out = set()
        stack = [t]
        while stack:
            x = stack.pop()
            if isinstance(x, List) and len(x) > 0:
                if str(x[0]) == "QUOTE":
                    continue
                if is_lambda(x[0]):
                    stack.append(x[0][2])
                    stack.extend(x[1:])
                else:
                    out.add(str(x[0]))
                    stack.extend(x[1:])
        return out


def islist_thm_name(fn_name, m):
    return ident(f"{fn_name}_isListB_{m}")


def islistN_thm_name(fn_name, m):
    return ident(f"{fn_name}_isListN_{m}")


def emit_served_ops(out_dir, targets, fn_defs, fill_world_bodies, widx):
    """`targets`: iterable of `(fn_name, m)` with `m >= 2`."""
    analyzer = TupleShapeAnalyzer(fn_defs, widx)
    proved = set()
    for fn_name, m in sorted(set(targets)):
        if m >= 2 and analyzer.ensure(fn_name, m):
            proved.add((fn_name, m))

    lines = [
        "import Fn2.Instances.ServedCertificates.ServedCommon",
        "",
        "set_option maxHeartbeats 800000",
        "set_option maxRecDepth 100000",
        "set_option linter.unusedVariables false",
        "set_option linter.unusedSimpArgs false",
        "",
        "namespace Fn2.Instances.ServedCertificates.ServedOps",
        "open Fn2.ACL2 Fn2.Arms Fn2.Instances.LayerAWorld Fn2.Instances.ServedCertificates.ServedCommon",
        "",
    ]

    for fn_name, m, deps, rec_mi in analyzer.order:
        formals = fn_defs[fn_name][0]
        binders = " ".join(f"({ident(v)} : Val)" for v in formals)
        args = " ".join(ident(v) for v in formals)
        call_expr = f"({ident(fn_name)}{' ' if args else ''}{args})"
        dep_thms = [islist_thm_name(d_fn, d_m) for d_fn, d_m in deps]
        simp_items = [
            "isListB_ite", "isListB_succ_cons", "isListB_zero_nil", "ite_self",
            "Bool.true_eq_false", *dep_thms,
        ]
        if rec_mi is not None:
            mv = ident(formals[rec_mi])
            go_thm = ident(f"{fn_name}_isListB_{m}_go")
            underscores = " ".join("_" for _ in formals)
            lines += [
                f"theorem {go_thm} (fuel : Nat) : ∀ {binders}, («NFIX» {mv}).nfix < fuel →",
                f"    isListB {m} ({ident(fn_name)}.go fuel {args}) = true := by",
                "  induction fuel with",
                f"  | zero => intro {underscores} hf; omega",
                "  | succ fuel ih =>",
                f"    intro {args} hf",
                f"    dsimp only [{ident(fn_name)}.go]",
                "    split",
                f"    · simp only [{', '.join(simp_items)}]",
                "    · rename_i hcond",
                "      have hlt : («NFIX» (Prim.plus (.int (-1)) " + mv + ")).nfix < fuel := by",
                "        first",
                "        | exact Nat.lt_of_lt_of_le (zp_pred_lt (Bool.eq_false_iff.mpr hcond)) (by omega)",
                "        | exact Nat.lt_of_lt_of_le (zp_or_pred_lt (Bool.eq_false_iff.mpr hcond)) (by omega)",
                f"      simp only [{', '.join(simp_items)}, ih _ {' '.join('_' for _ in formals[1:])} hlt]",
                "",
                f"theorem {islist_thm_name(fn_name, m)} {binders} :",
                f"    isListB {m} {call_expr} = true := by",
                f"  dsimp only [{ident(fn_name)}]",
                f"  exact {go_thm} _ {args} (by first | omega | exact nfix_lt_acl2Count_succ {mv})",
                "",
            ]
        else:
            lines += [
                f"theorem {islist_thm_name(fn_name, m)} {binders} :",
                f"    isListB {m} {call_expr} = true := by",
                f"  simp only [{ident(fn_name)}, {', '.join(simp_items)}]",
                "",
            ]
        lines += [
            f"theorem {islistN_thm_name(fn_name, m)} {binders} :",
            f"    Combinators.IsListN {m} {call_expr} := by",
            f"  exact isListN_of_isListB ({islist_thm_name(fn_name, m)}{' ' if args else ''}{args})",
            "",
        ]

    lines += ["end Fn2.Instances.ServedCertificates.ServedOps", ""]
    src = fill_world_bodies(
        as_module("\n".join(lines), expose=True, import_all=CORE_STRING_BODIES, bodies="scan"),
        widx,
    )
    (out_dir / "ServedOps.lean").write_text(src)
    return proved


# ---------------------------------------------------------------------------
# Mirror of Fn2.Arms expression & step reader
# ---------------------------------------------------------------------------

VOCAB_FNS = {
    "NFIX": 1, "IFIX": 1, "ZP": 1, "ZIP": 1, "NATP": 1, "POSP": 1, "INTEGERP": 1,
    "UNSIGNED-BYTE-P": 2, "FLOOR": 2, "MOD": 2, "ASH": 2, "MIN": 2, "MAX": 2,
    "BINARY-+": 2, "BINARY-*": 2, "UNARY--": 1,
}


class UnsupportedArmError(Exception):
    pass


def parse_col_type(raw_ty):
    if isinstance(raw_ty, List):
        tag = str(raw_ty[0])
        if tag == ":ENUM":
            return ("enum", len(as_list(raw_ty[2])))
        if tag in (":UW", "UW", "UNSIGNED-BYTE", ":UNSIGNED-BYTE"):
            return ("uw", int(str(raw_ty[1])))
        raise UnsupportedArmError(f"unknown column type {show(raw_ty)}")
    w = {
        ":U8": 8, ":U16": 16, ":U32": 32, ":LINK": 32,
        ":U60": 60, ":U64": 64, ":BOOL": 1,
    }.get(str(raw_ty))
    if w is None:
        raise UnsupportedArmError(f"unknown column type {show(raw_ty)}")
    return ("uw", w)


def col_type_lean(ct):
    kind, n = ct
    return f"(.uw {n})" if kind == "uw" else f"(.enum {n})"


def parse_ops(ops_sexp):
    out = {}
    for idx, e in enumerate(as_list(ops_sexp)):
        e = as_list(e)
        name = str(e[0])
        d = plist_dict(e[1:])
        ans = d[":ANSWERS"]
        if is_nil(ans):
            answers = ("none", [])
        elif str(ans) == "T":
            answers = ("open", [])
        else:
            answers = ("list", list(as_list(ans)))
        callee = None if is_nil(d[":CALLEE"]) else str(d[":CALLEE"])
        so = lambda xs: [None if is_nil(x) else str(x) for x in as_list(xs)]
        cf = d.get(":CORE-FORMALS", List([]))
        core_formals = [] if is_nil(cf) else [str(x) for x in as_list(cf)]
        core_in = [] if is_nil(cf) else so(d[":CORE-STOBJS-IN"])
        core_out = [] if is_nil(cf) else so(d[":CORE-STOBJS-OUT"])
        out[name] = {
            "idx": idx,
            "name": name,
            "callee": callee,
            "formals": [str(x) for x in as_list(d[":FORMALS"])],
            "stobjs_in": so(d[":STOBJS-IN"]),
            "stobjs_out": so(d[":STOBJS-OUT"]),
            "answers": answers,
            "faults": list(as_list(d[":FAULTS"])),
            "core_formals": core_formals,
            "core_in": core_in,
            "core_out": core_out,
        }
    return out


def parse_waits(waits_rows):
    out = {}
    for _, row in waits_rows:
        d = plist_dict(as_list(row))
        wkind = str(d[":KIND"]).lstrip(":")
        park = str(d[":PARK"]) if ":PARK" in d and not is_nil(d[":PARK"]) else None
        out[wkind] = park
    return out


def build_kind_info(kd, ki, consts, ops_by_name, waits_by_name, commit_map):
    kn = str(kd[0])
    kp = plist_dict(kd[1:])
    child_form = str(kp[":FORM"]) == ":CHILDREN"
    tuple_names = [str(x) for x in as_list(kp[":TUPLE"])]
    states = [str(x) for x in as_list(kp[":STATES"])]
    phases = {str(as_list(p)[0]): int(str(as_list(p)[1])) for p in as_list(kp[":PHASES"])}
    columns = []
    col_map = {}
    for c in as_list(kp[":COLUMNS"]):
        c = as_list(c)
        cname = str(c[0])
        ct = parse_col_type(c[1])
        columns.append((cname, ct))
        col_map[cname] = ct

    table_cols = [str(as_list(x)[0]) if isinstance(x, List) else str(x) for x in as_list(kp[":TABLE"])]
    stops = [str(x).lstrip(":") for x in as_list(kp[":STOPS"])]
    links = {}
    for l in as_list(kp.get(":LINKS", List([]))):
        l = as_list(l)
        ld = plist_dict(l[1:])
        lname = str(l[0])
        kf = str(ld[":KIND-FIELD"]) if ":KIND-FIELD" in ld and not is_nil(ld[":KIND-FIELD"]) else None
        links[lname] = {
            "name": lname,
            "kind": str(ld[":KIND"]),
            "slot": str(ld[":SLOT"]),
            "gen": str(ld[":GEN"]),
            "kind_field": kf,
            "back": [str(x) for x in as_list(ld.get(":BACK", List([])))],
            "reads": [str(x) for x in as_list(ld.get(":READS", List([])))],
        }

    subarms = {}
    subarm_idx = {}
    for si, e in enumerate(as_list(kp[":SUBARMS"])):
        stag = str(as_list(e)[0])
        subarms[stag] = e
        subarm_idx[stag] = si

    col_names = [c for c, _ in columns]
    rfield = next((f for f in ("WORD", "REPLY", "REASON") if f in col_names), None)
    rsub = "REFUSE" in subarms

    return {
        "name": kn,
        "ki": ki,
        "child_form": child_form,
        "tuple": tuple_names,
        "states": states,
        "phases": phases,
        "columns": columns,
        "col_map": col_map,
        "table": table_cols,
        "stops": stops,
        "links": links,
        "subarms": subarms,
        "subarm_idx": subarm_idx,
        "refuse_field": rfield,
        "refuse_sub": rsub,
        "consts": consts,
        "ops": ops_by_name,
        "waits": waits_by_name,
        "commit_map": commit_map,
    }


# ---------------------------------------------------------------------------
# Exact Python mirror of `Fn2.Arms` Term / Step / ArmDecl reader
# ---------------------------------------------------------------------------

def term_free_vars(t):
    tag = t[0]
    if tag == "var":
        return [t[1]]
    if tag == "quote":
        return []
    if tag == "app":
        out = []
        for a in t[2]:
            out.extend(term_free_vars(a))
        return out
    if tag == "lam":
        out = []
        for a in t[3]:
            out.extend(term_free_vars(a))
        return out
    return []


def erase_dups(xs):
    seen = set()
    out = []
    for x in xs:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def t_if(c, a, b):
    return ("app", "IF", [c, a, b])


def t_not(a):
    return t_if(a, ("quote", Atom("NIL")), ("quote", Atom("T")))


def is_eqlable_sexp(x):
    if isinstance(x, Str) or isinstance(x, List):
        return False
    return True


def read_expr_ast(x, kinfo, core_mode):
    """Exact mirror of `Fn2.Arms.readExpr` returning `('var', s) | ('quote', sexp) | ('app', f, args) | ('lam', fs, body, actuals)`."""
    kn = kinfo["name"]
    tuple_names = kinfo["core_tuple"] if core_mode else kinfo["tuple"]
    if isinstance(x, Str):
        return ("quote", x)
    if isinstance(x, Atom):
        s = str(x)
        if re.fullmatch(r"[+-]?\d+", s) or s in ("T", "NIL") or s.startswith(":"):
            return ("quote", x)
        if s == "ROW-SLOT":
            return ("var", "SLOT")
        if s == f"*{kn}-KIND*":
            return ("var", "KIND")
        if s == f"*{kn}-ADMISSION-ORDINAL*":
            return ("var", "ORDINAL")
        if len(s) > 2 and s.startswith("*") and s.endswith("*"):
            if s not in kinfo["consts"]:
                raise UnsupportedArmError(f"missing constant {s}")
            return ("quote", kinfo["consts"][s])
        return ("var", s)
    if not isinstance(x, List) or len(x) == 0 or not isinstance(x[0], Atom):
        raise UnsupportedArmError(f"invalid expression {show(x)}")
    f = str(x[0])
    args = list(x[1:])
    rd = lambda e: read_expr_ast(e, kinfo, core_mode)
    rds = lambda es: [rd(e) for e in es]

    def fold_r(fn_name, es):
        ts = rds(es)
        acc = ts[-1]
        for a in reversed(ts[:-1]):
            acc = ("app", fn_name, [a, acc])
        return acc

    if f == "QUOTE":
        return ("quote", args[0])
    if f == "IF":
        return ("app", "IF", rds(args))
    if f == "+":
        if len(args) == 0:
            return ("quote", Atom("0"))
        if len(args) == 1:
            return ("app", "BINARY-+", [("quote", Atom("0")), rd(args[0])])
        return fold_r("BINARY-+", args)
    if f == "*":
        if len(args) == 0:
            return ("quote", Atom("1"))
        if len(args) == 1:
            return ("app", "BINARY-*", [("quote", Atom("1")), rd(args[0])])
        return fold_r("BINARY-*", args)
    if f == "-":
        if len(args) == 1:
            return ("app", "UNARY--", [rd(args[0])])
        return ("app", "BINARY-+", [rd(args[0]), ("app", "UNARY--", [rd(args[1])])])
    if f == "1+":
        return ("app", "BINARY-+", [("quote", Atom("1")), rd(args[0])])
    if f == "1-":
        return ("app", "BINARY-+", [("quote", Atom("-1")), rd(args[0])])
    if f == "<":
        return ("app", "<", rds(args))
    if f == ">":
        ts = rds(args)
        return ("app", "<", [ts[1], ts[0]])
    if f == "<=":
        ts = rds(args)
        return t_not(("app", "<", [ts[1], ts[0]]))
    if f == ">=":
        ts = rds(args)
        return t_not(("app", "<", [ts[0], ts[1]]))
    if f in ("=", "EQ", "EQL", "EQUAL"):
        return ("app", "EQUAL", rds(args))
    if f == "/=":
        return t_not(("app", "EQUAL", rds(args)))
    if f in ("NOT", "NULL"):
        return t_not(rd(args[0]))
    if f == "AND":
        if not args:
            return ("quote", Atom("T"))
        ts = rds(args)
        acc = ts[-1]
        for a in reversed(ts[:-1]):
            acc = t_if(a, acc, ("quote", Atom("NIL")))
        return acc
    if f == "OR":
        if not args:
            return ("quote", Atom("NIL"))
        ts = rds(args)
        acc = ts[-1]
        for a in reversed(ts[:-1]):
            acc = t_if(a, a, acc)
        return acc
    if f == "COND":
        cls = []
        for c in args:
            cs = list(as_list(c))
            if len(cs) == 1:
                tt = rd(cs[0])
                cls.append((tt, tt))
            else:
                cls.append((rd(cs[0]), rd(cs[1])))
        acc = ("quote", Atom("NIL"))
        for tc, ec in reversed(cls):
            acc = t_if(tc, ec, acc)
        return acc
    if f == "CASE":
        key_x = args[0]
        key_t = rd(key_x)
        bound = not (isinstance(key_x, Atom) and not re.fullmatch(r"[+-]?\d+", str(key_x)))
        key = ("var", "CASE-DO-NOT-USE-ELSEWHERE") if bound else key_t

        def go_case(clauses):
            if not clauses:
                return ("quote", Atom("NIL"))
            cl = list(as_list(clauses[0]))
            keys, body_x = cl[0], cl[1]
            more = clauses[1:]
            if isinstance(keys, Atom) and str(keys) in ("OTHERWISE", "T"):
                return rd(body_x)
            if is_nil(keys):
                return go_case(more)
            if isinstance(keys, List):
                return t_if(("app", "MEMBER-EQUAL", [key, ("quote", keys)]), rd(body_x), go_case(more))
            return t_if(("app", "EQUAL", [key, ("quote", keys)]), rd(body_x), go_case(more))

        body = go_case(args[1:])
        if bound:
            fv = erase_dups([v for v in term_free_vars(body) if v != "CASE-DO-NOT-USE-ELSEWHERE"])
            return ("lam", ["CASE-DO-NOT-USE-ELSEWHERE"] + fv, body, [key_t] + [("var", v) for v in fv])
        return body
    if f in ("LOGAND", "LOGIOR"):
        if not args:
            return ("quote", Atom("-1" if f == "LOGAND" else "0"))
        if len(args) == 1:
            return rd(args[0])
        return fold_r("BINARY-" + f, args)
    if f == "MV":
        ts = rds(args)
        acc = ("quote", Atom("NIL"))
        for a in reversed(ts):
            acc = ("app", "CONS", [a, acc])
        return acc
    if f == "PROG2$":
        ts = rds(args)
        return ts[1]
    if f in ("MEMBER-EQ", "MEMBER-EQUAL"):
        return ("app", "MEMBER-EQUAL", rds(args))
    if f == ":LIVE":
        lname = str(args[0])
        link = kinfo["links"][lname]
        fn = f"{kn}-LINK-{lname}-LIVE-P"
        r_args = [("var", f"ROW-{link['slot']}"), ("var", f"ROW-{link['gen']}")]
        if link["kind_field"]:
            r_args.append(("var", f"ROW-{link['kind_field']}"))
        if len(link["back"]) >= 1:
            r_args.append(("var", "ID"))
        if len(link["back"]) >= 2:
            r_args.append(("var", "ROW-GENERATION"))
        if core_mode:
            return ("app", fn + "@CORE", r_args + [("var", c) for c in tuple_names])
        return ("app", fn, r_args + [("var", link["kind"]), ("var", "FN2-MACHINES")])
    if f == ":READ":
        lname, fld = str(args[0]), str(args[1])
        link = kinfo["links"][lname]
        fn = f"{kn}-LINK-{lname}-{fld}"
        r_args = [("var", f"ROW-{link['slot']}")]
        if core_mode:
            return ("app", fn + "@CORE", r_args + [("var", c) for c in tuple_names])
        return ("app", fn, r_args + [("var", link["kind"]), ("var", "FN2-MACHINES")])
    if f in VOCAB_FNS:
        return ("app", f, rds(args))
    if f in kinfo["ops"]:
        op_info = kinfo["ops"][f]
        if op_info["callee"] is not None:
            vals_len = 0
            for s in op_info["stobjs_in"]:
                if s is None:
                    vals_len += 1
                else:
                    break
            kid_names = [s for s in op_info["stobjs_in"][vals_len:] if s is not None]
            return ("app", op_info["callee"], rds(args) + [("var", c) for c in kid_names])
        elif core_mode and op_info["core_formals"]:
            vals_len = 0
            for s in op_info["core_in"]:
                if s is None:
                    vals_len += 1
                else:
                    break
            return ("app", f + "@CORE", rds(args) + [("var", c) for c in tuple_names])
    raise UnsupportedArmError(f"unsupported expression head {f} in {show(x)}")


def read_next_ast(n, kinfo, core_mode):
    """Exact mirror of `Fn2.Arms.readNext`."""
    if isinstance(n, Atom):
        s = str(n)
        if s.startswith(":"):
            if s not in kinfo["phases"]:
                raise UnsupportedArmError(f"unknown phase {s}")
            return ("quote", Atom(str(kinfo["phases"][s])))
        if s.startswith("ROW-"):
            return ("var", s)
        raise UnsupportedArmError(f"unsupported :next atom {s}")
    xs = list(as_list(n))
    head = str(xs[0])
    if head == ":IF":
        return t_if(
            read_expr_ast(xs[1], kinfo, core_mode),
            read_next_ast(xs[2], kinfo, core_mode),
            read_next_ast(xs[3], kinfo, core_mode),
        )
    if head == ":CASE":
        key = ("var", str(xs[1]))
        clauses = xs[2:]

        def go_next_case(cls):
            cl = list(as_list(cls[0]))
            cs, rhs = cl[0], cl[1]
            if isinstance(cs, Atom) and str(cs) == ":OTHERWISE":
                return read_next_ast(rhs, kinfo, core_mode)
            codes_sexp = List(as_list(cs))
            return t_if(
                ("app", "MEMBER-EQUAL", [key, ("quote", codes_sexp)]),
                read_next_ast(rhs, kinfo, core_mode),
                go_next_case(cls[1:]),
            )

        return go_next_case(clauses)
    raise UnsupportedArmError(f"unsupported :next form {show(n)}")


def term_to_lean(t):
    tag = t[0]
    if tag == "var":
        return f"(Term.var {lean_str(t[1])})"
    if tag == "quote":
        return f"(Term.quote ({val(t[1])}))"
    if tag == "app":
        args_s = ", ".join(term_to_lean(a) for a in t[2])
        return f"(Term.app {lean_str(t[1])} [{args_s}])"
    if tag == "lam":
        fs_s = ", ".join(lean_str(f) for f in t[1])
        as_s = ", ".join(term_to_lean(a) for a in t[3])
        return f"(Term.lam [{fs_s}] {term_to_lean(t[2])} [{as_s}])"
    raise ValueError(tag)



def read_call_ast(c_sexp):
    xs = list(as_list(c_sexp))
    op_name = str(xs[0])
    rest = xs[1:]
    pos = []
    i = 0
    while i < len(rest):
        if isinstance(rest[i], Atom) and str(rest[i]).startswith(":"):
            break
        pos.append(rest[i])
        i += 1
    keys = []
    while i + 1 < len(rest):
        keys.append((str(rest[i]), rest[i + 1]))
        i += 2
    return {"op": op_name, "args": pos, "keys": keys}


def call_to_lean(c):
    args_s = ", ".join(val(a) for a in c["args"])
    keys_s = ", ".join(f"({lean_str(k)}, {val(v)})" for k, v in c["keys"])
    return f"(Call.mk {lean_str(c['op'])} [{args_s}] [{keys_s}])"


def opt_expr_lean(x):
    return "none" if x is None else f"(some ({val(x)}))"


def opt_str_lean(s):
    return "none" if s is None else f"(some {lean_str(s)})"


def expand_refuse_sexp(s, kinfo):
    if isinstance(s, List) and len(s) == 2 and str(s[0]) == ":REFUSE" and kinfo["refuse_field"]:
        w = s[1]
        rf = kinfo["refuse_field"]
        set_s = List([Atom(":SET"), List([Atom(rf), w])])
        if kinfo["refuse_sub"]:
            return [set_s, List([Atom(":GOTO"), Atom("REFUSE")])]
        return [
            set_s,
            List([Atom(":NEXT"), Atom(":REFUSED")]),
            List([Atom(":CHARGE"), Atom(":STEPS"), Atom("*FN2-WORK-TRANSITION*"), Atom(":RUNNABLE"), Atom("T")]),
        ]
    return [s]


def read_steps_ast(ss_sexp, kinfo, area, tag):
    """Exact mirror of `Fn2.Arms.readSteps`."""
    if is_nil(ss_sexp):
        return []
    raw_list = list(as_list(ss_sexp))
    ref_exp = []
    for s in raw_list:
        ref_exp.extend(expand_refuse_sexp(s, kinfo))
    flat = []
    for s in ref_exp:
        if isinstance(s, List) and len(s) > 0 and str(s[0]) == ":COMMIT":
            ckey = (kinfo["name"], area, tag, show(s))
            if ckey not in kinfo["commit_map"]:
                raise UnsupportedArmError(f"missing commit expansion for {ckey[:3]}")
            flat.extend(kinfo["commit_map"][ckey])
        else:
            flat.append(s)
    return [read_step_one(s, kinfo, area, tag) for s in flat]


def read_codes_ast(cs_sexp):
    if isinstance(cs_sexp, Atom) and str(cs_sexp) == ":OTHERWISE":
        return None
    return list(as_list(cs_sexp))


def read_step_one(s, kinfo, area, tag):
    xs = list(as_list(s))
    h = str(xs[0])
    a = xs[1:]
    if h == ":LET":
        return ("let", str(a[0]), a[1])
    if h == ":SET":
        ps = []
        for p in a:
            pl = list(as_list(p))
            ps.append((str(pl[0]), pl[1]))
        return ("set", ps)
    if h == ":NEXT":
        return ("next", a[0])
    if h == ":DO":
        vs = [str(v) for v in as_list(a[0])]
        call = read_call_ast(a[1])
        opts = a[2:]
        when_raw = plist_get(opts, ":WHEN")
        when_ = None if (when_raw is None or is_nil(when_raw)) else when_raw
        ag = plist_has(opts, ":ACCEPT")
        acc_raw = plist_get(opts, ":ACCEPT")
        acc = [] if (acc_raw is None or is_nil(acc_raw)) else list(as_list(acc_raw))
        else_raw = plist_get(opts, ":ELSE")
        else_ = [] if (else_raw is None or is_nil(else_raw)) else list(as_list(else_raw))
        case_raw = plist_get(opts, ":CASE")
        cases = []
        if case_raw is not None and not is_nil(case_raw):
            for c in as_list(case_raw):
                cl = list(as_list(c))
                cases.append((read_codes_ast(cl[0]), read_steps_ast(List(cl[1:]), kinfo, area, tag)))
        return ("do", vs, call, ag, acc, when_, else_, cases)
    if h == ":ISSUE":
        call = read_call_ast(a[0])
        opts = a[1:]
        ok_s = read_steps_ast(plist_get(opts, ":OK", List([])), kinfo, area, tag)
        rf_s = read_steps_ast(plist_get(opts, ":REFUSED", List([])), kinfo, area, tag)
        return ("issue", call, ok_s, rf_s)
    if h == ":REPEAT":
        raise UnsupportedArmError("repeat step unsupported")
    if h == ":WAKE-ROW":
        return ("wake_row", a[0])
    if h == ":IF":
        return ("if", a[0], read_steps_ast(a[1], kinfo, area, tag), read_steps_ast(a[2], kinfo, area, tag))
    if h == ":COND":
        cls = []
        for c in a:
            cl = list(as_list(c))
            cls.append((cl[0], read_steps_ast(List(cl[1:]), kinfo, area, tag)))
        return ("cond", cls)
    if h == ":CASE":
        key = a[0]
        arms = []
        for c in a[1:]:
            cl = list(as_list(c))
            arms.append((read_codes_ast(cl[0]), read_steps_ast(List(cl[1:]), kinfo, area, tag)))
        return ("case", key, arms)
    if h == ":CHARGE":
        return (
            "charge",
            plist_get(a, ":BYTES"),
            plist_get(a, ":STEPS"),
            plist_get(a, ":DESCRIPTORS"),
            plist_get(a, ":RUNNABLE"),
        )
    if h == ":WAIT":
        pl = a[1:]
        return ("wait", plist_get(pl, ":BYTES"), plist_get(pl, ":STEPS"))
    if h == ":PARK":
        w = str(a[0])
        wait_name = w.lstrip(":")
        rest = a[1:]
        if w == ":TAKEN":
            t_kind = str(rest[0])
            pl = rest[1:]
            return ("park", wait_name, None, t_kind, plist_get(pl, ":STEPS"), [])
        if w in (":ADMISSION", ":POOL"):
            arg = rest[0]
            pl = rest[1:]
            return ("park", wait_name, arg, None, plist_get(pl, ":STEPS"), [])
        ks = []
        i = 0
        while i + 1 < len(rest):
            if str(rest[i]) != ":STEPS":
                ks.append((str(rest[i]), rest[i + 1]))
            i += 2
        return ("park", wait_name, None, None, plist_get(rest, ":STEPS"), ks)
    if h == ":STOP":
        reason = str(a[0]).lstrip(":")
        pl = a[1:]
        return ("stop", reason, plist_get(pl, ":STEPS"))
    if h in (":HALT", ":IDLE", ":YIELD", ":WAKE", ":NOWAKE"):
        return (h[1:].lower(),)
    if h == ":GOTO":
        return ("goto", str(a[0]))
    raise UnsupportedArmError(f"unknown step {show(s)}")


def read_arm_decl_ast(decl_sexp, kinfo, area, tag):
    """Exact mirror of `Fn2.Arms.Arm.read`."""
    xs = list(as_list(decl_sexp))
    from_ = []
    refusal_raw = Atom("NIL")
    while len(xs) >= 2 and isinstance(xs[0], Atom) and str(xs[0]) in (":FROM", ":ON-REFUSAL"):
        if str(xs[0]) == ":FROM":
            from_ = [str(x) for x in as_list(xs[1])]
        else:
            refusal_raw = xs[1]
        xs = xs[2:]
    if isinstance(refusal_raw, List) and len(refusal_raw) > 0 and isinstance(refusal_raw[0], Atom) and str(refusal_raw[0]).startswith(":"):
        refusal_raw = List([refusal_raw])
    on_refusal = read_steps_ast(refusal_raw, kinfo, area, tag)
    steps = read_steps_ast(List(xs), kinfo, area, tag)
    return {"from": from_, "on_refusal": on_refusal, "steps": steps}


def codes_opt_lean(cs):
    if cs is None:
        return "none"
    return f"(some [{', '.join(val(c) for c in cs)}])"


def step_to_lean(st):
    h = st[0]
    if h == "let":
        return f"(Step.let_ {lean_str(st[1])} ({val(st[2])}))"
    if h == "set":
        ps = ", ".join(f"({lean_str(f)}, {val(e)})" for f, e in st[1])
        return f"(Step.set [{ps}])"
    if h == "next":
        return f"(Step.next ({val(st[1])}))"
    if h == "do":
        _, vs, call, ag, acc, when_, else_, cases = st
        vs_s = ", ".join(lean_str(v) for v in vs)
        acc_s = ", ".join(val(c) for c in acc)
        el_s = ", ".join(val(e) for e in else_)
        cs_s = ", ".join(f"({codes_opt_lean(cs)}, [{', '.join(step_to_lean(x) for x in bs)}])" for cs, bs in cases)
        return (
            f"(Step.do_ [{vs_s}] {call_to_lean(call)} {'true' if ag else 'false'} "
            f"[{acc_s}] {opt_expr_lean(when_)} [{el_s}] [{cs_s}])"
        )
    if h == "issue":
        _, call, ok_s, rf_s = st
        ok_l = ", ".join(step_to_lean(x) for x in ok_s)
        rf_l = ", ".join(step_to_lean(x) for x in rf_s)
        return f"(Step.issue {call_to_lean(call)} [{ok_l}] [{rf_l}])"
    if h == "wake_row":
        return f"(Step.wakeRow ({val(st[1])}))"
    if h == "if":
        a_l = ", ".join(step_to_lean(x) for x in st[2])
        b_l = ", ".join(step_to_lean(x) for x in st[3])
        return f"(Step.if_ ({val(st[1])}) [{a_l}] [{b_l}])"
    if h == "cond":
        cl_l = ", ".join(f"({val(c)}, [{', '.join(step_to_lean(x) for x in bs)}])" for c, bs in st[1])
        return f"(Step.cond [{cl_l}])"
    if h == "case":
        ar_l = ", ".join(f"({codes_opt_lean(cs)}, [{', '.join(step_to_lean(x) for x in bs)}])" for cs, bs in st[2])
        return f"(Step.case_ ({val(st[1])}) [{ar_l}])"
    if h == "charge":
        return f"(Step.charge {opt_expr_lean(st[1])} {opt_expr_lean(st[2])} {opt_expr_lean(st[3])} {opt_expr_lean(st[4])})"
    if h == "wait":
        return f"(Step.wait {opt_expr_lean(st[1])} {opt_expr_lean(st[2])})"
    if h == "park":
        _, wn, arg, tk, stp, ks = st
        ks_s = ", ".join(f"({lean_str(k)}, {val(v)})" for k, v in ks)
        return f"(Step.park {lean_str(wn)} {opt_expr_lean(arg)} {opt_str_lean(tk)} {opt_expr_lean(stp)} [{ks_s}])"
    if h == "stop":
        return f"(Step.stop {lean_str(st[1])} {opt_expr_lean(st[2])})"
    if h in ("halt", "idle", "yield", "wake", "nowake"):
        return f"Step.{h}"
    if h == "goto":
        return f"(Step.goto {lean_str(st[1])})"
    raise ValueError(h)


def arm_decl_to_lean(d):
    fr_s = ", ".join(lean_str(x) for x in d["from"])
    rf_s = ", ".join(step_to_lean(x) for x in d["on_refusal"])
    st_s = ", ".join(step_to_lean(x) for x in d["steps"])
    return f"(ArmDecl.mk [{fr_s}] [{rf_s}] [{st_s}])"


# ---------------------------------------------------------------------------
# Proof builder: KindCommon, Subarms, ArmProofBuilder, RootProof
# ---------------------------------------------------------------------------

def static_fits(ct, val_lean):
    """Check if `ColType.fits ct val_lean` is statically `true` (e.g. `.int k` or `if` of `.int k`s)."""
    kind, bound = ct
    hi = (1 << bound) if kind == "uw" else bound
    m = re.fullmatch(r"\(?(?:Val\.int|\.int)\s+\(?(-?\d+)\)?\)?", val_lean.strip())
    if m:
        v = int(m.group(1))
        return 0 <= v < hi
    return False


def static_phase_expr_fits(t_ast, n_states):
    """Return True if every leaf of a `:next` Term AST is an in-bounds phase literal."""
    if t_ast[0] == "quote" and isinstance(t_ast[1], Atom):
        s = str(t_ast[1])
        if re.fullmatch(r"[+-]?\d+", s):
            v = int(s)
            return 0 <= v < n_states
    if t_ast[0] == "app" and t_ast[1] == "IF" and len(t_ast[2]) == 3:
        return (
            static_phase_expr_fits(t_ast[2][1], n_states)
            and static_phase_expr_fits(t_ast[2][2], n_states)
        )
    return False


def emit_kind_common(out_dir, kinfo, core_layout, fn_defs, fill_world_bodies, widx):
    """Emit `Kind<ki>Common.lean` with entry snapshot, `rowReads`, `ROW-*`, and `<KN>-WRITE+...` lemmas."""
    ki = kinfo["ki"]
    kn = kinfo["name"]
    n_core = len(core_layout)
    own_core_idx = core_layout.index(kn)
    dir_core_idx = core_layout.index("FN2-MACHINES")
    ctrl_core_idx = core_layout.index("FN2-CONTROL")
    kind_num = int(str(kinfo["consts"][f"*{kn}-KIND*"]))
    stop_write_code = int(str(kinfo["consts"]["*FN2-STOP-REASON-MACHINE-WRITE*"]))

    # Find core table getter/updater names from `fn_defs[f"{kn}-SNAPSHOT-READ-CODE"]` or convention
    own_table_fn = f"{kn}-TABLE" if f"{kn}-TABLE" in fn_defs else f"FN2-CORE-{kn[4:]}"
    upd_own_table_fn = f"UPDATE-{own_table_fn}"

    lines = [
        "import Fn2.Instances.ServedCertificates.ServedCommon",
        "import Fn2.Instances.ServedCertificates.ServedOps",
        "",
        "set_option maxHeartbeats 1600000",
        "set_option maxRecDepth 100000",
        "set_option linter.unusedVariables false",
        "set_option linter.unusedSimpArgs false",
        "",
        f"namespace Fn2.Instances.ServedCertificates.Kind{ki}Common",
        "open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core Fn2.Instances.ServedKinds Fn2.Instances.LayerAWorld",
        "open Fn2.Instances.ServedCertificates.ServedCommon Fn2.Instances.ServedCertificates.ServedOps",
        "",
        f"def kObj : Kind := kinds[{ki}]!",
        "",
        "theorem coreTuple_nodup : Combinators.nodupB coreTuple = true := by decide +kernel",
        "",
    ]
    if kinfo["child_form"]:
        lines += [
            "theorem childTuple_nodup : Combinators.nodupB kObj.tuple = true := by decide +kernel",
            "",
        ]

    # Snapshot entry theorems (used by all `runCore` roots of this kind)
    lines += [
        f"theorem snapshot_parts (id core : Val)",
        f"    (h : {ident(kn + '-SNAPSHOT-READ-CODE')} id core = .sym \":OK\") :",
        f"    «FN2-MACHINE-PHASE-READ-CODE» id core = .sym \":OK\" ∧",
        f"    «FN2-MACHINE-KIND» id core = .int {kind_num} := by",
        f"  unfold {ident(kn + '-SNAPSHOT-READ-CODE')} at h",
        "  dsimp only at h",
        "  by_cases hp : «FN2-MACHINE-PHASE-READ-CODE» id core = .sym \":OK\"",
        "  · simp [«NOT», «EQ», Prim.equal, hp] at h; exact ⟨hp, h⟩",
        "  · simp [«NOT», «EQ», Prim.equal, hp] at h",
        "",
        f"theorem snapshot_bounds (id core : Val)",
        f"    (h : {ident(kn + '-SNAPSHOT-READ-CODE')} id core = .sym \":OK\") :",
        "    («NATP» id).truthy = true ∧",
        "    (Prim.lt id («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» core))).truthy = true ∧",
        "    («NATP» («FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core))).truthy = true ∧",
        f"    (Prim.lt («FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core))",
        f"      ({ident(kn + '-ROWS')} ({ident(own_table_fn)} core))).truthy = true := by",
        "  obtain ⟨hp, hk⟩ := snapshot_parts id core h",
        "  have hi : («FN2-MACHINE-IDP» id core).truthy = true := by",
        "    by_cases hi : («FN2-MACHINE-IDP» id core).truthy = true",
        "    · exact hi",
        "    · simp [«FN2-MACHINE-PHASE-READ-CODE», «NOT», hi] at hp",
        "  have hid : («NATP» id).truthy = true ∧",
        "      (Prim.lt id («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» core))).truthy = true := by",
        "    simpa [«FN2-MACHINE-IDP», Fn2.Arms.Val.truthy_ite] using hi",
        "  have hs : «FN2-MACHINE-SLOT» id core = «FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core) := by",
        "    simp [«FN2-MACHINE-SLOT», «FN2-MACHINE-SLOT-READ-CODE», hi, «EQ», Prim.equal]",
        "  simp [«FN2-MACHINE-PHASE-READ-CODE», «NOT», hi, hk, «EQL», Prim.equal, Val.ofBool, hs] at hp",
        "  exact ⟨hid.1, hid.2, hp⟩",
        "",
        f"theorem entry_bounds (id : Val) (kids : Fin {n_core} → Val)",
        f"    (h : {ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) = .sym \":OK\") :",
        f"    «FN2-MACHINE-SLOT» id (Combinators.tupleImage kids) = «FN2-MACHINES-SLOT» id (kids ⟨{dir_core_idx}, by decide⟩) ∧",
        f"    natLt («FN2-MACHINE-SLOT» id (Combinators.tupleImage kids)) ({ident(kn + '-ROWS')} (kids ⟨{own_core_idx}, by decide⟩)) = true ∧",
        f"    natLt id («FN2-MACHINES-ROWS» (kids ⟨{dir_core_idx}, by decide⟩)) = true := by",
        "  obtain ⟨hi, hr, hs, hb⟩ := snapshot_bounds id (Combinators.tupleImage kids) h",
        "  have hid : («FN2-MACHINE-IDP» id (Combinators.tupleImage kids)).truthy = true := by",
        "    simp [«FN2-MACHINE-IDP», hi, hr]",
        f"  have hdir_eq : «FN2-CORE-MACHINES» (Combinators.tupleImage kids) = kids ⟨{dir_core_idx}, by decide⟩ := by",
        f"    simpa [«FN2-CORE-MACHINES»] using Combinators.nth_tupleImage kids {dir_core_idx} (by decide)",
        f"  have hown_eq : {ident(own_table_fn)} (Combinators.tupleImage kids) = kids ⟨{own_core_idx}, by decide⟩ := by",
        f"    simpa [{ident(own_table_fn)}] using Combinators.nth_tupleImage kids {own_core_idx} (by decide)",
        "  have hslot : «FN2-MACHINE-SLOT» id (Combinators.tupleImage kids) =",
        f"      «FN2-MACHINES-SLOT» id (kids ⟨{dir_core_idx}, by decide⟩) := by",
        "    simp [«FN2-MACHINE-SLOT», «FN2-MACHINE-SLOT-READ-CODE», hid, «EQ», Prim.equal, hdir_eq]",
        "  have hown : natLt («FN2-MACHINE-SLOT» id (Combinators.tupleImage kids))",
        f"      ({ident(kn + '-ROWS')} (kids ⟨{own_core_idx}, by decide⟩)) = true := by",
        "    rw [← natp_lt_eq_natLt, hslot, ← hdir_eq, ← hown_eq, hs, hb]; rfl",
        f"  have hdir : natLt id («FN2-MACHINES-ROWS» (kids ⟨{dir_core_idx}, by decide⟩)) = true := by",
        "    rw [← natp_lt_eq_natLt, ← hdir_eq, hi, hr]; rfl",
        "  exact ⟨hslot, hown, hdir⟩",
        "",
    ]

    # Core rowReads theorem
    col_names = [c for c, _ in kinfo["columns"]]
    col_names_lean = "[" + ", ".join(lean_str(c) for c in col_names) + "]"
    rcases_pat = " | ".join(["rfl"] * len(col_names))

    def emit_row_reads_thm(thm_name, w_expr, k_expr, tup_expr, n_tup, own_i, dir_i, is_core):
        read_fn_name = f"{thm_name}_val"
        read_arms = []
        row_pairs = []
        call_proofs = []
        for c in col_names:
            if c in DIRECTORY_FIELDS:
                fn_c = f"FN2-MACHINES-{c}"
                val_c = f"({ident(fn_c)} id (kids ⟨{dir_i}, by decide⟩))"
                args_c = f"[id, kids ⟨{dir_i}, by decide⟩]"
            else:
                fn_c = f"{kn}-{c}"
                val_c = f"({ident(fn_c)} slot (kids ⟨{own_i}, by decide⟩))"
                args_c = f"[slot, kids ⟨{own_i}, by decide⟩]"
            read_arms.append(f"  | {lean_str(c)} => {val_c}")
            row_pairs.append(f"({lean_str('ROW-' + c)}, {val_c})")
            if is_core:
                call_proofs.append(
                    f"  · dsimp only [{read_fn_name}]\n"
                    f"    exact (Combinators.callFn_core_plain world coreTuple {lean_str(fn_c)} {args_c} (by decide +kernel)).trans\n"
                    f"      (callFn_world_of_fns {lean_str(fn_c)} {args_c} _ (by decide +kernel) ({ident(fn_c)}.fns_eq _ _))"
                )
            else:
                call_proofs.append(
                    f"  · dsimp only [{read_fn_name}]\n"
                    f"    exact callFn_world_of_fns {lean_str(fn_c)} {args_c} _ (by decide +kernel) ({ident(fn_c)}.fns_eq _ _)"
                )
        read_arms.append("  | _ => Val.nil")
        lines.extend([
            f"def {read_fn_name} (id slot : Val) (kids : Fin {n_tup} → Val) : String → Val",
            *read_arms,
            "",
            f"def {thm_name}_env (id slot : Val) (kids : Fin {n_tup} → Val) : Env := [",
            "  " + ",\n  ".join(row_pairs) + "]",
            "",
            f"theorem {thm_name} (id slot : Val) (kids : Fin {n_tup} → Val) :",
            f"    rowReads {w_expr} {k_expr} (Combinators.tupleStobjs {tup_expr} kids) id slot =",
            f"      .ok ({thm_name}_env id slot kids) := by",
            f"  refine (Combinators.rowReads_tupleStobjs {w_expr} {k_expr} {tup_expr} kids id slot {own_i} {dir_i}",
            f"    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)",
            f"    ({read_fn_name} id slot kids) ?_).trans rfl",
            "  intro c hc",
            f"  change c ∈ {col_names_lean} at hc",
            "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc",
            f"  rcases hc with {rcases_pat}",
            *call_proofs,
            "",
        ])

    emit_row_reads_thm(
        "core_row_reads", "(coreWorld world coreTuple)", "(coreKind kObj coreTuple)",
        "coreTuple", n_core, own_core_idx, dir_core_idx, True,
    )
    if kinfo["child_form"]:
        n_child = len(kinfo["tuple"])
        own_c_idx = kinfo["tuple"].index(kn)
        dir_c_idx = kinfo["tuple"].index("FN2-MACHINES")
        emit_row_reads_thm(
            "child_row_reads", "world", "kObj",
            "kObj.tuple", n_child, own_c_idx, dir_c_idx, False,
        )

    # Column `fieldWrite` equations (`rfl`) for own table and directory
    for ti, tc in enumerate(kinfo["table"]):
        setter = f"{kn}-SET-{tc}"
        if setter in fn_defs:
            lines += [
                f"theorem set_{tc.replace('-', '_')}_fw (slot v own : Val) :",
                f"    {ident(setter)} slot v own = Combinators.fieldWrite {ti} slot v own := by rfl",
                "",
            ]
    dir_col_idx = {"READY-PREV": 2, "READY-NEXT": 3, "WAIT-REASON": 4}
    for dc, di in dir_col_idx.items():
        setter = f"FN2-MACHINES-SET-{dc}"
        if setter in fn_defs:
            lines += [
                f"theorem set_dir_{dc.replace('-', '_')}_fw (id v dir : Val) :",
                f"    {ident(setter)} id v dir = Combinators.fieldWrite {di} id v dir := by rfl",
                "",
            ]

    # Core-kind specific: `ROW-<C>` readers and `<KN>-WRITE+...` batch write lemmas
    write_lemmas = {}
    if not kinfo["child_form"]:
        if "FN2-CORE-STOP" in fn_defs:
            lines += [
                f"theorem core_stop_eq (r : Val) (kids : Fin {n_core} → Val) :",
                f"    «FN2-CORE-STOP» r (Combinators.tupleImage kids) =",
                f"      Combinators.tupleImage (Combinators.patchKids kids {ctrl_core_idx}",
                f"        («FN2-CONTROL-RECORD-STOP» r (kids ⟨{ctrl_core_idx}, by decide⟩))) := by",
                f"  have hc : «FN2-CORE-CONTROL» (Combinators.tupleImage kids) = kids ⟨{ctrl_core_idx}, by decide⟩ :=",
                f"    Combinators.nth_tupleImage kids {ctrl_core_idx} (by decide)",
                f"  have hu (v : Val) : «UPDATE-FN2-CORE-CONTROL» v (Combinators.tupleImage kids) =",
                f"      Combinators.tupleImage (Combinators.patchKids kids {ctrl_core_idx} v) :=",
                f"    (Combinators.tupleImage_patchKids kids {ctrl_core_idx} v (by decide)).symm",
                "  simp only [«FN2-CORE-STOP», hc, hu]",
                "",
            ]
        if "FN2-CORE-KIND-STOP" in fn_defs:
            lines += [
                f"theorem core_kind_stop_eq (k idx : Val) (kids : Fin {n_core} → Val) :",
                f"    «FN2-CORE-KIND-STOP» k idx (Combinators.tupleImage kids) =",
                f"      Combinators.tupleImage (Combinators.patchKids kids {ctrl_core_idx}",
                f"        («FN2-CONTROL-RECORD-KIND-STOP» k idx (kids ⟨{ctrl_core_idx}, by decide⟩))) := by",
                f"  have hc : «FN2-CORE-CONTROL» (Combinators.tupleImage kids) = kids ⟨{ctrl_core_idx}, by decide⟩ :=",
                f"    Combinators.nth_tupleImage kids {ctrl_core_idx} (by decide)",
                f"  have hu (v : Val) : «UPDATE-FN2-CORE-CONTROL» v (Combinators.tupleImage kids) =",
                f"      Combinators.tupleImage (Combinators.patchKids kids {ctrl_core_idx} v) :=",
                f"    (Combinators.tupleImage_patchKids kids {ctrl_core_idx} v (by decide)).symm",
                "  simp only [«FN2-CORE-KIND-STOP», hc, hu]",
                "",
            ]
        if "FN2-MACHINE-WAKE-ROW" in fn_defs:
            lines += [
                f"theorem core_wake_row_eq (rid : Val) (kids : Fin {n_core} → Val) :",
                f"    «FN2-MACHINE-WAKE-ROW» rid (Combinators.tupleImage kids) =",
                f"      let r := «FN2-MACHINES-WAKE-ROW» rid (kids ⟨{dir_core_idx}, by decide⟩) (kids ⟨{ctrl_core_idx}, by decide⟩)",
                f"      Combinators.tupleImage (Combinators.patchKids (Combinators.patchKids kids {dir_core_idx} r.car) {ctrl_core_idx} r.cdr.car) := by",
                f"  have hd : «FN2-CORE-MACHINES» (Combinators.tupleImage kids) = kids ⟨{dir_core_idx}, by decide⟩ :=",
                f"    Combinators.nth_tupleImage kids {dir_core_idx} (by decide)",
                f"  have hc : «FN2-CORE-CONTROL» (Combinators.tupleImage kids) = kids ⟨{ctrl_core_idx}, by decide⟩ :=",
                f"    Combinators.nth_tupleImage kids {ctrl_core_idx} (by decide)",
                f"  have hud (vd : Val) : «UPDATE-FN2-CORE-MACHINES» vd (Combinators.tupleImage kids) =",
                f"      Combinators.tupleImage (Combinators.patchKids kids {dir_core_idx} vd) :=",
                f"    (Combinators.tupleImage_patchKids kids {dir_core_idx} vd (by decide)).symm",
                f"  have huc (vd vc : Val) : «UPDATE-FN2-CORE-CONTROL» vc (Combinators.tupleImage (Combinators.patchKids kids {dir_core_idx} vd)) =",
                f"      Combinators.tupleImage (Combinators.patchKids (Combinators.patchKids kids {dir_core_idx} vd) {ctrl_core_idx} vc) :=",
                f"    (Combinators.tupleImage_patchKids (Combinators.patchKids kids {dir_core_idx} vd) {ctrl_core_idx} vc (by decide)).symm",
                "  simp only [«FN2-MACHINE-WAKE-ROW», hd, hc, nth_0_eq_car, nth_1_eq_cdr_car, hud, huc]",
                "",
            ]
        for c, _ in kinfo["columns"]:
            row_fn = f"{kn}-ROW-{c}"
            if row_fn not in fn_defs:
                continue
            if c in DIRECTORY_FIELDS:
                rhs = f"({ident('FN2-MACHINES-' + c)} id (kids ⟨{dir_core_idx}, by decide⟩))"
                tbl_eq = f"have hd : «FN2-CORE-MACHINES» (Combinators.tupleImage kids) = kids ⟨{dir_core_idx}, by decide⟩ := Combinators.nth_tupleImage kids {dir_core_idx} (by decide)"
                extra_rw = "hd"
            else:
                rhs = f"({ident(kn + '-' + c)} («FN2-MACHINE-SLOT» id (Combinators.tupleImage kids)) (kids ⟨{own_core_idx}, by decide⟩))"
                tbl_eq = f"have ho : {ident(own_table_fn)} (Combinators.tupleImage kids) = kids ⟨{own_core_idx}, by decide⟩ := Combinators.nth_tupleImage kids {own_core_idx} (by decide)"
                extra_rw = "ho"
            safe_c = c.replace("-", "_")
            lines += [
                f"theorem row_read_{safe_c} (id : Val) (kids : Fin {n_core} → Val)",
                f"    (h : {ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) = .sym \":OK\") :",
                f"    {ident(row_fn)} id (Combinators.tupleImage kids) = {rhs} := by",
                f"  {tbl_eq}",
                f"  dsimp only [{ident(row_fn)}]",
                f"  simp only [h, eq_def, not_def, equal_val_truthy, beq_self_eq_true, Val.truthy_ite, Val.truthy_ofBool, Val.truthy_t, Val.truthy_nil, Bool.false_eq_true, ↓reduceIte, {extra_rw}]",
                "",
            ]

        # Phase clamp helper if kind has states
        m_states = len(kinfo["states"])
        if m_states >= 1:
            # Build ACL2's `fn2-arms-phase-choice` term after `eql_def` + `equal_val_truthy`
            def build_phase_clamp(idx):
                if idx >= m_states - 1:
                    return f"(Val.int {m_states - 1})"
                return f"(if (ph == Val.int {idx}) then Val.int {idx} else {build_phase_clamp(idx + 1)})"

            disj = " ∨ ".join(f"i = {j}" for j in range(m_states))
            pats = " | ".join(["rfl"] * m_states)
            lines += [
                f"def phaseClamp (ph : Val) : Val := {build_phase_clamp(0)}",
                "",
                f"theorem phaseClamp_eq (ph : Val) (hph : ColType.fits (.enum {m_states}) ph = true) :",
                "    phaseClamp ph = ph := by",
                "  cases ph with",
                "  | int i =>",
                "    simp only [ColType.fits, Bool.and_eq_true, decide_eq_true_eq] at hph",
                f"    have hor : {disj} := by omega",
                f"    rcases hor with {pats} <;> decide",
                "  | _ => simp [ColType.fits] at hph",
                "",
            ]

        prefix = f"{kn}-WRITE+"
        for fn_name in sorted(fn_defs):
            if not fn_name.startswith(prefix):
                continue
            fields = fn_name[len(prefix):].split("+")
            if any(f not in kinfo["col_map"] for f in fields):
                continue
            thm_w = "write_" + "_".join(f.replace("-", "_") for f in fields)
            write_lemmas[tuple(fields)] = thm_w
            w_vars = [f"w_{i}" for i in range(len(fields))]
            w_binders = " ".join(f"({v} : Val)" for v in w_vars)
            w_args = " ".join(w_vars)
            fits_terms = [f"ColType.fits {col_type_lean(kinfo['col_map'][f])} {w_vars[i]}" for i, f in enumerate(fields)]
            fits_expr = " && ".join(fits_terms) if fits_terms else "true"
            slot_expr = "(«FN2-MACHINE-SLOT» id (Combinators.tupleImage kids))"
            own_expr = f"(kids ⟨{own_core_idx}, by decide⟩)"
            dir_expr = f"(kids ⟨{dir_core_idx}, by decide⟩)"
            ctrl_expr = f"(kids ⟨{ctrl_core_idx}, by decide⟩)"
            for i, f in enumerate(fields):
                if f not in DIRECTORY_FIELDS:
                    own_expr = f"({ident(kn + '-SET-' + f)} {slot_expr} {w_vars[i]} {own_expr})"
                else:
                    dir_expr = f"({ident('FN2-MACHINES-SET-' + f)} id {w_vars[i]} {dir_expr})"
            has_dir = any(f in DIRECTORY_FIELDS for f in fields)
            if has_dir:
                pass_kids = (
                    f"(Combinators.patchKids (Combinators.patchKids kids {own_core_idx} {own_expr}) "
                    f"{dir_core_idx} {dir_expr})"
                )
            else:
                pass_kids = f"(Combinators.patchKids kids {own_core_idx} {own_expr})"
            fail_kids = (
                f"(Combinators.patchKids kids {ctrl_core_idx} "
                f"(«FN2-CONTROL-RECORD-STOP» (.int {stop_write_code}) {ctrl_expr}))"
            )
            has_phase = "PHASE" in fields
            ph_idx = fields.index("PHASE") if has_phase else -1
            ph_hyp_decl = (
                f"\n    (hph : ColType.fits (.enum {m_states}) {w_vars[ph_idx]} = true)"
                if has_phase else ""
            )

            lines += [
                f"theorem {thm_w} (id : Val) {w_binders} (kids : Fin {n_core} → Val)",
                f"    (h : {ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) = .sym \":OK\"){ph_hyp_decl} :",
                f"    {ident(fn_name)} id {w_args} (Combinators.tupleImage kids) =",
                f"      (if ({fits_expr}) then Combinators.tupleImage {pass_kids}",
                f"       else Combinators.tupleImage {fail_kids}) := by",
                "  obtain ⟨hi, hr, hs, hb⟩ := snapshot_bounds id (Combinators.tupleImage kids) h",
                "  obtain ⟨_, hk⟩ := snapshot_parts id (Combinators.tupleImage kids) h",
                "  have hid : («FN2-MACHINE-IDP» id (Combinators.tupleImage kids)).truthy = true := by",
                "    simp [«FN2-MACHINE-IDP», hi, hr]",
                "  have hslot : «FN2-MACHINE-SLOT» id (Combinators.tupleImage kids) =",
                "      «FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» (Combinators.tupleImage kids)) := by",
                "    simp [«FN2-MACHINE-SLOT», «FN2-MACHINE-SLOT-READ-CODE», hid, «EQ», Prim.equal]",
                f"  have hown_get : {ident(own_table_fn)} (Combinators.tupleImage kids) = kids ⟨{own_core_idx}, by decide⟩ :=",
                f"    Combinators.nth_tupleImage kids {own_core_idx} (by decide)",
                f"  have hdir_get : «FN2-CORE-MACHINES» (Combinators.tupleImage kids) = kids ⟨{dir_core_idx}, by decide⟩ :=",
                f"    Combinators.nth_tupleImage kids {dir_core_idx} (by decide)",
                f"  have hctrl_get : «FN2-CORE-CONTROL» (Combinators.tupleImage kids) = kids ⟨{ctrl_core_idx}, by decide⟩ :=",
                f"    Combinators.nth_tupleImage kids {ctrl_core_idx} (by decide)",
                "  rw [← hslot] at hs hb",
                "  rw [hown_get] at hb",
                "  rw [hdir_get] at hr",
                f"  have hupd_own (v : Val) : {ident(upd_own_table_fn)} v (Combinators.tupleImage kids) =",
                f"      Combinators.tupleImage (Combinators.patchKids kids {own_core_idx} v) :=",
                f"    (Combinators.tupleImage_patchKids kids {own_core_idx} v (by decide)).symm",
                f"  have hself_own : Combinators.patchKids kids {own_core_idx} (kids ⟨{own_core_idx}, by decide⟩) = kids :=",
                f"    Combinators.patchKids_self kids {own_core_idx} (by decide)",
                f"  have hupd_ctrl (v : Val) : «UPDATE-FN2-CORE-CONTROL» v (Combinators.tupleImage kids) =",
                f"      Combinators.tupleImage (Combinators.patchKids kids {ctrl_core_idx} v) :=",
                f"    (Combinators.tupleImage_patchKids kids {ctrl_core_idx} v (by decide)).symm",
            ]
            if has_dir:
                lines += [
                    f"  have hdir_after_own (v : Val) : «FN2-CORE-MACHINES» (Combinators.tupleImage (Combinators.patchKids kids {own_core_idx} v)) =",
                    f"      kids ⟨{dir_core_idx}, by decide⟩ := by",
                    f"    change Native.nth (.int ({dir_core_idx} : Nat)) (Combinators.tupleImage (Combinators.patchKids kids {own_core_idx} v)) = _",
                    f"    rw [Combinators.nth_tupleImage _ {dir_core_idx} (by decide), Combinators.patchKids_ne kids {own_core_idx} {dir_core_idx} v (by decide) (by decide)]",
                    f"  have hupd_dir (vo vd : Val) : «UPDATE-FN2-CORE-MACHINES» vd (Combinators.tupleImage (Combinators.patchKids kids {own_core_idx} vo)) =",
                    f"      Combinators.tupleImage (Combinators.patchKids (Combinators.patchKids kids {own_core_idx} vo) {dir_core_idx} vd) :=",
                    f"    (Combinators.tupleImage_patchKids (Combinators.patchKids kids {own_core_idx} vo) {dir_core_idx} vd (by decide)).symm",
                ]
            if has_phase:
                lines += [
                    f"  have hph_clamp : phaseClamp {w_vars[ph_idx]} = {w_vars[ph_idx]} := phaseClamp_eq {w_vars[ph_idx]} hph",
                    "  dsimp only [phaseClamp] at hph_clamp",
                ]
            ph_simp = ", hph_clamp" if has_phase else ""
            dir_simp = ", hdir_after_own, hi, hr, hupd_dir" if has_dir else ""
            lines += [
                f"  dsimp only [{ident(fn_name)}]",
                "  simp only [eq_def, eql_def, num_eq_def, not_def, equal_val_truthy, hid, hk, beq_self_eq_true,",
                "    Val.truthy_ite, Val.truthy_ofBool, Val.truthy_t, Val.truthy_nil, ↓reduceIte, Bool.false_eq_true,",
                "    and_truthy, ite_bool_false_eq_and, ubp_truthy, ubp_int_truthy, enum_truthy, enum_and_truthy,",
                "    enum_int_truthy, enum_int_and_truthy, enum_int_left_and_truthy, Int.reduceLE, Int.toNat, decide_true,",
                f"    hs, hb, hown_get, Bool.true_and, Bool.and_true, Bool.and_self, ← Bool.and_assoc{ph_simp}]",
                f"  by_cases hfits : ({fits_expr}) = true",
                f"  · simp only [hfits, ↓reduceIte, Pres.nth_cons_zero, Pres.nth_cons_succ, Int.reduceLT, Int.reduceSub,",
                f"      Val.truthy_ite, Val.truthy_t, Val.truthy_nil, and_truthy, ite_bool_false_eq_and, Bool.and_self, hupd_own{dir_simp}]",
                "  · have hff : (" + fits_expr + ") = false := Bool.eq_false_iff.mpr hfits",
                "    simp only [hfits, hff, Bool.false_eq_true, ↓reduceIte, Pres.nth_cons_zero, Pres.nth_cons_succ,",
                "      Int.reduceLT, Int.reduceSub, Val.truthy_t, Val.truthy_nil, hupd_own, hself_own,",
                "      «FN2-MACHINE-REFUSE-WRITE», «FN2-CORE-STOP», hctrl_get, hupd_ctrl]",
                "",
            ]

    lines += [f"end Fn2.Instances.ServedCertificates.Kind{ki}Common", ""]
    src = fill_world_bodies(
        as_module("\n".join(lines), expose=True, import_all=CORE_STRING_BODIES, bodies="scan"),
        widx,
    )
    (out_dir / f"Kind{ki}Common.lean").write_text(src)
    return {"own_table_fn": own_table_fn, "upd_own_table_fn": upd_own_table_fn, "write_lemmas": write_lemmas}


# ---------------------------------------------------------------------------
# Symbolic Arm Proof Builder (`ArmProofBuilder`)
# ---------------------------------------------------------------------------

class SymCtx:
    """Symbolic interpreter state at a step/node boundary."""

    def __init__(self, local_vars=None, kids_var="kids", pending=None,
                 next_expr=None, next_done=False, woken=False, snap_hyp="hs0"):
        self.local_vars = list(local_vars or [])  # [(arm_var_name, lean_ident), ...]
        self.kids_var = kids_var
        self.pending = list(pending or [])        # [(col_name, expr_sexp), ...]
        self.next_expr = next_expr                # None or expr_sexp
        self.next_done = next_done
        self.woken = woken
        self.snap_hyp = snap_hyp                  # None or Lean proof ident for SNAPSHOT-READ-CODE = :OK

    def clone(self, **kw):
        c = SymCtx(
            local_vars=self.local_vars,
            kids_var=self.kids_var,
            pending=self.pending,
            next_expr=self.next_expr,
            next_done=self.next_done,
            woken=self.woken,
            snap_hyp=self.snap_hyp,
        )
        for k, v in kw.items():
            setattr(c, k, v)
        return c


class ArmProofBuilder:
    """Compiles an ArmDecl AST into bottom-up `node_k` definitions and `node_k_run` theorems."""

    def __init__(self, kinfo, core_mode, observe, decl_ast, prefix="arm",
                 tuple_analyzer=None, subarm_mod=None, fn_defs=None):
        self.kinfo = kinfo
        self.kn = kinfo["name"]
        self.core_mode = core_mode
        self.observe = observe
        self.decl_ast = decl_ast
        self.prefix = prefix
        self.tuple_analyzer = tuple_analyzer
        self.subarm_mod = subarm_mod
        self.fn_defs = fn_defs or {}

        self.tup_list = kinfo["core_tuple"] if core_mode else kinfo["tuple"]
        self.n_tup = len(self.tup_list)
        self.tup_expr = "coreTuple" if core_mode else "kObj.tuple"
        self.w_expr = "(coreWorld world coreTuple)" if core_mode else "world"
        self.k_expr = "(coreKind kObj coreTuple)" if core_mode else "kObj"
        self.own_idx = self.tup_list.index(self.kn)
        self.dir_idx = self.tup_list.index("FN2-MACHINES")
        self.ctrl_idx = self.tup_list.index("FN2-CONTROL")
        self.ans_len = 1 if observe else 4

        if observe:
            self.base_pairs = [
                ("ID", "id"), ("SLOT", "slot"), ("KIND", "kindTag"), ("ORDINAL", "ordinal"),
                ("EVENT", "event"), ("OUTCOME", "outcome"), ("REASON", "reason"),
                ("COUNT", "count"), ("AUX0", "aux0"), ("AUX1", "aux1"),
            ]
        else:
            self.base_pairs = [
                ("ID", "id"), ("SLOT", "slot"), ("KIND", "kindTag"),
                ("ORDINAL", "ordinal"), ("BUDGET", "budget"),
            ]
        self.val_params = [p[1] for p in self.base_pairs]
        self.base_env_lean = "[" + ", ".join(f"({lean_str(k)}, {v})" for k, v in self.base_pairs) + "]"
        self.kcommon_ns = f"Kind{kinfo['ki']}Common"
        self.reads_env_fn = f"{self.kcommon_ns}.core_row_reads_env" if core_mode else f"{self.kcommon_ns}.child_row_reads_env"

        self.col_read_exprs = []
        for c, _ in kinfo["columns"]:
            if c in DIRECTORY_FIELDS:
                self.col_read_exprs.append((f"ROW-{c}", f"({ident('FN2-MACHINES-' + c)} id (kids0 ⟨{self.dir_idx}, by decide⟩))"))
            else:
                self.col_read_exprs.append((f"ROW-{c}", f"({ident(self.kn + '-' + c)} slot (kids0 ⟨{self.own_idx}, by decide⟩))"))

        self.refusal_steps = decl_ast["on_refusal"]
        self.refusal_lean = "[" + ", ".join(step_to_lean(s) for s in self.refusal_steps) + "]"
        self.frame_call = f"({self.prefix}_frame {' '.join(self.val_params)})"

        self.node_counter = 0
        self.let_counter = 0
        self.emitted_defs = []
        self.node_names = []
        self.used_multi_ops = set()  # {(callee, m), ...}
        self.used_subarms = set()    # {sub_tag, ...}
        self.modified_idxs = set()   # indices patched across arm

    def fresh_let(self, hint="lv"):
        i = self.let_counter
        self.let_counter += 1
        return f"{hint}_{i}"

    def vars_lean(self, ctx):
        res = f"({self.reads_env_fn} id slot kids0 ++ {self.base_env_lean})"
        for vn, lv in reversed(ctx.local_vars):
            res = f"(({lean_str(vn)}, {lv}) :: {res})"
        return res

    def prove_pend(self, cur_ctx, pend_pairs_lean):
        return (
            f"(by unfold pend; have hdup : ({pend_pairs_lean}.any fun p => ({self.pend_lean(cur_ctx.pending)} : List (String × Expr)).any (·.1 == p.1)) = false := (by dsimp only [List.any]; decide); "
            f"dsimp only []; rw [if_neg (Bool.eq_false_iff.mp hdup)]; try rfl)"
        )

    def all_var_entries(self, ctx):
        return list(ctx.local_vars) + self.col_read_exprs + self.base_pairs

    def pend_lean(self, pending):
        if not pending:
            return "[]"
        return "[" + ", ".join(f"({lean_str(c)}, {val(e)})" for c, e in pending) + "]"

    def next_lean(self, next_expr):
        return "none" if next_expr is None else f"(some ({val(next_expr)}))"

    def st_lean(self, ctx):
        return (
            f"(⟨Combinators.tupleStobjs {self.tup_expr} {ctx.kids_var}, "
            f"{self.vars_lean(ctx)}, {self.pend_lean(ctx.pending)}, "
            f"{self.next_lean(ctx.next_expr)}, {'true' if ctx.next_done else 'false'}, "
            f"{'true' if ctx.woken else 'false'}, (0, 0, 0)⟩ : St)"
        )

    def prove_var_st(self, x, ctx):
        entries = self.all_var_entries(ctx)
        ks = [k for k, _ in entries]
        if x not in ks:
            raise UnsupportedArmError(f"unbound variable {x}")
        idx = ks.index(x)
        v_expr = entries[idx][1]
        ks_lean = "[" + ", ".join(lean_str(k) for k in ks) + "]"
        st_s = self.st_lean(ctx)
        prf = (
            f"(Combinators.var_of_findIdx {st_s} {ks_lean} {lean_str(x)} {idx} {v_expr} "
            f"rfl (by decide +kernel) rfl)"
        )
        return v_expr, prf

    def prove_stobj(self, s_name, ctx):
        if s_name not in self.tup_list:
            raise UnsupportedArmError(f"unknown stobj {s_name}")
        idx = self.tup_list.index(s_name)
        v_expr = f"({ctx.kids_var} ⟨{idx}, by decide⟩)"
        prf = (
            f"(Combinators.stobj_tupleStobjs {self.tup_expr} {ctx.kids_var} "
            f"{self.vars_lean(ctx)} {self.pend_lean(ctx.pending)} {self.next_lean(ctx.next_expr)} "
            f"{'true' if ctx.next_done else 'false'} {'true' if ctx.woken else 'false'} (0, 0, 0) "
            f"{lean_str(s_name)} {idx} (by decide) (by decide +kernel) (by decide +kernel))"
        )
        return v_expr, prf

    def prove_call_fn_plain(self, fn_name, vs_exprs, vs_list_lean):
        v_lean = f"({ident(fn_name)}" + ("" if not vs_exprs else " " + " ".join(vs_exprs)) + ")"
        if fn_name not in self.fn_defs:
            raise UnsupportedArmError(f"missing function {fn_name} in world")
        fns_thm = f"({ident(fn_name)}.fns_eq" + ("" if not vs_exprs else " " + " ".join(vs_exprs)) + ")"
        if self.core_mode:
            prf = (
                f"(Combinators.callFn_core_of_fns world coreTuple {lean_str(fn_name)} "
                f"{vs_list_lean} {v_lean} (by decide +kernel) (by decide +kernel) {fns_thm})"
            )
        else:
            prf = f"(callFn_world_of_fns {lean_str(fn_name)} {vs_list_lean} {v_lean} (by decide +kernel) {fns_thm})"
        return v_lean, prf

    def prove_eval_args(self, ts, env_ctx):
        env_s = env_ctx["env_expr"]
        if not ts:
            return [], "[]", f"(Combinators.evalArgs_nil {self.w_expr}.fns {env_s})"
        v0, h0 = self.prove_term_eval(ts[0], env_ctx)
        vs_rest, vs_rest_lean, hrest = self.prove_eval_args(ts[1:], env_ctx)
        all_vs = [v0] + vs_rest
        list_lean = "[" + ", ".join(all_vs) + "]"
        ts_tail_lean = "[" + ", ".join(term_to_lean(x) for x in ts[1:]) + "]"
        prf = (
            f"(Combinators.evalArgs_cons {self.w_expr}.fns {env_s} {term_to_lean(ts[0])} "
            f"{ts_tail_lean} {v0} {vs_rest_lean} {h0} {hrest})"
        )
        return all_vs, list_lean, prf

    def prove_tuple_vars_eval(self, env_ctx):
        env_s = env_ctx["env_expr"]
        if env_ctx["kind"] == "st":
            ctx = env_ctx["ctx"]
            entries = self.all_var_entries(ctx)
            ks_lean = "[" + ", ".join(lean_str(k) for k, _ in entries) + "]"
            return (
                f"(Combinators.evalArgs_tuple_vars {self.w_expr}.fns {self.tup_expr} "
                f"{ctx.kids_var} {self.vars_lean(ctx)} {ks_lean} "
                f"(by decide) (by decide +kernel) rfl (by decide +kernel))"
            )
        # Inside a `Term.lam` body where all tuple names are bound in `formals`:
        t_terms = [("var", c) for c in self.tup_list]
        _, _, h_list = self.prove_eval_args(t_terms, env_ctx)
        return h_list

    def prove_term_eval(self, t, env_ctx):
        tag = t[0]
        env_s = env_ctx["env_expr"]
        if tag == "quote":
            v_lean = f"({val(t[1])})"
            return v_lean, f"(Combinators.eval_quote {self.w_expr}.fns {env_s} {v_lean})"
        if tag == "var":
            x = t[1]
            if env_ctx["kind"] == "lam":
                formals = env_ctx["formals"]
                vs_exprs = env_ctx["vs_exprs"]
                if x not in formals:
                    raise UnsupportedArmError(f"unbound lambda var {x}")
                idx = formals.index(x)
                v_lean = vs_exprs[idx]
                ks_lean = "[" + ", ".join(lean_str(f) for f in formals) + "]"
                hget = (
                    f"(Combinators.env_get_of_findIdx {env_s} {ks_lean} {lean_str(x)} "
                    f"{idx} {v_lean} rfl (by decide +kernel) rfl)"
                )
                return v_lean, f"(Combinators.eval_var {self.w_expr}.fns {env_s} {lean_str(x)} {v_lean} {hget})"
            ctx = env_ctx["ctx"]
            entries = self.all_var_entries(ctx)
            ks = [k for k, _ in entries]
            if x in ks:
                v_lean, hvar = self.prove_var_st(x, ctx)
                return v_lean, f"(Combinators.eval_var_st {self.w_expr} {self.st_lean(ctx)} {lean_str(x)} {v_lean} {hvar})"
            if x in self.tup_list:
                t_idx = self.tup_list.index(x)
                v_lean = f"({ctx.kids_var} ⟨{t_idx}, by decide⟩)"
                ks_lean = "[" + ", ".join(lean_str(k) for k in ks) + "]"
                hnone = f"(Combinators.env_get_none_of_keys {self.vars_lean(ctx)} {ks_lean} {lean_str(x)} rfl (by decide +kernel))"
                hget = (
                    f"(Combinators.env_get_tupleStobjs {self.tup_expr} {ctx.kids_var} "
                    f"{self.vars_lean(ctx)} {lean_str(x)} {t_idx} (by decide) {hnone} "
                    f"(by decide +kernel) (by decide +kernel))"
                )
                return v_lean, f"(Combinators.eval_var {self.w_expr}.fns {env_s} {lean_str(x)} {v_lean} {hget})"
            raise UnsupportedArmError(f"unbound term var {x}")
        if tag == "lam":
            _, formals, body, actuals = t
            vs_exprs, vs_lean, hargs = self.prove_eval_args(actuals, env_ctx)
            fs_lean = "[" + ", ".join(lean_str(f) for f in formals) + "]"
            lam_ctx = {
                "kind": "lam",
                "env_expr": f"({fs_lean}.zip {vs_lean})",
                "formals": formals,
                "vs_exprs": vs_exprs,
                "kids_var": env_ctx["kids_var"],
            }
            vb, hbody = self.prove_term_eval(body, lam_ctx)
            act_lean = "[" + ", ".join(term_to_lean(a) for a in actuals) + "]"
            prf = (
                f"(Combinators.eval_lam {self.w_expr}.fns {env_s} {fs_lean} "
                f"{term_to_lean(body)} {act_lean} {vs_lean} {vb} {hargs} {hbody})"
            )
            return vb, prf
        if tag == "app":
            _, f, args = t
            if f == "IF" and len(args) == 3:
                vc, hc = self.prove_term_eval(args[0], env_ctx)
                va, ha = self.prove_term_eval(args[1], env_ctx)
                vb, hb = self.prove_term_eval(args[2], env_ctx)
                v_lean = f"(if ({vc}).truthy then {va} else {vb})"
                prf = (
                    f"(Combinators.eval_if {self.w_expr}.fns {env_s} {term_to_lean(args[0])} "
                    f"{term_to_lean(args[1])} {term_to_lean(args[2])} {vc} {va} {vb} "
                    f"{hc} (fun _ => {ha}) (fun _ => {hb}))"
                )
                return v_lean, prf
            if f == "RETURN-LAST" and len(args) == 3:
                vc, hc = self.prove_term_eval(args[2], env_ctx)
                prf = (
                    f"(Combinators.eval_return_last {self.w_expr}.fns {env_s} "
                    f"{term_to_lean(args[0])} {term_to_lean(args[1])} {term_to_lean(args[2])} {vc} {hc})"
                )
                return vc, prf
            hnif = "(by decide)"
            hnrl = "(by decide)"
            args_lean = "[" + ", ".join(term_to_lean(a) for a in args) + "]"
            if f.endswith("@CORE"):
                base_fn = f[:-5]
                if base_fn not in self.fn_defs:
                    raise UnsupportedArmError(f"missing @CORE target {base_fn}")
                n_pre = len(args) - self.n_tup
                pre_terms = args[:n_pre]
                pre_exprs, pre_lean, hpre = self.prove_eval_args(pre_terms, env_ctx)
                htup = self.prove_tuple_vars_eval(env_ctx)
                kv = env_ctx["kids_var"]
                pre_terms_lean = "[" + ", ".join(term_to_lean(a) for a in pre_terms) + "]"
                vs_lean = f"({pre_lean} ++ List.ofFn {kv})"
                hargs = (
                    f"(Combinators.evalArgs_append {self.w_expr}.fns {env_s} {pre_terms_lean} "
                    f"({self.tup_expr}.map Term.var) {pre_lean} (List.ofFn {kv}) {hpre} {htup})"
                )
                call_args_str = (" " + " ".join(pre_exprs) if pre_exprs else "") + f" (Combinators.tupleImage {kv})"
                v_lean = f"({ident(base_fn)}{call_args_str})"
                fns_thm = f"({ident(base_fn)}.fns_eq{call_args_str})"
                if base_fn in self.kinfo["ops"]:
                    op_idx = self.kinfo["ops"][base_fn]["idx"]
                    hcall = (
                        f"(Combinators.callFn_core_pure_op world coreTuple {lean_str(f)} "
                        f"world.ops[{op_idx}]! {pre_lean} {kv} {v_lean} (by decide) "
                        f"(by decide +kernel) rfl rfl rfl rfl {fns_thm})"
                    )
                else:
                    hcall = (
                        f"(Combinators.callFn_core_link world coreTuple {lean_str(f)} {lean_str(base_fn)} "
                        f"{pre_lean} {kv} {v_lean} (by decide) (by decide +kernel) rfl "
                        f"rfl (by decide +kernel) {fns_thm})"
                    )
                prf = (
                    f"(Combinators.eval_app_callFn {self.w_expr} {env_s} {lean_str(f)} "
                    f"({pre_terms_lean} ++ {self.tup_expr}.map Term.var) {vs_lean} {v_lean} {hnif} {hnrl} {hargs} {hcall})"
                )
                return v_lean, prf
            vs_exprs, vs_lean, hargs = self.prove_eval_args(args, env_ctx)
            if f in NATIVE_IMPL_EXPR:
                v_lean = NATIVE_IMPL_EXPR[f](vs_exprs)
                hcall = f"(Combinators.callFn_of_native {self.w_expr} {lean_str(f)} {vs_lean} {v_lean} rfl)"
            else:
                v_lean, hcall = self.prove_call_fn_plain(f, vs_exprs, vs_lean)
            prf = (
                f"(Combinators.eval_app_callFn {self.w_expr} {env_s} {lean_str(f)} "
                f"{args_lean} {vs_lean} {v_lean} {hnif} {hnrl} {hargs} {hcall})"
            )
            return v_lean, prf
        raise UnsupportedArmError(f"unknown term tag {tag}")

    def st_env_ctx(self, ctx):
        st_s = self.st_lean(ctx)
        return {"kind": "st", "ctx": ctx, "env_expr": f"({st_s}.vars ++ {st_s}.stobjs)", "kids_var": ctx.kids_var}

    def prove_ev(self, e_sexp, ctx):
        t = read_expr_ast(e_sexp, self.kinfo, self.core_mode)
        t_lean = term_to_lean(t)
        v_lean, heval = self.prove_term_eval(t, self.st_env_ctx(ctx))
        e_lean = f"({val(e_sexp)})"
        st_s = self.st_lean(ctx)
        hr = f"(Combinators.exceptTermOk_eq (r := readExpr {self.w_expr} {self.k_expr} {e_lean}) (t := {t_lean}) (by decide +kernel))"
        return v_lean, f"(Combinators.ev_of_readExpr {self.w_expr} {self.k_expr} {st_s} {e_lean} {t_lean} {v_lean} {hr} {heval})"

    def prove_ev_opt(self, opt_sexp, dflt_lean, ctx):
        st_s = self.st_lean(ctx)
        if opt_sexp is None:
            return dflt_lean, f"(Combinators.evOpt_none {self.w_expr} {self.k_expr} {st_s} {dflt_lean})"
        v_lean, hev = self.prove_ev(opt_sexp, ctx)
        return v_lean, f"(Combinators.evOpt_some {self.w_expr} {self.k_expr} {st_s} ({val(opt_sexp)}) {dflt_lean} {v_lean} {hev})"

    def prove_flush(self, ctx):
        """Returns `(let_defs, let_prfs, hfl_prf, post_rw_lines, new_ctx)`."""
        if not ctx.pending and ctx.next_expr is None:
            hfl = f"(Fn2.Arms.flush_empty {self.w_expr} {self.frame_call} {self.st_lean(ctx)} rfl rfl)"
            return [], [], hfl, [], ctx

        if self.core_mode and not self.kinfo["child_form"] and ctx.snap_hyp is None:
            raise UnsupportedArmError("core multi-flush requires snapshot preservation")

        let_defs = []
        let_prfs = []
        st_s = self.st_lean(ctx)

        # Evaluate pending expressions in declaration order
        pend_vars = []
        pend_evals = []
        for col_n, e_sexp in ctx.pending:
            v_expr, hev = self.prove_ev(e_sexp, ctx)
            pv = self.fresh_let("pw")
            let_defs.append(f"let {pv} : Val := {v_expr}")
            let_prfs.append(f"let {pv} : Val := {v_expr}")
            pend_vars.append((col_n, pv))
            pend_evals.append((col_n, e_sexp, pv, hev))

        # Build `hpairs` proof term bottom-up
        hpairs = f"(mapM_pend_nil {self.w_expr} {self.k_expr} {st_s})"
        tail_val_lean = "[]"
        tail_expr_lean = "[]"
        for i in range(len(pend_evals) - 1, -1, -1):
            col_n, e_sexp, pv, hev = pend_evals[i]
            hpairs = (
                f"(mapM_pend_cons {self.w_expr} {self.k_expr} {st_s} "
                f"{lean_str(col_n)} ({val(e_sexp)}) {tail_expr_lean} {pv} {tail_val_lean} {hev} {hpairs})"
            )
            tail_val_lean = "[" + ", ".join(f"({lean_str(c)}, {v})" for c, v in pend_vars[i:]) + "]"
            tail_expr_lean = "[" + ", ".join(f"({lean_str(c)}, {val(e)})" for c, e, _, _ in pend_evals[i:]) + "]"
        pairs_val_lean = tail_val_lean

        if ctx.next_expr is not None:
            n_term = read_next_ast(ctx.next_expr, self.kinfo, self.core_mode)
            n_term_lean = term_to_lean(n_term)
            ph_raw, hen = self.prove_term_eval(n_term, self.st_env_ctx(ctx))
            ph_v = self.fresh_let("pw_ph")
            let_defs.append(f"let {ph_v} : Val := {ph_raw}")
            let_prfs.append(f"let {ph_v} : Val := {ph_raw}")
            hrn = (
                f"(Combinators.exceptTermOk_eq (r := readNext {self.w_expr} {self.k_expr} ({val(ctx.next_expr)})) "
                f"(t := {n_term_lean}) (by decide +kernel))"
            )
            all_pairs = pend_vars + [("PHASE", ph_v)]
            new_nd = True
        else:
            all_pairs = list(pend_vars)
            new_nd = ctx.next_done

        all_pairs_lean = "[" + ", ".join(f"({lean_str(c)}, {v})" for c, v in all_pairs) + "]"
        own_pairs = [(c, v) for c, v in all_pairs if c not in DIRECTORY_FIELDS]
        dir_pairs = [(c, v) for c, v in all_pairs if c in DIRECTORY_FIELDS]
        has_dir = len(dir_pairs) > 0

        _, hslot = self.prove_var_st("SLOT", ctx)
        _, hid = self.prove_var_st("ID", ctx)
        own_cur, ht = self.prove_stobj(self.kn, ctx)
        dir_cur, hd = self.prove_stobj("FN2-MACHINES", ctx)
        ctrl_cur, hc = self.prove_stobj("FN2-CONTROL", ctx)
        rows_val, hrows = self.prove_call_fn_plain(f"{self.kn}-ROWS", [own_cur], f"[{own_cur}]")
        drows_val, hdrows = self.prove_call_fn_plain("FN2-MACHINES-ROWS", [dir_cur], f"[{dir_cur}]")

        # Fold setters in declaration order for `put_eq_ite`
        def build_fold(pairs_sub, prefix_fn, slot_arg, init_expr):
            steps_acc = []
            cur = init_expr
            for c, v in pairs_sub:
                nxt, hstep = self.prove_call_fn_plain(prefix_fn + c, [slot_arg, v, cur], f"[{slot_arg}, {v}, {cur}]")
                steps_acc.append((c, v, cur, nxt, hstep))
                cur = nxt
            final_expr = cur
            hfold = f"(foldlM_set_nil {self.w_expr} {lean_str(prefix_fn)} {slot_arg} {final_expr})"
            rem_lean = "[]"
            for idx_f in range(len(steps_acc) - 1, -1, -1):
                c, v, acc_in, acc_out, hstep = steps_acc[idx_f]
                hfold = (
                    f"(foldlM_set_cons {self.w_expr} {lean_str(prefix_fn)} {slot_arg} "
                    f"{acc_in} {v} {acc_out} {final_expr} {lean_str(c)} {rem_lean} {hstep} {hfold})"
                )
                rem_lean = "[" + ", ".join(f"({lean_str(x[0])}, {x[1]})" for x in steps_acc[idx_f:]) + "]"
            return final_expr, hfold

        tab_pend, htab = build_fold(own_pairs, f"{self.kn}-SET-", "slot", own_cur)
        dir_pend, hdir = build_fold(dir_pairs, "FN2-MACHINES-SET-", "id", dir_cur)

        stop_w_val = f"({val(self.kinfo['consts']['*FN2-STOP-REASON-MACHINE-WRITE*'])})"
        hreason = f"(by decide +kernel : const {self.w_expr} \"*FN2-STOP-REASON-MACHINE-WRITE*\" = .ok {stop_w_val})"
        stopped_val, hstop = self.prove_call_fn_plain("FN2-CONTROL-RECORD-STOP", [stop_w_val, ctrl_cur], f"[{stop_w_val}, {ctrl_cur}]")

        col_order = [c for c, _ in self.kinfo["columns"]]
        cols_lean = "[" + ", ".join(f"({lean_str(c)}, {col_type_lean(ty)})" for c, ty in self.kinfo["columns"]) + "]"
        hcf_haves = "\n".join(
            f"    have hcf_{idx_p} : (match ({cols_lean} : List (String × ColType)).find? (·.1 == {lean_str(c)}) with "
            f"| some (_, ty) => ty.fits {v} | none => false) = ColType.fits {col_type_lean(self.kinfo['col_map'][c])} {v} := rfl"
            for idx_p, (c, v) in enumerate(all_pairs)
        )
        hcf_rws = ", ".join(f"hcf_{idx_p}" for idx_p in range(len(all_pairs)))
        emp_bool = "false" if has_dir else "true"
        extra_sort_rws = []
        if self.core_mode and not self.kinfo["child_form"]:
            # Order fields in kind column order to match `<KN>-WRITE+F1+...+Fk`!
            sorted_pairs = sorted(all_pairs, key=lambda p: col_order.index(p[0]))
            fits_terms = [f"ColType.fits {col_type_lean(self.kinfo['col_map'][c])} {v}" for c, v in sorted_pairs]
            cond_expr = "(" + " && ".join(fits_terms) + ")"
            hcond_var = self.fresh_let("hcond")
            let_prfs.append(
                f"have {hcond_var} : (natLt slot {rows_val} && "
                f"(({all_pairs_lean}.filter fun p => directoryFields.contains p.1).isEmpty || natLt id {drows_val}) && "
                f"{all_pairs_lean}.all fun (n, v) => match ({self.frame_call}).kind.columns.find? (·.1 == n) with "
                f"| some (_, ty) => ty.fits v | none => false) = ({cond_expr}) := by\n"
                f"    have heb := {self.kcommon_ns}.entry_bounds id {ctx.kids_var} {ctx.snap_hyp}\n"
                f"    have hcols : ({self.frame_call}).kind.columns = {cols_lean} := rfl\n"
                f"    have hdir_emp : ({all_pairs_lean}.filter fun p => directoryFields.contains p.1).isEmpty = {emp_bool} := rfl\n"
                f"{hcf_haves}\n"
                f"    rw [hcols, hdir_emp, hslot_eq, heb.2.1, heb.2.2]\n"
                f"    dsimp only [List.all]\n"
                f"    rw [{hcf_rws}]\n"
                f"    simp only [Bool.or_true, Bool.true_or, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.and_assoc]\n"
                f"    try ac_rfl"
            )
            own_sorted = [p for p in sorted_pairs if p[0] not in DIRECTORY_FIELDS]
            dir_sorted = [p for p in sorted_pairs if p[0] in DIRECTORY_FIELDS]
            tab_final = own_cur
            for c, v in own_sorted:
                tab_final = f"({ident(self.kn + '-SET-' + c)} slot {v} {tab_final})"
            dir_final = dir_cur
            for c, v in dir_sorted:
                dir_final = f"({ident('FN2-MACHINES-SET-' + c)} id {v} {dir_final})"
            if [c for c, _ in own_pairs] != [c for c, _ in own_sorted]:
                ws_p = "[" + ", ".join(f"({self.kinfo['table'].index(c)}, {v})" for c, v in own_pairs) + "]"
                ws_s = "[" + ", ".join(f"({self.kinfo['table'].index(c)}, {v})" for c, v in own_sorted) + "]"
                htab_eq = self.fresh_let("htab_ord")
                let_prfs.append(
                    f"have {htab_eq} : {tab_pend} = {tab_final} :=\n"
                    f"    (Combinators.applyFieldWrites_sort slot {own_cur} {ws_p}).symm.trans "
                    f"(Combinators.applyFieldWrites_sort slot {own_cur} {ws_s})"
                )
                extra_sort_rws.append(htab_eq)
            dir_idx_map = {"READY-PREV": 2, "READY-NEXT": 3, "WAIT-REASON": 4}
            if [c for c, _ in dir_pairs] != [c for c, _ in dir_sorted]:
                ws_p = "[" + ", ".join(f"({dir_idx_map[c]}, {v})" for c, v in dir_pairs) + "]"
                ws_s = "[" + ", ".join(f"({dir_idx_map[c]}, {v})" for c, v in dir_sorted) + "]"
                hdir_eq = self.fresh_let("hdir_ord")
                let_prfs.append(
                    f"have {hdir_eq} : {dir_pend} = {dir_final} :=\n"
                    f"    (Combinators.applyFieldWrites_sort id {dir_cur} {ws_p}).symm.trans "
                    f"(Combinators.applyFieldWrites_sort id {dir_cur} {ws_s})"
                )
                extra_sort_rws.append(hdir_eq)
        else:
            # Child form (`echo`, `scribe`, `cursor`): exact `all_pairs` order, dynamic slot/id bounds!
            fits_terms = [f"ColType.fits {col_type_lean(self.kinfo['col_map'][c])} {v}" for c, v in all_pairs]
            fits_part = " && ".join(fits_terms)
            if has_dir:
                cond_expr = f"(natLt slot {rows_val} && natLt id {drows_val} && ({fits_part}))"
            else:
                cond_expr = f"(natLt slot {rows_val} && ({fits_part}))"
            hcond_var = self.fresh_let("hcond")
            let_prfs.append(
                f"have {hcond_var} : (natLt slot {rows_val} && "
                f"(({all_pairs_lean}.filter fun p => directoryFields.contains p.1).isEmpty || natLt id {drows_val}) && "
                f"{all_pairs_lean}.all fun (n, v) => match ({self.frame_call}).kind.columns.find? (·.1 == n) with "
                f"| some (_, ty) => ty.fits v | none => false) = {cond_expr} := by\n"
                f"    have hcols : ({self.frame_call}).kind.columns = {cols_lean} := rfl\n"
                f"    have hdir_emp : ({all_pairs_lean}.filter fun p => directoryFields.contains p.1).isEmpty = {emp_bool} := rfl\n"
                f"{hcf_haves}\n"
                f"    rw [hcols, hdir_emp]\n"
                f"    dsimp only [List.all]\n"
                f"    rw [{hcf_rws}]\n"
                f"    simp only [Bool.or_true, Bool.true_or, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.and_assoc]"
            )
            tab_final = tab_pend
            dir_final = dir_pend

        hput_var = self.fresh_let("hput")
        let_prfs.append(
            f"have {hput_var} := Combinators.put_eq_ite {self.w_expr} {self.frame_call} {st_s} "
            f"{all_pairs_lean} slot id {own_cur} {dir_cur} {ctrl_cur} {rows_val} {drows_val} "
            f"{tab_final if not extra_sort_rws else tab_pend} "
            f"{dir_final if not extra_sort_rws else dir_pend} {stop_w_val} {stopped_val} "
            f"{cond_expr} {hslot} {hid} {ht} {hd} {hc} {hrows} {hdrows} {hcond_var} {htab} {hdir} {hreason} {hstop}"
        )
        if extra_sort_rws:
            let_prfs.append(f"rw [{', '.join(extra_sort_rws)}] at {hput_var}")

        if has_dir:
            pass_kids = f"(Combinators.patchKids (Combinators.patchKids {ctx.kids_var} {self.own_idx} {tab_final}) {self.dir_idx} {dir_final})"
            self.modified_idxs.update([self.own_idx, self.dir_idx, self.ctrl_idx])
        else:
            pass_kids = f"(Combinators.patchKids {ctx.kids_var} {self.own_idx} {tab_final})"
            self.modified_idxs.update([self.own_idx, self.ctrl_idx])
        fail_kids = f"(Combinators.patchKids {ctx.kids_var} {self.ctrl_idx} {stopped_val})"

        cond_v = self.fresh_let("pcond")
        kids_new = self.fresh_let("kids")
        let_defs.append(f"let {cond_v} : Bool := {cond_expr}")
        let_defs.append(f"let {kids_new} : Fin {self.n_tup} → Val := if {cond_v} then {pass_kids} else {fail_kids}")
        let_prfs.append(f"let {cond_v} : Bool := {cond_expr}")
        let_prfs.append(f"let {kids_new} : Fin {self.n_tup} → Val := if {cond_v} then {pass_kids} else {fail_kids}")

        # Simplify `setStobj` inside `hput_var` to `tupleStobjs`
        hkn_v = self.fresh_let("hkn")
        let_prfs.append(
            f"have {hkn_v} : ({self.frame_call}).kind.name = {lean_str(self.kn)} := rfl\n"
            f"  rw [{hkn_v}, Combinators.setStobj_tupleStobjs {self.tup_expr} {ctx.kids_var} _ _ _ _ _ _ {lean_str(self.kn)} {self.own_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel),\n"
            f"      Combinators.setStobj_tupleStobjs {self.tup_expr} _ _ _ _ _ _ _ \"FN2-MACHINES\" {self.dir_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel),\n"
            f"      Combinators.setStobj_tupleStobjs {self.tup_expr} {ctx.kids_var} _ _ _ _ _ _ \"FN2-CONTROL\" {self.ctrl_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel)] at {hput_var}"
        )
        if not has_dir:
            # Simplify `patchKids (patchKids kids own tab) dir (kids dir)` -> `patchKids kids own tab`
            hdir_id = self.fresh_let("hdir_id")
            let_prfs.append(
                f"have {hdir_id} : Combinators.patchKids (Combinators.patchKids {ctx.kids_var} {self.own_idx} {tab_final}) "
                f"{self.dir_idx} {dir_cur} = Combinators.patchKids {ctx.kids_var} {self.own_idx} {tab_final} := by\n"
                f"    rw [← Combinators.patchKids_ne {ctx.kids_var} {self.own_idx} {self.dir_idx} {tab_final} (by decide) (by decide)]\n"
                f"    exact Combinators.patchKids_self _ {self.dir_idx} (by decide)\n"
                f"  rw [{hdir_id}] at {hput_var}"
            )

        if ctx.next_expr is not None:
            hfl = (
                f"(Combinators.flush_next_some {self.w_expr} {self.frame_call} {st_s} "
                f"({val(ctx.next_expr)}) {n_term_lean} {ph_v} {pairs_val_lean} _ rfl {hpairs} {hrn} {hen} {hput_var})"
            )
        else:
            hfl = (
                f"(Combinators.flush_nonempty_none {self.w_expr} {self.frame_call} {st_s} "
                f"{all_pairs_lean} _ rfl {hpairs} rfl {hput_var})"
            )

        nd1_s = "true" if ctx.next_done else "false"
        nd2_s = "true" if new_nd else "false"
        wk_s = "true" if ctx.woken else "false"
        post_rw = [
            f"rw [st_flush_ite {self.tup_expr} {cond_v} {pass_kids} {fail_kids} "
            f"{self.vars_lean(ctx)} {self.pend_lean(ctx.pending)} {self.next_lean(ctx.next_expr)} {nd1_s} {nd2_s} {wk_s} (0, 0, 0)]"
        ]
        new_ctx = ctx.clone(kids_var=kids_new, pending=[], next_expr=None, next_done=new_nd, snap_hyp=None)
        return let_defs, let_prfs, hfl, post_rw, new_ctx

    def expand_owner_py(self, keys):
        for kw, sexp in keys:
            if kw == ":OWNER":
                lname = str(sexp)
                link = self.kinfo["links"][lname]
                kc = f"*{link['kind']}-KIND*"
                okind = Atom("ROW-" + link["kind_field"]) if link["kind_field"] else Atom(kc)
                return [
                    (k, v) for k, v in keys if k != ":OWNER"
                ] + [
                    (":OKIND", okind),
                    (":OSLOT", Atom("ROW-" + link["slot"])),
                    (":OGEN", Atom("ROW-" + link["gen"])),
                ]
        return list(keys)

    def prove_callee_call(self, call_dict, ctx):
        """Proves `callOp` for an op with `o.callee = some callee` (`:CHILDREN` ops & shared child ops)."""
        op_name = call_dict["op"]
        if op_name not in self.kinfo["ops"]:
            raise UnsupportedArmError(f"unknown op {op_name}")
        op_info = self.kinfo["ops"][op_name]
        callee = op_info["callee"]
        if callee is None:
            raise UnsupportedArmError(f"core-only op {op_name} requires @CORE adapter")
        if callee not in self.fn_defs:
            raise UnsupportedArmError(f"callee {callee} missing from world")
        op_idx = op_info["idx"]
        op_lean = f"world.ops[{op_idx}]!"
        if self.core_mode:
            hfind = (
                f"((Combinators.findOp_coreWorld world coreTuple {lean_str(op_name)} {op_lean} rfl).trans "
                f"(rfl : Except.ok (coreOp coreTuple {op_lean}) = .ok {op_lean}))"
            )
        else:
            hfind = f"(Combinators.findOp_of_find world {lean_str(op_name)} {op_lean} rfl)"

        exp_keys = self.expand_owner_py(call_dict["keys"])
        exp_keys_lean = "[" + ", ".join(f"({lean_str(k)}, {val(v)})" for k, v in exp_keys) + "]"
        c_lean = call_to_lean(call_dict)
        hkeys = f"(by decide +kernel : expandOwner {self.w_expr} {self.k_expr} ({c_lean}).keys = .ok {exp_keys_lean})"

        formals = op_info["formals"]
        sin = op_info["stobjs_in"]
        pos_args = list(call_dict["args"])
        st_s = self.st_lean(ctx)

        def build_actuals(i_f, rem_pos):
            if i_f == len(formals):
                sin_tail = "[" + ", ".join(opt_str_lean(s) for s in sin[i_f:]) + "]"
                return [], "[]", f"(Combinators.actuals_nil {self.w_expr} {self.k_expr} {st_s} {sin_tail} {exp_keys_lean})"
            fm = formals[i_f]
            s_opt = sin[i_f]
            fs_tail = "[" + ", ".join(lean_str(x) for x in formals[i_f + 1:]) + "]"
            ss_tail = "[" + ", ".join(opt_str_lean(x) for x in sin[i_f + 1:]) + "]"
            if s_opt is not None:
                v_s, hs = self.prove_stobj(s_opt, ctx)
                rest_vs, rest_lean, hr = build_actuals(i_f + 1, rem_pos)
                pos_lean = "[" + ", ".join(val(p) for p in rem_pos) + "]"
                all_vs = [v_s] + rest_vs
                all_lean = "[" + ", ".join(all_vs) + "]"
                prf = (
                    f"(Combinators.actuals_stobj {self.w_expr} {self.k_expr} {st_s} "
                    f"{lean_str(fm)} {fs_tail} {lean_str(s_opt)} {ss_tail} {pos_lean} {exp_keys_lean} "
                    f"{v_s} {rest_lean} {hs} {hr})"
                )
                return all_vs, all_lean, prf
            if rem_pos:
                p0 = rem_pos[0]
                v_p, hv = self.prove_ev(p0, ctx)
                rest_vs, rest_lean, hr = build_actuals(i_f + 1, rem_pos[1:])
                ps_lean = "[" + ", ".join(val(p) for p in rem_pos[1:]) + "]"
                all_vs = [v_p] + rest_vs
                all_lean = "[" + ", ".join(all_vs) + "]"
                prf = (
                    f"(Combinators.actuals_pos {self.w_expr} {self.k_expr} {st_s} "
                    f"{lean_str(fm)} {fs_tail} {ss_tail} ({val(p0)}) {ps_lean} {exp_keys_lean} "
                    f"{v_p} {rest_lean} {hv} {hr})"
                )
                return all_vs, all_lean, prf
            # Key or owner default
            found_kv = next(((k, v) for k, v in exp_keys if k == ":" + fm), None)
            if found_kv is not None:
                kw_s, e_s = found_kv
                v_k, hev = self.prove_ev(e_s, ctx)
                hko = (
                    f"(Combinators.keyOrOwner_found {self.w_expr} {self.k_expr} {st_s} "
                    f"{lean_str(fm)} {exp_keys_lean} {lean_str(kw_s)} ({val(e_s)}) {v_k} (by decide +kernel) {hev})"
                )
            elif fm == "OKIND":
                v_k, hv = self.prove_var_st("KIND", ctx)
                hko = f"(Combinators.keyOrOwner_okind {self.w_expr} {self.k_expr} {st_s} {exp_keys_lean} {v_k} (by decide +kernel) {hv})"
            elif fm == "OSLOT":
                v_k, hv = self.prove_var_st("ID", ctx)
                hko = f"(Combinators.keyOrOwner_oslot {self.w_expr} {self.k_expr} {st_s} {exp_keys_lean} {v_k} (by decide +kernel) {hv})"
            elif fm == "OGEN":
                v_k, hv = self.prove_var_st("ROW-GENERATION", ctx)
                hko = f"(Combinators.keyOrOwner_ogen {self.w_expr} {self.k_expr} {st_s} {exp_keys_lean} {v_k} (by decide +kernel) {hv})"
            else:
                raise UnsupportedArmError(f"missing key argument {fm} for {op_name}")
            rest_vs, rest_lean, hr = build_actuals(i_f + 1, [])
            all_vs = [v_k] + rest_vs
            all_lean = "[" + ", ".join(all_vs) + "]"
            prf = (
                f"(Combinators.actuals_key {self.w_expr} {self.k_expr} {st_s} "
                f"{lean_str(fm)} {fs_tail} {ss_tail} {exp_keys_lean} {v_k} {rest_lean} {hko} {hr})"
            )
            return all_vs, all_lean, prf

        act_vs, act_lean, hargs_raw = build_actuals(0, pos_args)
        r_lean, hcall_fn = self.prove_call_fn_plain(callee, act_vs, act_lean)
        fms_all_lean = "[" + ", ".join(lean_str(x) for x in formals) + "]"
        sis_all_lean = "[" + ", ".join(opt_str_lean(x) for x in sin) + "]"
        hcal = f"(rfl : ({op_lean}).callee = some {lean_str(callee)})"
        hargs = (
            f"(by have hfm : ({op_lean}).formals = {fms_all_lean} := rfl; "
            f"have hsi : ({op_lean}).stobjsIn = {sis_all_lean} := rfl; "
            f"rw [hfm, hsi]; exact {hargs_raw})"
        )
        hcall = (
            f"(Combinators.callOp_callee {self.w_expr} {self.k_expr} {st_s} {c_lean} "
            f"{op_lean} {lean_str(callee)} {exp_keys_lean} {act_lean} {r_lean} "
            f"{hfind} {hcal} {hkeys} {hargs} {hcall_fn})"
        )
        return op_info, op_lean, callee, act_vs, r_lean, hfind, hcall

    def prove_bind_outs(self, outs, bvars, r_var, callee, act_vs, ctx):
        """Returns `(let_defs, let_prfs, hbind_lines, new_ctx)`."""
        let_defs = []
        let_prfs = []
        rw_lines = []
        m = len(outs)
        st_s = self.st_lean(ctx)
        bvars_lean = "[" + ", ".join(lean_str(v) for v in bvars) + "]"

        if m == 1 and outs[0] is not None:
            s_out = outs[0]
            idx = self.tup_list.index(s_out)
            self.modified_idxs.add(idx)
            kids_n = self.fresh_let("kids")
            pk = f"(Combinators.patchKids {ctx.kids_var} {idx} {r_var})"
            let_defs.append(f"let {kids_n} : Fin {self.n_tup} → Val := {pk}")
            let_prfs.append(f"let {kids_n} : Fin {self.n_tup} → Val := {pk}")
            hbind = self.fresh_let("hbind")
            let_prfs.append(
                f"have {hbind} : bindOuts {st_s} [some {lean_str(s_out)}] {bvars_lean} {r_var} = "
                f".ok ⟨Combinators.tupleStobjs {self.tup_expr} {kids_n}, {self.vars_lean(ctx)}, "
                f"{self.pend_lean(ctx.pending)}, {self.next_lean(ctx.next_expr)}, "
                f"{'true' if ctx.next_done else 'false'}, {'true' if ctx.woken else 'false'}, (0, 0, 0)⟩ := by\n"
                f"    rw [Combinators.bindOuts_single_stobj, Combinators.setStobj_tupleStobjs {self.tup_expr} "
                f"{ctx.kids_var} _ _ _ _ _ _ {lean_str(s_out)} {idx} {r_var} (by decide +kernel) (by decide +kernel) (by decide +kernel)]"
            )
            return let_defs, let_prfs, hbind, ctx.clone(kids_var=kids_n, snap_hyp=None)

        if m == 1 and outs[0] is None:
            new_lvs = list(ctx.local_vars)
            if bvars:
                lv_n = self.fresh_let("rv")
                let_defs.append(f"let {lv_n} : Val := {r_var}")
                let_prfs.append(f"let {lv_n} : Val := {r_var}")
                new_lvs.insert(0, (bvars[0], lv_n))
            new_ctx = ctx.clone(local_vars=new_lvs)
            hbind = self.fresh_let("hbind")
            let_prfs.append(
                f"have {hbind} : bindOuts {st_s} [none] {bvars_lean} {r_var} = .ok {self.st_lean(new_ctx)} := by\n"
                f"    rw [Combinators.bindOuts_single_val]; rfl"
            )
            return let_defs, let_prfs, hbind, new_ctx

        # Multi-output (`m >= 2`): requires `ServedOps.<callee>_isListN_<m>`!
        if self.tuple_analyzer is None or not self.tuple_analyzer.ensure(callee, m):
            raise UnsupportedArmError(f"cannot prove IsListN {m} for {callee}")
        self.used_multi_ops.add((callee, m))
        isl_thm = f"(ServedOps.{islistN_thm_name(callee, m)}" + ("" if not act_vs else " " + " ".join(act_vs)) + ")"

        cur_kids = ctx.kids_var
        cur_lvs = list(ctx.local_vars)
        rem_bvars = list(bvars)
        stobj_rws = []
        for j, s_opt in enumerate(outs):
            rj = f"(Native.nth (.int {j}) {r_var})"
            if s_opt is None:
                if rem_bvars:
                    v_name = rem_bvars.pop(0)
                    lv_n = self.fresh_let("rv")
                    let_defs.append(f"let {lv_n} : Val := {rj}")
                    let_prfs.append(f"let {lv_n} : Val := {rj}")
                    cur_lvs.insert(0, (v_name, lv_n))
            else:
                idx = self.tup_list.index(s_opt)
                self.modified_idxs.add(idx)
                stobj_rws.append((s_opt, idx, rj, cur_kids))
                cur_kids = f"(Combinators.patchKids {cur_kids} {idx} {rj})"

        kids_n = self.fresh_let("kids")
        let_defs.append(f"let {kids_n} : Fin {self.n_tup} → Val := {cur_kids}")
        let_prfs.append(f"let {kids_n} : Fin {self.n_tup} → Val := {cur_kids}")
        new_ctx = ctx.clone(local_vars=cur_lvs, kids_var=kids_n, snap_hyp=None)
        outs_lean = "[" + ", ".join(opt_str_lean(s) for s in outs) + "]"
        hbind = self.fresh_let("hbind")
        set_stobj_lines = "\n".join(
            f"    rw [Combinators.setStobj_tupleStobjs {self.tup_expr} _ _ _ _ _ _ _ {lean_str(sn)} {ix} _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]"
            for sn, ix, _, _ in stobj_rws
        )
        let_prfs.append(
            f"have {hbind} : bindOuts {st_s} {outs_lean} {bvars_lean} {r_var} = .ok {self.st_lean(new_ctx)} := by\n"
            f"    rw [Combinators.bindOuts_multi {st_s} {outs_lean} {bvars_lean} {r_var} (by decide) rfl {isl_thm}]\n"
            f"    dsimp only [List.range, List.range.loop, List.map, Nat.add_zero, Int.ofNat_eq_natCast, "
            f"Combinators.bindOuts_go_some, Combinators.bindOuts_go_none_cons, Combinators.bindOuts_go_none_nil, Combinators.bindOuts_go_nil]\n"
            + (set_stobj_lines + "\n" if set_stobj_lines else "")
            + "    rfl"
        )
        return let_defs, let_prfs, hbind, new_ctx

    def node_sig_parts(self, entry_ctx):
        lv_names = [lv for _, lv in entry_ctx.local_vars]
        val_binders = " ".join(f"({v} : Val)" for v in self.val_params + lv_names)
        val_args = " ".join(self.val_params + lv_names)
        kids_binders = f"(kids0 {entry_ctx.kids_var} : Fin {self.n_tup} → Val)"
        kids_args = f"kids0 {entry_ctx.kids_var}"
        extra_hyps = []
        extra_args = []
        if self.core_mode and not self.kinfo["child_form"] and entry_ctx.snap_hyp is not None:
            extra_hyps.append(f"(hslot_eq : slot = «FN2-MACHINE-SLOT» id (Combinators.tupleImage {entry_ctx.kids_var}))")
            extra_args.append("hslot_eq")
            extra_hyps.append(
                f"({entry_ctx.snap_hyp} : {ident(self.kn + '-SNAPSHOT-READ-CODE')} id "
                f"(Combinators.tupleImage {entry_ctx.kids_var}) = .sym \":OK\")"
            )
            extra_args.append(entry_ctx.snap_hyp)
        return val_binders, val_args, kids_binders, kids_args, extra_hyps, extra_args

    def make_call_expr(self, node_info, ctx):
        lv_names = [lv for _, lv in ctx.local_vars]
        all_args = self.val_params + lv_names + ["kids0", ctx.kids_var]
        return f"({node_info['name']} {' '.join(all_args)})"

    def make_run_call(self, node_info, ctx, fuel_expr, hfuel_expr):
        lv_names = [lv for _, lv in ctx.local_vars]
        all_args = self.val_params + lv_names + ["kids0", ctx.kids_var, f"({fuel_expr})", hfuel_expr]
        if self.core_mode and not self.kinfo["child_form"] and ctx.snap_hyp is not None:
            all_args.extend(["hslot_eq", ctx.snap_hyp])
        return f"({node_info['name']}_run {' '.join(all_args)})"

    def make_len_call(self, node_info, ctx):
        lv_names = [lv for _, lv in ctx.local_vars]
        all_args = self.val_params + lv_names + ["kids0", ctx.kids_var]
        return f"({node_info['name']}_len {' '.join(all_args)})"

    def compile_node(self, steps, entry_ctx):
        if not steps:
            raise UnsupportedArmError("empty step sequence")

        cur_ctx = entry_ctx.clone()
        def_lines = []
        prf_lines = []
        len_lets = []
        consumed = 0
        idx_s = 0

        while idx_s < len(steps):
            st = steps[idx_s]
            rest = steps[idx_s + 1:]
            rest_lean = "[" + ", ".join(step_to_lean(x) for x in rest) + "]"
            h = st[0]

            if h == "let":
                _, v_name, e_sexp = st
                v_lean, hev = self.prove_ev(e_sexp, cur_ctx)
                lv = self.fresh_let("lv")
                def_lines.append(f"  let {lv} : Val := {v_lean}")
                len_lets.append(f"  let {lv} : Val := {v_lean}")
                prf_lines.append(f"  let {lv} : Val := {v_lean}")
                prf_lines.append(
                    f"  rw [Combinators.run_let {self.w_expr} {self.frame_call} _ {self.st_lean(cur_ctx)} "
                    f"{lean_str(v_name)} ({val(e_sexp)}) {rest_lean} {lv} {hev}]\n"
                    f"  dsimp only []"
                )
                cur_ctx = cur_ctx.clone(local_vars=[(v_name, lv)] + cur_ctx.local_vars)
                consumed += 1
                idx_s += 1
                continue

            if h == "set":
                _, pairs = st
                pairs_lean = "[" + ", ".join(f"({lean_str(f)}, {val(e)})" for f, e in pairs) + "]"
                prf_lines.append(
                    f"  rw [Combinators.run_set {self.w_expr} {self.frame_call} _ {self.st_lean(cur_ctx)} "
                    f"{pairs_lean} {rest_lean} (by dsimp only [List.any]; decide)]\n"
                    f"  dsimp only [List.nil_append, List.cons_append]"
                )
                cur_ctx = cur_ctx.clone(pending=cur_ctx.pending + list(pairs))
                consumed += 1
                idx_s += 1
                continue

            if h == "next":
                _, ph_sexp = st
                prf_lines.append(
                    f"  rw [Combinators.run_next {self.w_expr} {self.frame_call} _ {self.st_lean(cur_ctx)} "
                    f"({val(ph_sexp)}) {rest_lean} rfl rfl]\n"
                    f"  dsimp only []"
                )
                cur_ctx = cur_ctx.clone(next_expr=ph_sexp)
                consumed += 1
                idx_s += 1
                continue

            if h == "wake_row":
                if self.core_mode and not self.kinfo["child_form"] and rest:
                    # If subsequent steps need `snap_hyp`, defer to Milestone 2 if flush follows
                    pass
                _, e_sexp = st
                v_lean, hev = self.prove_ev(e_sexp, cur_ctx)
                dir_cur, hd = self.prove_stobj("FN2-MACHINES", cur_ctx)
                ctrl_cur, hc = self.prove_stobj("FN2-CONTROL", cur_ctx)
                r_val, hcall = self.prove_call_fn_plain(
                    "FN2-MACHINES-WAKE-ROW", [v_lean, dir_cur, ctrl_cur], f"[{v_lean}, {dir_cur}, {ctrl_cur}]"
                )
                wr_v = self.fresh_let("wr")
                kids_n = self.fresh_let("kids")
                pk = f"(Combinators.patchKids (Combinators.patchKids {cur_ctx.kids_var} {self.dir_idx} {wr_v}.car) {self.ctrl_idx} {wr_v}.cdr.car)"
                self.modified_idxs.update([self.dir_idx, self.ctrl_idx])
                def_lines.append(f"  let {wr_v} : Val := {r_val}")
                def_lines.append(f"  let {kids_n} : Fin {self.n_tup} → Val := {pk}")
                len_lets.extend([f"  let {wr_v} : Val := {r_val}", f"  let {kids_n} : Fin {self.n_tup} → Val := {pk}"])
                prf_lines.append(f"  let {wr_v} : Val := {r_val}")
                prf_lines.append(f"  let {kids_n} : Fin {self.n_tup} → Val := {pk}")
                prf_lines.append(
                    f"  rw [Combinators.run_wakeRow {self.w_expr} {self.frame_call} _ {self.st_lean(cur_ctx)} "
                    f"({val(e_sexp)}) {rest_lean} {v_lean} {dir_cur} {ctrl_cur} {wr_v} rfl {hev} {hd} {hc} {hcall},\n"
                    f"      Combinators.setStobj_tupleStobjs {self.tup_expr} {cur_ctx.kids_var} _ _ _ _ _ _ \"FN2-MACHINES\" {self.dir_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel),\n"
                    f"      Combinators.setStobj_tupleStobjs {self.tup_expr} _ _ _ _ _ _ _ \"FN2-CONTROL\" {self.ctrl_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]\n"
                    f"  dsimp only []"
                )
                cur_ctx = cur_ctx.clone(kids_var=kids_n, woken=True, snap_hyp=None)
                consumed += 1
                idx_s += 1
                continue

            if h == "do":
                _, vs, call_d, ag, acc, when_, else_, cases = st
                if when_ is not None:
                    raise UnsupportedArmError(":do :when deferred")
                op_info = self.kinfo["ops"].get(call_d["op"])
                if op_info is None or op_info["callee"] is None:
                    raise UnsupportedArmError(f"core op {call_d['op']} deferred")
                if op_info["answers"][0] == "none":
                    ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
                    def_lines.extend("  " + x for x in ld)
                    len_lets.extend("  " + x for x in ld)
                    prf_lines.extend("  " + x for x in lp)
                    _, op_lean, callee, act_vs, r_lean, hfind, hcall = self.prove_callee_call(call_d, fl_ctx)
                    rv_raw = self.fresh_let("op_r")
                    def_lines.append(f"  let {rv_raw} : Val := {r_lean}")
                    len_lets.append(f"  let {rv_raw} : Val := {r_lean}")
                    prf_lines.append(f"  let {rv_raw} : Val := {r_lean}")
                    bd, bp, hbind, nxt_ctx = self.prove_bind_outs(op_info["stobjs_out"], vs, rv_raw, callee, act_vs, fl_ctx)
                    def_lines.extend("  " + x for x in bd)
                    len_lets.extend("  " + x for x in bd)
                    prf_lines.extend("  " + x for x in bp)
                    hfl_v = self.fresh_let("hfl")
                    prf_lines.append(f"  have {hfl_v} := {hfl}")
                    for rw_l in prw:
                        prf_lines.append(f"  {rw_l} at {hfl_v}")
                    acc_l = "[" + ", ".join(val(c) for c in acc) + "]"
                    el_l = "[" + ", ".join(val(e) for e in else_) + "]"
                    cs_l = "[" + ", ".join(f"({codes_opt_lean(cs)}, [{', '.join(step_to_lean(x) for x in bs)}])" for cs, bs in cases) + "]"
                    vs_l = "[" + ", ".join(lean_str(v) for v in vs) + "]"
                    prf_lines.append(
                        f"  rw [Combinators.run_do_none {self.w_expr} {self.frame_call} _ {self.st_lean(cur_ctx)} "
                        f"{self.st_lean(fl_ctx)} {self.st_lean(nxt_ctx)} {vs_l} {call_to_lean(call_d)} "
                        f"{'true' if ag else 'false'} {acc_l} {el_l} {cs_l} {rest_lean} {op_lean} {rv_raw} "
                        f"{hfl_v} {hfind} {hcall} {hbind} rfl]"
                    )
                    cur_ctx = nxt_ctx
                    consumed += 1
                    idx_s += 1
                    continue

            # Branching or terminal step ends `while` loop
            break

        # Dispatch final branching or terminal step `st = steps[idx_s]`
        st = steps[idx_s]
        rest = steps[idx_s + 1:]
        rest_lean = "[" + ", ".join(step_to_lean(x) for x in rest) + "]"
        h = st[0]
        total_depth = None
        ret_expr = None
        end_prf_lines = []
        len_body = "rfl"

        if h == "if":
            _, c_sexp, a_steps, b_steps = st
            vc, hc = self.prove_ev(c_sexp, cur_ctx)
            na = self.compile_node(a_steps, cur_ctx)
            nb = self.compile_node(b_steps, cur_ctx)
            child_d = max(na["depth"], nb["depth"])
            total_depth = consumed + 1 + child_d
            ca = self.make_call_expr(na, cur_ctx)
            cb = self.make_call_expr(nb, cur_ctx)
            ret_expr = f"if ({vc}).truthy then {ca} else {cb}"
            len_body = (
                f"by_cases h : ({vc}).truthy = true\n"
                f"  · rw [if_pos h]; exact {self.make_len_call(na, cur_ctx)}\n"
                f"  · rw [if_neg h]; exact {self.make_len_call(nb, cur_ctx)}"
            )
            a_l = "[" + ", ".join(step_to_lean(x) for x in a_steps) + "]"
            b_l = "[" + ", ".join(step_to_lean(x) for x in b_steps) + "]"
            ra = self.make_run_call(na, cur_ctx, "fuel'", "(by omega)")
            rb = self.make_run_call(nb, cur_ctx, "fuel'", "(by omega)")
            end_prf_lines += [
                f"  refine Combinators.run_if {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"({val(c_sexp)}) {a_l} {b_l} {rest_lean} {vc} _ {hc} ?_ ?_",
                f"  · intro ht; rw [ArmOut.toChild_ite, if_pos ht]; exact {ra}",
                f"  · intro htf; have htn : ¬(({vc}).truthy = true) := Bool.eq_false_iff.mp htf",
                f"    rw [ArmOut.toChild_ite, if_neg htn]; exact {rb}",
            ]

        elif h == "cond":
            _, clauses = st
            if not clauses:
                raise UnsupportedArmError("empty :cond")
            # Desugar `:cond` recursively over clauses: note `run_cond_cons` keeps `fuel + 1`!
            c0, s0 = clauses[0]
            if len(clauses) == 1 and isinstance(c0, Atom) and str(c0) == "T":
                n0 = self.compile_node(s0, cur_ctx)
                total_depth = consumed + 1 + n0["depth"]
                ret_expr = self.make_call_expr(n0, cur_ctx)
                len_body = f"exact {self.make_len_call(n0, cur_ctx)}"
                vc, hc = self.prove_ev(c0, cur_ctx)
                s0_l = "[" + ", ".join(step_to_lean(x) for x in s0) + "]"
                r0 = self.make_run_call(n0, cur_ctx, "fuel'", "(by omega)")
                end_prf_lines += [
                    f"  rw [Combinators.run_cond_true {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"({val(c0)}) {s0_l} [] {rest_lean} {vc} {hc} rfl]",
                    f"  exact {r0}",
                ]
            elif len(clauses) >= 2:
                vc, hc = self.prove_ev(c0, cur_ctx)
                na = self.compile_node(s0, cur_ctx)
                nb = self.compile_node([("cond", clauses[1:])] + rest, cur_ctx)
                # Note `nb` consumes `fuel' + 1` in `run_cond_cons`, so `nb["depth"] ≤ fuel' + 1` -> `nb["depth"] - 1 ≤ fuel'`!
                child_d = max(na["depth"], max(0, nb["depth"] - 1))
                total_depth = consumed + 1 + child_d
                ca = self.make_call_expr(na, cur_ctx)
                cb = self.make_call_expr(nb, cur_ctx)
                ret_expr = f"if ({vc}).truthy then {ca} else {cb}"
                len_body = (
                    f"by_cases h : ({vc}).truthy = true\n"
                    f"  · rw [if_pos h]; exact {self.make_len_call(na, cur_ctx)}\n"
                    f"  · rw [if_neg h]; exact {self.make_len_call(nb, cur_ctx)}"
                )
                s0_l = "[" + ", ".join(step_to_lean(x) for x in s0) + "]"
                more_l = "[" + ", ".join(f"({val(c)}, [{', '.join(step_to_lean(x) for x in bs)}])" for c, bs in clauses[1:]) + "]"
                ra = self.make_run_call(na, cur_ctx, "fuel'", "(by omega)")
                rb = self.make_run_call(nb, cur_ctx, "fuel' + 1", "(by omega)")
                end_prf_lines += [
                    f"  refine Combinators.run_cond_cons {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"({val(c0)}) {s0_l} {more_l} {rest_lean} {vc} _ {hc} ?_ ?_",
                    f"  · intro ht; rw [ArmOut.toChild_ite, if_pos ht]; exact {ra}",
                    f"  · intro htf; have htn : ¬(({vc}).truthy = true) := Bool.eq_false_iff.mp htf",
                    f"    rw [ArmOut.toChild_ite, if_neg htn]; exact {rb}",
                ]
            else:
                raise UnsupportedArmError("malformed :cond without T fallback")

        elif h == "case":
            _, key_sexp, arms = st
            if not arms or arms[-1][0] is not None:
                raise UnsupportedArmError(":case without trailing :otherwise")
            kv, hk = self.prove_ev(key_sexp, cur_ctx)
            kv_v = self.fresh_let("ckv")
            def_lines.append(f"  let {kv_v} : Val := {kv}")
            len_lets.append(f"  let {kv_v} : Val := {kv}")
            prf_lines.append(f"  let {kv_v} : Val := {kv}")
            child_nodes = [(cs, self.compile_node(bs, cur_ctx)) for cs, bs in arms]
            child_d = max(cn["depth"] for _, cn in child_nodes)
            total_depth = consumed + 1 + child_d

            # Build nested `if codeIn kv_v [...]` expression from back to front
            cur_ret = self.make_call_expr(child_nodes[-1][1], cur_ctx)
            for cs, cn in reversed(child_nodes[:-1]):
                cs_lean = "[" + ", ".join(val(c) for c in cs) + "]"
                cur_ret = f"(if codeIn {kv_v} {cs_lean} then {self.make_call_expr(cn, cur_ctx)} else {cur_ret})"
            ret_expr = cur_ret

            # Build `len` proof
            len_lines = []
            for idx_c, (cs, cn) in enumerate(child_nodes[:-1]):
                pad = "  " * idx_c
                cs_lean = "[" + ", ".join(val(c) for c in cs) + "]"
                len_lines.append(f"{pad}by_cases h_{idx_c} : codeIn {kv_v} {cs_lean} = true")
                len_lines.append(f"{pad}· rw [if_pos h_{idx_c}]; exact {self.make_len_call(cn, cur_ctx)}")
                len_lines.append(f"{pad}· rw [if_neg h_{idx_c}]")
            len_lines.append(f"{'  ' * (len(child_nodes) - 1)}exact {self.make_len_call(child_nodes[-1][1], cur_ctx)}")
            len_body = "\n  ".join(len_lines)

            arms_lean = "[" + ", ".join(f"({codes_opt_lean(cs)}, [{', '.join(step_to_lean(x) for x in bs)}])" for cs, bs in arms) + "]"
            end_prf_lines.append(
                f"  rw [Combinators.run_case_step {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"({val(key_sexp)}) {arms_lean} {rest_lean} {kv_v} {hk}]"
            )
            end_prf_lines.append("  dsimp only [List.find?]")
            for idx_c, (cs, cn) in enumerate(child_nodes[:-1]):
                pad = "  " * (idx_c + 1)
                cs_lean = "[" + ", ".join(val(c) for c in cs) + "]"
                hc_name = f"hc_{idx_c}"
                end_prf_lines.append(f"{pad}by_cases {hc_name} : codeIn {kv_v} {cs_lean} = true")
                end_prf_lines.append(
                    f"{pad}· simp (config := {{ zetaDelta := true }}) only [{hc_name}, ↓reduceIte, ArmOut.toChild_ite]\n"
                    f"{pad}  exact {self.make_run_call(cn, cur_ctx, 'fuel\'', '(by omega)')}"
                )
                end_prf_lines.append(
                    f"{pad}· have {hc_name}_f : codeIn {kv_v} {cs_lean} = false := Bool.eq_false_iff.mpr {hc_name}\n"
                    f"{pad}  simp (config := {{ zetaDelta := true }}) only [{hc_name}, {hc_name}_f, Bool.false_eq_true, ↓reduceIte, ArmOut.toChild_ite]"
                )
            end_prf_lines.append(f"{'  ' * len(child_nodes)}exact {self.make_run_call(child_nodes[-1][1], cur_ctx, 'fuel\'', '(by omega)')}")

        elif h == "do":
            # Answered `:do` (`when_ is None`, `op_info["answers"][0] != "none"`)
            _, vs, call_d, ag, acc, when_, else_, cases = st
            if not vs:
                raise UnsupportedArmError(":do with answers binds no variable")
            op_info = self.kinfo["ops"][call_d["op"]]
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            _, op_lean, callee, act_vs, r_lean, hfind, hcall = self.prove_callee_call(call_d, fl_ctx)
            rv_raw = self.fresh_let("op_r")
            def_lines.append(f"  let {rv_raw} : Val := {r_lean}")
            len_lets.append(f"  let {rv_raw} : Val := {r_lean}")
            prf_lines.append(f"  let {rv_raw} : Val := {r_lean}")
            bd, bp, hbind, nxt_ctx = self.prove_bind_outs(op_info["stobjs_out"], vs, rv_raw, callee, act_vs, fl_ctx)
            def_lines.extend("  " + x for x in bd)
            len_lets.extend("  " + x for x in bd)
            prf_lines.extend("  " + x for x in bp)
            code_v, hcode = self.prove_var_st(vs[0], nxt_ctx)
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")

            # Determine branches in exact interpreter order!
            case_code_strs = [show(c) for cs, _ in cases if cs is not None for c in cs]
            if ag:
                acc_sexps = list(acc)
            elif op_info["answers"][0] == "list":
                ans_strs = [show(x) for x in op_info["answers"][1]]
                acc_sexps = [] if (":OK" in case_code_strs or ":OK" not in ans_strs) else [Atom(":OK")]
            else:
                acc_sexps = [] if ":OK" in case_code_strs else [Atom(":OK")]

            v0_l = lean_str(vs[0])
            vs_rest_l = "[" + ", ".join(lean_str(v) for v in vs[1:]) + "]"
            acc_l = "[" + ", ".join(val(c) for c in acc) + "]"
            el_l = "[" + ", ".join(val(e) for e in else_) + "]"
            cs_l = "[" + ", ".join(f"({codes_opt_lean(cs)}, [{', '.join(step_to_lean(x) for x in bs)}])" for cs, bs in cases) + "]"
            if op_info["answers"][0] == "open":
                ans_lean = "Answers.open_"
            else:
                ans_lean = f"(Answers.list [{', '.join(val(x) for x in op_info['answers'][1])}])"
            flts_all_lean = "[" + ", ".join(val(c) for c in op_info["faults"]) + "]"
            acc_res_lean = "[" + ", ".join(val(c) for c in acc_sexps) + "]"
            hnans_prf = f"(by have ha : ({op_lean}).answers = {ans_lean} := rfl; rw [ha]; intro h; cases h)"
            end_prf_lines.append(f"  have hans_eq : ({op_lean}).answers = {ans_lean} := rfl")
            end_prf_lines.append(f"  have hflts_eq : ({op_lean}).faults = {flts_all_lean} := rfl")
            end_prf_lines.append(
                f"  rw [Combinators.run_do_answers {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"{self.st_lean(fl_ctx)} {self.st_lean(nxt_ctx)} {v0_l} {vs_rest_l} {call_to_lean(call_d)} "
                f"{'true' if ag else 'false'} {acc_l} {el_l} {cs_l} {rest_lean} {op_lean} {rv_raw} {code_v} "
                f"{hfl_v} {hfind} {hcall} {hbind} {hnans_prf} {hcode}]"
            )
            end_prf_lines.append(f"  rw [hans_eq, hflts_eq]")
            end_prf_lines.append(
                f"  have hacc_eq : (let caseCodes := ({cs_l} : List (Option (List Val) × List Step)).flatMap fun (cs, _) => cs.getD []; "
                f"let ok := Val.kw \"OK\"; "
                f"if {'true' if ag else 'false'} = true then ({acc_l} : List Val) "
                f"else match {ans_lean} with "
                f"| .list l => if (caseCodes.contains ok || !l.contains ok) = true then [] else [ok] "
                f"| _ => if caseCodes.contains ok = true then [] else [ok]) = {acc_res_lean} := by decide +kernel"
            )
            end_prf_lines.append("  dsimp only []; rw [hacc_eq]")
            end_prf_lines.append(
                f"  dsimp only [{self.prefix}_frame, List.find?, Option.isNone, List.isEmpty, "
                f"Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, faultRoute, List.getLast?]"
            )

            branches = []  # [(cond_lean_bool, child_node), ...] + final fallback `fallback_node`
            if acc_sexps:
                branches.append((f"codeIn {code_v} {acc_res_lean}", self.compile_node(rest, nxt_ctx)))
            else:
                # `codeIn code []` is `false` definitionally!
                end_prf_lines.append("  dsimp only [codeIn, List.contains, Bool.false_eq_true, ↓reduceIte]")

            other_steps = None
            for cs, bs in cases:
                if cs is None:
                    if other_steps is None:
                        other_steps = bs
                else:
                    cs_lean = "[" + ", ".join(val(c) for c in cs) + "]"
                    branches.append((f"codeIn {code_v} {cs_lean}", self.compile_node(bs, nxt_ctx)))

            if other_steps is not None:
                fallback_node = self.compile_node(other_steps, nxt_ctx)
            elif self.refusal_steps:
                ref_stops = len(self.refusal_steps) > 0 and self.refusal_steps[-1][0] == "stop"
                if op_info["answers"][0] == "list" and not ref_stops and op_info["faults"]:
                    flts_lean = "[" + ", ".join(val(c) for c in op_info["faults"]) + "]"
                    branches.append((f"({flts_lean} : List Val).contains {code_v}", self.compile_node([("stop", "MACHINE-PHASE", None)], nxt_ctx)))
                fallback_node = self.compile_node(self.refusal_steps, nxt_ctx)
            else:
                fallback_node = self.compile_node([("stop", "MACHINE-CONTRACT", None)], nxt_ctx)

            all_cn = [cn for _, cn in branches] + [fallback_node]
            total_depth = consumed + 1 + max(cn["depth"] for cn in all_cn)

            cur_ret = self.make_call_expr(fallback_node, nxt_ctx)
            for cond_b, cn in reversed(branches):
                cur_ret = f"(if {cond_b} then {self.make_call_expr(cn, nxt_ctx)} else {cur_ret})"
            ret_expr = cur_ret

            len_lines = []
            for idx_b, (cond_b, cn) in enumerate(branches):
                pad = "  " * idx_b
                len_lines.append(f"{pad}by_cases h_{idx_b} : ({cond_b}) = true")
                len_lines.append(f"{pad}· rw [if_pos h_{idx_b}]; exact {self.make_len_call(cn, nxt_ctx)}")
                len_lines.append(f"{pad}· rw [if_neg h_{idx_b}]")
            len_lines.append(f"{'  ' * len(branches)}exact {self.make_len_call(fallback_node, nxt_ctx)}")
            len_body = "\n  ".join(len_lines)

            for idx_b, (cond_b, cn) in enumerate(branches):
                pad = "  " * (idx_b + 1)
                hb = f"hdo_{idx_b}"
                end_prf_lines.append(f"{pad}by_cases {hb} : ({cond_b}) = true")
                end_prf_lines.append(
                    f"{pad}· simp (config := {{ zetaDelta := true }}) only [codeIn] at {hb} ⊢\n"
                    f"{pad}  simp (config := {{ zetaDelta := true }}) only [{hb}, ↓reduceIte, Bool.true_and, ArmOut.toChild_ite]\n"
                    f"{pad}  exact {self.make_run_call(cn, nxt_ctx, 'fuel\'', '(by omega)')}"
                )
                end_prf_lines.append(
                    f"{pad}· have {hb}_f : ({cond_b}) = false := Bool.eq_false_iff.mpr {hb}\n"
                    f"{pad}  simp (config := {{ zetaDelta := true }}) only [codeIn] at {hb} {hb}_f ⊢\n"
                    f"{pad}  simp (config := {{ zetaDelta := true }}) only [{hb}, {hb}_f, Bool.false_eq_true, Bool.and_false, ↓reduceIte, ArmOut.toChild_ite]"
                )
            end_prf_lines.append(f"{'  ' * (len(branches) + 1)}exact {self.make_run_call(fallback_node, nxt_ctx, 'fuel\'', '(by omega)')}")

        elif h == "issue":
            _, call_d, ok_s, rf_s = st
            op_info = self.kinfo["ops"].get(call_d["op"])
            if op_info is None or op_info["callee"] is None:
                raise UnsupportedArmError(f"core issue op {call_d['op']} deferred")
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            _, op_lean, callee, act_vs, r_lean, _, hcall = self.prove_callee_call(call_d, fl_ctx)
            rv_raw = self.fresh_let("iss_r")
            def_lines.append(f"  let {rv_raw} : Val := {r_lean}")
            len_lets.append(f"  let {rv_raw} : Val := {r_lean}")
            prf_lines.append(f"  let {rv_raw} : Val := {r_lean}")
            iss_vars = ["FN2-ISSUE-CODE", "FN2-ISSUE-OP", "FN2-ISSUE-OPGEN"]
            bd, bp, hbind, nxt_ctx = self.prove_bind_outs(op_info["stobjs_out"], iss_vars, rv_raw, callee, act_vs, fl_ctx)
            def_lines.extend("  " + x for x in bd)
            len_lets.extend("  " + x for x in bd)
            prf_lines.extend("  " + x for x in bp)
            code_v, hcode = self.prove_var_st("FN2-ISSUE-CODE", nxt_ctx)
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")

            n_ok = self.compile_node(ok_s, nxt_ctx)
            n_exh = self.compile_node(rf_s + [("park", "OPERATION", None, None, None, [])], nxt_ctx)
            n_ref = self.compile_node(rf_s + (self.refusal_steps if self.refusal_steps else [("halt",)]), nxt_ctx)
            total_depth = consumed + 1 + max(n_ok["depth"], n_exh["depth"], n_ref["depth"])
            ret_expr = (
                f"(if {code_v} == Val.kw \"OK\" then {self.make_call_expr(n_ok, nxt_ctx)} "
                f"else if {code_v} == Val.kw \"EXHAUSTED\" then {self.make_call_expr(n_exh, nxt_ctx)} "
                f"else {self.make_call_expr(n_ref, nxt_ctx)})"
            )
            len_body = (
                f"by_cases h1 : ({code_v} == Val.kw \"OK\") = true\n"
                f"  · rw [if_pos h1]; exact {self.make_len_call(n_ok, nxt_ctx)}\n"
                f"  · rw [if_neg h1]; by_cases h2 : ({code_v} == Val.kw \"EXHAUSTED\") = true\n"
                f"    · rw [if_pos h2]; exact {self.make_len_call(n_exh, nxt_ctx)}\n"
                f"    · rw [if_neg h2]; exact {self.make_len_call(n_ref, nxt_ctx)}"
            )
            ok_l = "[" + ", ".join(step_to_lean(x) for x in ok_s) + "]"
            rf_l = "[" + ", ".join(step_to_lean(x) for x in rf_s) + "]"
            end_prf_lines += [
                f"  rw [Combinators.run_issue {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"{self.st_lean(fl_ctx)} {self.st_lean(nxt_ctx)} {call_to_lean(call_d)} {ok_l} {rf_l} {rest_lean} "
                f"{op_lean} {rv_raw} {code_v} {hfl_v} {hcall} {hbind} {hcode}]",
                f"  dsimp only [{self.prefix}_frame, List.isEmpty, ↓reduceIte]",
                f"  by_cases h1 : ({code_v} == Val.kw \"OK\") = true",
                f"  · simp (config := {{ zetaDelta := true }}) only [h1, ↓reduceIte, ArmOut.toChild_ite]; exact {self.make_run_call(n_ok, nxt_ctx, 'fuel\'', '(by omega)')}",
                f"  · have h1f : ({code_v} == Val.kw \"OK\") = false := Bool.eq_false_iff.mpr h1",
                f"    simp (config := {{ zetaDelta := true }}) only [h1, h1f, Bool.false_eq_true, ↓reduceIte, ArmOut.toChild_ite]",
                f"    by_cases h2 : ({code_v} == Val.kw \"EXHAUSTED\") = true",
                f"    · simp (config := {{ zetaDelta := true }}) only [h2, ↓reduceIte, ArmOut.toChild_ite]; exact {self.make_run_call(n_exh, nxt_ctx, 'fuel\'', '(by omega)')}",
                f"    · have h2f : ({code_v} == Val.kw \"EXHAUSTED\") = false := Bool.eq_false_iff.mpr h2",
                f"      simp (config := {{ zetaDelta := true }}) only [h2, h2f, Bool.false_eq_true, ↓reduceIte, ArmOut.toChild_ite]; exact {self.make_run_call(n_ref, nxt_ctx, 'fuel\'', '(by omega)')}",
            ]

        elif h == "goto":
            _, sub_name = st
            if self.subarm_mod is None or sub_name not in self.subarm_mod:
                raise UnsupportedArmError(f"subarm {sub_name} not available")
            sub_meta = self.subarm_mod[sub_name]
            self.used_subarms.add(sub_name)
            self.modified_idxs.update(sub_meta["modified_idxs"])
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")
            _, hid = self.prove_var_st("ID", fl_ctx)
            _, hslot = self.prove_var_st("SLOT", fl_ctx)
            si = self.kinfo["subarm_idx"][sub_name]
            sub_arm_lean = f"kObj.subarms[{si}]!"
            hreads = f"({self.kcommon_ns}.{'core_row_reads' if self.core_mode else 'child_row_reads'} id slot {fl_ctx.kids_var})"
            total_depth = consumed + 1 + sub_meta["depth"]
            sub_args = " ".join(self.val_params + [fl_ctx.kids_var, fl_ctx.kids_var])
            ret_expr = f"({sub_meta['out_fn']} {sub_args})"
            len_body = f"exact ({sub_meta['len_fn']} {sub_args})"
            end_prf_lines += [
                f"  rw [Combinators.run_goto {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"{self.st_lean(fl_ctx)} {lean_str(sub_name)} {rest_lean} {sub_arm_lean} id slot _ "
                f"{sub_meta['decl_fn']} {hfl_v} rfl {hid} {hslot} {hreads} (by with_unfolding_all rfl)]",
                f"  exact ({sub_meta['run_fn']} {sub_args} fuel' (by omega))",
            ]

        elif h == "charge":
            _, b_o, s_o, d_o, r_o = st
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            vb, hb = self.prove_ev_opt(b_o, "(.int 0)", fl_ctx)
            vs, hs = self.prove_ev_opt(s_o, "(.int 0)", fl_ctx)
            vd, hd = self.prove_ev_opt(d_o, "(.int 0)", fl_ctx)
            vr, hr = self.prove_ev_opt(r_o, "Val.nil", fl_ctx)
            total_depth = consumed + 1
            ret_expr = f"⟨[{vb}, {vs}, {vd}, {vr}], {fl_ctx.kids_var}⟩"
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")
            end_prf_lines += [
                f"  rw [Combinators.run_charge {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"{self.st_lean(fl_ctx)} {opt_expr_lean(b_o)} {opt_expr_lean(s_o)} {opt_expr_lean(d_o)} {opt_expr_lean(r_o)} "
                f"{rest_lean} {vb} {vs} {vd} {vr} {hfl_v} {hb} {hs} {hd} {hr}]",
                f"  exact Combinators.chargeResult_tupleStobjs {self.frame_call} {self.tup_expr} {fl_ctx.kids_var} "
                f"_ _ _ _ _ {vb} {vs} {vd} {vr} rfl (by decide +kernel) (by decide +kernel)",
            ]

        elif h in ("idle", "yield"):
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            empty_v = f"({val(self.kinfo['consts']['*FN2-WORK-EMPTY*'])})"
            run_v = "Val.nil" if h == "idle" else "Val.t"
            total_depth = consumed + 1
            ret_expr = f"⟨[.int 0, {empty_v}, .int 0, {run_v}], {fl_ctx.kids_var}⟩"
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")
            thm_n = "run_idle" if h == "idle" else "run_yield"
            end_prf_lines += [
                f"  rw [Combinators.{thm_n} {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"{self.st_lean(fl_ctx)} {rest_lean} {empty_v} {hfl_v} (by decide +kernel)]",
                f"  exact Combinators.chargeResult_tupleStobjs {self.frame_call} {self.tup_expr} {fl_ctx.kids_var} "
                f"_ _ _ _ _ (.int 0) {empty_v} (.int 0) {run_v} rfl (by decide +kernel) (by decide +kernel)",
            ]

        elif h == "wait":
            _, b_o, s_o = st
            wcomp = self.kinfo["consts"]["*FN2-WAIT-COMPLETION*"]
            mbox_v = f"({val(self.kinfo['consts']['*FN2-WORK-MAILBOX*'])})"
            wcomp_v = f"({val(wcomp)})"
            stp_ctx = cur_ctx.clone(pending=cur_ctx.pending + [("PENDING", List([Atom("QUOTE"), Atom("1")])), ("WAIT-REASON", List([Atom("QUOTE"), wcomp]))])
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(stp_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            vb, hb = self.prove_ev_opt(b_o, "(.int 0)", fl_ctx)
            vs, hs = self.prove_ev_opt(s_o, mbox_v, fl_ctx)
            total_depth = consumed + 1
            ret_expr = f"⟨[{vb}, {vs}, .int 1, Val.nil], {fl_ctx.kids_var}⟩"
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")
            hpend_w = self.prove_pend(cur_ctx, f"[(\"PENDING\", Expr.q (.int 1)), (\"WAIT-REASON\", Expr.q {wcomp_v})]")
            end_prf_lines += [
                f"  rw [Combinators.run_wait {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"{self.st_lean(stp_ctx)} {self.st_lean(fl_ctx)} {opt_expr_lean(b_o)} {opt_expr_lean(s_o)} {rest_lean} "
                f"{wcomp_v} {mbox_v} {vb} {vs} (by decide +kernel) {hpend_w} {hfl_v} (by decide +kernel) {hb} {hs}]",
                f"  exact Combinators.chargeResult_tupleStobjs {self.frame_call} {self.tup_expr} {fl_ctx.kids_var} "
                f"_ _ _ _ _ {vb} {vs} (.int 1) Val.nil rfl (by decide +kernel) (by decide +kernel)",
            ]

        elif h == "halt":
            wnone = self.kinfo["consts"]["*FN2-WAIT-NONE*"]
            mbox_v = f"({val(self.kinfo['consts']['*FN2-WORK-MAILBOX*'])})"
            wnone_v = f"({val(wnone)})"
            stp_ctx = cur_ctx.clone(pending=cur_ctx.pending + [("STOPPED", List([Atom("QUOTE"), Atom("1")])), ("WAIT-REASON", List([Atom("QUOTE"), wnone]))])
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(stp_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            total_depth = consumed + 1
            ret_expr = f"⟨[.int 0, {mbox_v}, .int 0, Val.nil], {fl_ctx.kids_var}⟩"
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")
            hpend_h = self.prove_pend(cur_ctx, f"[(\"STOPPED\", Expr.q (.int 1)), (\"WAIT-REASON\", Expr.q {wnone_v})]")
            end_prf_lines += [
                f"  rw [Combinators.run_halt {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                f"{self.st_lean(stp_ctx)} {self.st_lean(fl_ctx)} {rest_lean} {wnone_v} {mbox_v} "
                f"(by decide +kernel) {hpend_h} {hfl_v} (by decide +kernel)]",
                f"  exact Combinators.chargeResult_tupleStobjs {self.frame_call} {self.tup_expr} {fl_ctx.kids_var} "
                f"_ _ _ _ _ (.int 0) {mbox_v} (.int 0) Val.nil rfl (by decide +kernel) (by decide +kernel)",
            ]

        elif h == "stop":
            _, reason, steps_o = st
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")
            ctrl_cur, hc = self.prove_stobj("FN2-CONTROL", fl_ctx)
            self.modified_idxs.add(self.ctrl_idx)
            if reason in self.kinfo["stops"]:
                s_idx = self.kinfo["stops"].index(reason)
                _, hk_var = self.prove_var_st("KIND", fl_ctx)
                stopped_v, hs_call = self.prove_call_fn_plain(
                    "FN2-CONTROL-RECORD-KIND-STOP", ["kindTag", f"(.int {s_idx})", ctrl_cur], f"[kindTag, .int {s_idx}, {ctrl_cur}]"
                )
                stop_rw = (
                    f"Combinators.run_stop_kind {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"{self.st_lean(fl_ctx)} {lean_str(reason)} {opt_expr_lean(steps_o)} {rest_lean} "
                    f"{s_idx} kindTag {ctrl_cur} {stopped_v} rfl {hfl_v} {hc} (by dsimp only [{self.prefix}_frame, coreKind]; decide +kernel) {hk_var} {hs_call}"
                )
            else:
                rc_key = f"*FN2-STOP-REASON-{reason}*"
                if rc_key not in self.kinfo["consts"]:
                    raise UnsupportedArmError(f"unknown stop reason {reason}")
                rc_v = f"({val(self.kinfo['consts'][rc_key])})"
                stopped_v, hs_call = self.prove_call_fn_plain(
                    "FN2-CONTROL-RECORD-STOP", [rc_v, ctrl_cur], f"[{rc_v}, {ctrl_cur}]"
                )
                stop_rw = (
                    f"Combinators.run_stop_global' {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"{self.st_lean(fl_ctx)} {lean_str(reason)} {opt_expr_lean(steps_o)} {rest_lean} "
                    f"{ctrl_cur} {rc_v} {stopped_v} rfl {hfl_v} {hc} (by dsimp only [{self.prefix}_frame, coreKind]; decide +kernel) (by decide +kernel) {hs_call}"
                )
            kids_st = self.fresh_let("kids")
            pk_st = f"(Combinators.patchKids {fl_ctx.kids_var} {self.ctrl_idx} {stopped_v})"
            def_lines.append(f"  let {kids_st} : Fin {self.n_tup} → Val := {pk_st}")
            len_lets.append(f"  let {kids_st} : Fin {self.n_tup} → Val := {pk_st}")
            prf_lines.append(f"  let {kids_st} : Fin {self.n_tup} → Val := {pk_st}")
            st_ctx = fl_ctx.clone(kids_var=kids_st, snap_hyp=None)
            total_depth = consumed + 1
            end_prf_lines.append(
                f"  rw [{stop_rw},\n"
                f"      Combinators.setStobj_tupleStobjs {self.tup_expr} {fl_ctx.kids_var} _ _ _ _ _ _ \"FN2-CONTROL\" {self.ctrl_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]"
            )
            if self.observe:
                none_v = f"({val(self.kinfo['consts']['*FN2-NONE*'])})"
                ret_expr = f"⟨[{none_v}], {kids_st}⟩"
                end_prf_lines += [
                    f"  rw [Combinators.stopEnd_observe {self.w_expr} {self.frame_call} {self.st_lean(st_ctx)} "
                    f"{opt_expr_lean(steps_o)} {none_v} rfl (by decide +kernel)]",
                    f"  exact Combinators.wakeResult_tupleStobjs {self.frame_call} {self.tup_expr} {kids_st} "
                    f"_ _ _ _ _ _ {none_v} rfl (by decide +kernel) (by decide +kernel)",
                ]
            else:
                empty_v = f"({val(self.kinfo['consts']['*FN2-WORK-EMPTY*'])})"
                vs, hs_ev = self.prove_ev_opt(steps_o, empty_v, st_ctx)
                ret_expr = f"⟨[.int 0, {vs}, .int 0, Val.nil], {kids_st}⟩"
                end_prf_lines += [
                    f"  rw [Combinators.stopEnd_arm {self.w_expr} {self.frame_call} {self.st_lean(st_ctx)} "
                    f"{opt_expr_lean(steps_o)} {empty_v} {vs} rfl (by decide +kernel) {hs_ev}]",
                    f"  exact Combinators.chargeResult_tupleStobjs {self.frame_call} {self.tup_expr} {kids_st} "
                    f"_ _ _ _ _ (.int 0) {vs} (.int 0) Val.nil rfl (by decide +kernel) (by decide +kernel)",
                ]

        elif h in ("wake", "nowake"):
            ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
            def_lines.extend("  " + x for x in ld)
            len_lets.extend("  " + x for x in ld)
            prf_lines.extend("  " + x for x in lp)
            hfl_v = self.fresh_let("hfl")
            prf_lines.append(f"  have {hfl_v} := {hfl}")
            for rw_l in prw:
                prf_lines.append(f"  {rw_l} at {hfl_v}")
            total_depth = consumed + 1
            if h == "wake":
                _, hid = self.prove_var_st("ID", fl_ctx)
                ret_expr = f"⟨[id], {fl_ctx.kids_var}⟩"
                end_prf_lines += [
                    f"  rw [Combinators.run_wake {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"{self.st_lean(fl_ctx)} {rest_lean} id rfl {hfl_v} {hid}]",
                    f"  exact Combinators.wakeResult_tupleStobjs {self.frame_call} {self.tup_expr} {fl_ctx.kids_var} "
                    f"_ _ _ _ _ _ id rfl (by decide +kernel) (by decide +kernel)",
                ]
            else:
                none_v = f"({val(self.kinfo['consts']['*FN2-NONE*'])})"
                ret_expr = f"⟨[{none_v}], {fl_ctx.kids_var}⟩"
                end_prf_lines += [
                    f"  rw [Combinators.run_nowake {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"{self.st_lean(fl_ctx)} {rest_lean} {none_v} {hfl_v} (by decide +kernel)]",
                    f"  exact Combinators.wakeResult_tupleStobjs {self.frame_call} {self.tup_expr} {fl_ctx.kids_var} "
                    f"_ _ _ _ _ _ {none_v} rfl (by decide +kernel) (by decide +kernel)",
                ]

        elif h == "park":
            _, wn, arg_o, tk_o, steps_o, ks = st
            mbox_v = f"({val(self.kinfo['consts']['*FN2-WORK-MAILBOX*'])})"
            ks_lean = "[" + ", ".join(f"({lean_str(k)}, {val(v)})" for k, v in ks) + "]"
            is_builtin = wn in ("OPERATION", "ADMISSION", "TAKEN", "POOL")
            wait_op = self.kinfo["waits"].get(wn) if not is_builtin else None

            if not is_builtin and wait_op is None and wn in self.kinfo["waits"]:
                w_const = self.kinfo["consts"][f"*FN2-WAIT-{wn}*"]
                w_val = f"({val(w_const)})"
                stp_ctx = cur_ctx.clone(pending=cur_ctx.pending + [("WAIT-REASON", List([Atom("QUOTE"), w_const]))])
                ld, lp, hfl, prw, fl_ctx = self.prove_flush(stp_ctx)
                def_lines.extend("  " + x for x in ld)
                len_lets.extend("  " + x for x in ld)
                prf_lines.extend("  " + x for x in lp)
                vs, hs_ev = self.prove_ev_opt(steps_o, mbox_v, fl_ctx)
                total_depth = consumed + 1
                ret_expr = f"⟨[.int 0, {vs}, .int 0, Val.nil], {fl_ctx.kids_var}⟩"
                hfl_v = self.fresh_let("hfl")
                prf_lines.append(f"  have {hfl_v} := {hfl}")
                for rw_l in prw:
                    prf_lines.append(f"  {rw_l} at {hfl_v}")
                hpend_pw = self.prove_pend(cur_ctx, f"[(\"WAIT-REASON\", Expr.q {w_val})]")
                end_prf_lines += [
                    f"  rw [Combinators.run_park_wait_col {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"{self.st_lean(stp_ctx)} {self.st_lean(fl_ctx)} {lean_str(wn)} {opt_expr_lean(arg_o)} "
                    f"{opt_str_lean(tk_o)} {opt_expr_lean(steps_o)} {ks_lean} {rest_lean} {mbox_v} {w_val} {vs} "
                    f"(by decide) rfl (by decide +kernel) (by decide +kernel) {hpend_pw} {hfl_v} {hs_ev}]",
                    f"  exact Combinators.chargeResult_tupleStobjs {self.frame_call} {self.tup_expr} {fl_ctx.kids_var} "
                    f"_ _ _ _ _ (.int 0) {vs} (.int 0) Val.nil rfl (by decide +kernel) (by decide +kernel)",
                ]

            elif wn == "POOL":
                if not self.kinfo["child_form"]:
                    raise UnsupportedArmError("core :park :pool deferred")
                stp_ctx = cur_ctx.clone(pending=cur_ctx.pending + [("CURSOR", arg_o)])
                ld, lp, hfl, prw, fl_ctx = self.prove_flush(stp_ctx)
                def_lines.extend("  " + x for x in ld)
                len_lets.extend("  " + x for x in ld)
                prf_lines.extend("  " + x for x in lp)
                _, hid = self.prove_var_st("ID", fl_ctx)
                dir_cur, hd = self.prove_stobj("FN2-MACHINES", fl_ctx)
                ctrl_cur, hc = self.prove_stobj("FN2-CONTROL", fl_ctx)
                r_val, hcall = self.prove_call_fn_plain(
                    "FN2-MACHINES-PARK-POOL", ["id", dir_cur, ctrl_cur], f"[id, {dir_cur}, {ctrl_cur}]"
                )
                pr_v = self.fresh_let("pr")
                kids_p = self.fresh_let("kids")
                pk_p = f"(Combinators.patchKids (Combinators.patchKids {fl_ctx.kids_var} {self.dir_idx} {pr_v}.car) {self.ctrl_idx} {pr_v}.cdr.car)"
                self.modified_idxs.update([self.dir_idx, self.ctrl_idx])
                def_lines.extend([f"  let {pr_v} : Val := {r_val}", f"  let {kids_p} : Fin {self.n_tup} → Val := {pk_p}"])
                len_lets.extend([f"  let {pr_v} : Val := {r_val}", f"  let {kids_p} : Fin {self.n_tup} → Val := {pk_p}"])
                prf_lines.extend([f"  let {pr_v} : Val := {r_val}", f"  let {kids_p} : Fin {self.n_tup} → Val := {pk_p}"])
                pk_ctx = fl_ctx.clone(kids_var=kids_p, snap_hyp=None)
                vs, hs_ev = self.prove_ev_opt(steps_o, mbox_v, pk_ctx)
                total_depth = consumed + 1
                ret_expr = f"⟨[.int 0, {vs}, .int 0, Val.nil], {kids_p}⟩"
                hfl_v = self.fresh_let("hfl")
                prf_lines.append(f"  have {hfl_v} := {hfl}")
                for rw_l in prw:
                    prf_lines.append(f"  {rw_l} at {hfl_v}")
                hs_ev_raw = self.fresh_let("hs_pk")
                prf_lines.append(
                    f"  have {hs_ev_raw} : evOpt {self.w_expr} ({self.frame_call}).kind "
                    f"(setStobj (setStobj {self.st_lean(fl_ctx)} \"FN2-MACHINES\" {pr_v}.car) \"FN2-CONTROL\" {pr_v}.cdr.car) "
                    f"{opt_expr_lean(steps_o)} {mbox_v} = .ok {vs} := by\n"
                    f"    rw [Combinators.setStobj_tupleStobjs {self.tup_expr} {fl_ctx.kids_var} _ _ _ _ _ _ \"FN2-MACHINES\" {self.dir_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel),\n"
                    f"        Combinators.setStobj_tupleStobjs {self.tup_expr} _ _ _ _ _ _ _ \"FN2-CONTROL\" {self.ctrl_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]\n"
                    f"    exact {hs_ev}"
                )
                hpend_pp = self.prove_pend(cur_ctx, f"[(\"CURSOR\", ({val(arg_o)}))]")
                end_prf_lines += [
                    f"  rw [Combinators.run_park_pool {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"{self.st_lean(stp_ctx)} {self.st_lean(fl_ctx)} ({val(arg_o)}) {opt_str_lean(tk_o)} "
                    f"{opt_expr_lean(steps_o)} {ks_lean} {rest_lean} {mbox_v} id {dir_cur} {ctrl_cur} {pr_v} {vs} "
                    f"(by decide +kernel) {hpend_pp} {hfl_v} {hid} {hd} {hc} {hcall} {hs_ev_raw},\n"
                    f"      Combinators.setStobj_tupleStobjs {self.tup_expr} {fl_ctx.kids_var} _ _ _ _ _ _ \"FN2-MACHINES\" {self.dir_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel),\n"
                    f"      Combinators.setStobj_tupleStobjs {self.tup_expr} _ _ _ _ _ _ _ \"FN2-CONTROL\" {self.ctrl_idx} _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]",
                    f"  exact Combinators.chargeResult_tupleStobjs {self.frame_call} {self.tup_expr} {kids_p} "
                    f"_ _ _ _ _ (.int 0) {vs} (.int 0) Val.nil rfl (by decide +kernel) (by decide +kernel)",
                ]

            else:
                # `viaOp` park (`OPERATION`, `ADMISSION`, `TAKEN`, or `defwait` with `:op`)
                if wn == "OPERATION":
                    op_n, op_a, hroute = "FN2-MACHINE-PARK", [Atom("ID")], "Or.inl ⟨rfl, rfl, rfl⟩"
                elif wn == "ADMISSION":
                    op_n = "FN2-MACHINE-PARK-ADMISSION"
                    op_a = [Atom("ID")] + ([arg_o] if arg_o is not None else [])
                    hroute = "Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)"
                elif wn == "TAKEN":
                    op_n, op_a = "FN2-MACHINE-PARK-TAKEN-" + (tk_o or ""), [Atom("ID")]
                    hroute = "Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))"
                elif wait_op is not None:
                    op_n, op_a = wait_op, [Atom("ID")]
                    hroute = "Or.inr (Or.inr (Or.inr ⟨by decide, by decide, by decide, by decide, rfl, rfl⟩))"
                else:
                    raise UnsupportedArmError(f"unsupported park {wn}")
                call_d = {"op": op_n, "args": op_a, "keys": ks}
                op_info = self.kinfo["ops"].get(op_n)
                if op_info is None or op_info["callee"] is None:
                    raise UnsupportedArmError(f"core park op {op_n} deferred")
                ld, lp, hfl, prw, fl_ctx = self.prove_flush(cur_ctx)
                def_lines.extend("  " + x for x in ld)
                len_lets.extend("  " + x for x in ld)
                prf_lines.extend("  " + x for x in lp)
                _, op_lean, callee, act_vs, r_lean, _, hcall = self.prove_callee_call(call_d, fl_ctx)
                rv_raw = self.fresh_let("pk_r")
                def_lines.append(f"  let {rv_raw} : Val := {r_lean}")
                len_lets.append(f"  let {rv_raw} : Val := {r_lean}")
                prf_lines.append(f"  let {rv_raw} : Val := {r_lean}")
                bd, bp, hbind, nxt_ctx = self.prove_bind_outs(op_info["stobjs_out"], [], rv_raw, callee, act_vs, fl_ctx)
                def_lines.extend("  " + x for x in bd)
                len_lets.extend("  " + x for x in bd)
                prf_lines.extend("  " + x for x in bp)
                vs, hs_ev = self.prove_ev_opt(steps_o, mbox_v, nxt_ctx)
                total_depth = consumed + 1
                ret_expr = f"⟨[.int 0, {vs}, .int 0, Val.nil], {nxt_ctx.kids_var}⟩"
                hfl_v = self.fresh_let("hfl")
                prf_lines.append(f"  have {hfl_v} := {hfl}")
                for rw_l in prw:
                    prf_lines.append(f"  {rw_l} at {hfl_v}")
                op_a_lean = "[" + ", ".join(val(x) for x in op_a) + "]"
                end_prf_lines += [
                    f"  rw [Combinators.run_park_viaOp {self.w_expr} {self.frame_call} fuel' {self.st_lean(cur_ctx)} "
                    f"{self.st_lean(fl_ctx)} {self.st_lean(nxt_ctx)} {lean_str(wn)} {opt_expr_lean(arg_o)} "
                    f"{opt_str_lean(tk_o)} {opt_expr_lean(steps_o)} {ks_lean} {rest_lean} {lean_str(op_n)} "
                    f"{op_a_lean} {op_lean} {rv_raw} {mbox_v} {vs} (by decide +kernel) ({hroute}) {hfl_v} {hcall} {hbind} {hs_ev}]",
                    f"  exact Combinators.chargeResult_tupleStobjs {self.frame_call} {self.tup_expr} {nxt_ctx.kids_var} "
                    f"_ _ _ _ _ (.int 0) {vs} (.int 0) Val.nil rfl (by decide +kernel) (by decide +kernel)",
                ]

        else:
            raise UnsupportedArmError(f"unsupported step {h}")

        nid = self.node_counter
        self.node_counter += 1
        nname = f"{self.prefix}_node_{nid}"
        self.node_names.append(nname)
        val_binders, val_args, kids_binders, kids_args, extra_hyps, _ = self.node_sig_parts(entry_ctx)
        steps_lean = "[" + ", ".join(step_to_lean(s) for s in steps) + "]"
        step_consume = consumed + 1

        node_block = [
            f"def {nname} {val_binders} {kids_binders} : ArmOut {self.n_tup} :=",
            *def_lines,
            f"  {ret_expr}",
            "",
            f"theorem {nname}_len {val_binders} {kids_binders} :",
            f"    ({nname} {val_args} {kids_args}).ans.length = {self.ans_len} := by",
            f"  dsimp only [{nname}]",
            *(len_lets if len_body != "rfl" else []),
            f"  {len_body}",
            "",
            f"theorem {nname}_run {val_binders} {kids_binders} (fuel : Nat) (hfuel : {total_depth} ≤ fuel)",
            *(["    " + x for x in extra_hyps] if extra_hyps else []),
            f"    : run {self.w_expr} {self.frame_call} fuel {self.st_lean(entry_ctx)} {steps_lean} =",
            f"      .ok (.done ({nname} {val_args} {kids_args}).toChild) := by",
            f"  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + {step_consume} := ⟨fuel - {step_consume}, by omega⟩",
            f"  dsimp only [{nname}]",
            *prf_lines,
            *end_prf_lines,
            "",
        ]
        self.emitted_defs.extend(node_block)
        return {"name": nname, "depth": total_depth}

    def build(self):
        init_snap = "hs0" if (self.core_mode and not self.kinfo["child_form"]) else None
        entry_ctx = SymCtx(kids_var="kids", snap_hyp=init_snap)
        root_node = self.compile_node(self.decl_ast["steps"], entry_ctx)
        val_binders = " ".join(f"({v} : Val)" for v in self.val_params)
        frame_lines = [
            f"def {self.prefix}_decl : ArmDecl := {arm_decl_to_lean(self.decl_ast)}",
            "",
            f"def {self.prefix}_frame {val_binders} : Frame :=",
            f"  {{ kind := {self.k_expr}, observe := {'true' if self.observe else 'false'},",
            f"    refusal := {self.refusal_lean}, base := {self.base_env_lean} }}",
            "",
        ]
        return root_node, frame_lines + self.emitted_defs


# ---------------------------------------------------------------------------
# Subarm module emitter & per-root certificate emitter
# ---------------------------------------------------------------------------

def emit_kind_subarms(ki, kinfo, fn_defs, kcommon, tuple_analyzer, out_dir, fill_world_bodies, widx, core_mode):
    """Emits per-subarm `Kind<ki>(Core)Sub_<stag>.lean` modules."""
    if not kinfo["subarms"]:
        return {}, set()
    mod_suffix = "CoreSub" if core_mode else "Sub"
    kn = kinfo["name"]

    sub_registry = {}
    multi_ops = set()

    for stag, s_entry in kinfo["subarms"].items():
        s_plist = plist_dict(as_list(s_entry)[1:])
        decl_sexp = s_plist.get(":DECL")
        if decl_sexp is None:
            continue
        safe_stag = stag.replace("-", "_")
        mod_name = f"Kind{ki}{mod_suffix}_{safe_stag}"
        pfx = f"sub_{safe_stag}"
        try:
            decl_ast = read_arm_decl_ast(decl_sexp, kinfo, ":SUBARMS", stag)
            builder = ArmProofBuilder(
                kinfo, core_mode, False, decl_ast, prefix=pfx,
                tuple_analyzer=tuple_analyzer, subarm_mod=sub_registry, fn_defs=fn_defs,
            )
            root_node, def_lines = builder.build()
        except UnsupportedArmError:
            continue

        multi_ops.update(builder.used_multi_ops)
        if stag in ("RENDER-SINGLE", "SEEK-IDENTITY"):
            continue

        dep_mods = sorted({m for dep in builder.used_subarms for m in sub_registry[dep]["all_mods"]})
        max_hb = 3200000 if stag == "SEEK-SELECTED" else 800000
        lines = [
            "import Fn2.Arms.Combinators",
            "import Fn2.Arms.Wrapper",
            "import Fn2.Instances.ServedCertificates.ServedCommon",
            "import Fn2.Instances.ServedCertificates.ServedOps",
            f"import Fn2.Instances.ServedCertificates.Kind{ki}Common",
            *(f"import Fn2.Instances.ServedCertificates.{dm}" for dm in dep_mods),
            "",
            f"set_option maxHeartbeats {max_hb}",
            "set_option maxRecDepth 100000",
            "set_option linter.unusedVariables false",
            "set_option linter.unusedSimpArgs false",
            "",
            f"namespace Fn2.Instances.ServedCertificates.{mod_name}",
            "open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core Fn2.Instances.ServedKinds Fn2.Instances.LayerAWorld",
            "open Fn2.Instances.ServedCertificates Fn2.Instances.ServedCertificates.ServedCommon",
            "",
            f"abbrev kObj : Kind := kinds[{ki}]!",
            "",
            *def_lines,
            f"end Fn2.Instances.ServedCertificates.{mod_name}",
            "",
        ]
        src = fill_world_bodies(
            as_module("\n".join(lines), expose=True, import_all=CORE_STRING_BODIES, bodies="scan"),
            widx,
        )
        (out_dir / f"{mod_name}.lean").write_text(src)

        seen_nn = set()
        trans_node_names = []
        for nn in [f"{mod_name}.{x}" for x in builder.node_names] + [
            x for dep in sorted(builder.used_subarms) for x in sub_registry[dep]["node_names"]
        ]:
            if nn not in seen_nn:
                seen_nn.add(nn)
                trans_node_names.append(nn)

        sub_registry[stag] = {
            "mod_name": mod_name,
            "all_mods": set(dep_mods) | {mod_name},
            "decl_fn": f"{mod_name}.{pfx}_decl",
            "out_fn": f"{mod_name}.{root_node['name']}",
            "len_fn": f"{mod_name}.{root_node['name']}_len",
            "run_fn": f"{mod_name}.{root_node['name']}_run",
            "node_names": trans_node_names,
            "depth": root_node["depth"],
            "modified_idxs": set(builder.modified_idxs),
            "fn_name": f"{kn}-SUB-{stag}-CHILDREN" if kinfo["child_form"] else f"{kn}-SUB-{stag}",
        }
        multi_ops.update(builder.used_multi_ops)

    return sub_registry, multi_ops


def acl2_calls_closure(fn_name, fn_defs):
    """Collect transitive helper calls within the same arm (`-CHAIN-`, `-SUB-`) that live in `fn_defs`."""
    helpers = []
    seen = {fn_name}
    if fn_name not in fn_defs:
        return helpers
    stack = list(calls_of(fn_defs[fn_name][1], set()))
    while stack:
        c = stack.pop()
        if c in seen:
            continue
        seen.add(c)
        if ("-CHAIN-" in c or "-SUB-" in c) and c in fn_defs:
            helpers.append(c)
            stack.extend(calls_of(fn_defs[c][1], set()))
    return helpers


def emit_root_proof(ri, ki, kd, area, ai, tag, name, sig_sexp, decl_sexp, kinfo, kcommon,
                    fn_defs, tuple_analyzer, sub_child_reg, sub_core_reg, widx, fill_world_bodies, out_dir,
                    write_proof=True):
    """Emits `Root<ri>Proof.lean` or raises `UnsupportedArmError`."""
    kn = kinfo["name"]
    observe = area == ":OBSERVE-ARMS"
    is_child_subarm = area == ":SUBARMS" and kinfo["child_form"]
    core_mode = not is_child_subarm
    part = {":ARMS": "arms", ":OBSERVE-ARMS": "observes", ":SUBARMS": "subarms"}[area]
    ns = f"Root{ri}"

    # Ensure primary function (and `-CHILDREN` inner function if child-form wrapper) is in `fn_defs`
    if name not in fn_defs:
        raise UnsupportedArmError(f"{name} missing from fn_defs")
    child_fn_name = f"{name}-CHILDREN" if (kinfo["child_form"] and not is_child_subarm) else None
    if child_fn_name and child_fn_name not in fn_defs:
        raise UnsupportedArmError(f"{child_fn_name} missing from fn_defs")

    check_target = child_fn_name or name
    for c in calls_of(fn_defs[check_target][1], set()):
        if ("-CHAIN-" in c or "-SUB-" in c) and c not in fn_defs:
            raise UnsupportedArmError(f"helper {c} missing from fn_defs")

    decl_ast = read_arm_decl_ast(decl_sexp, kinfo, area, tag)
    sub_reg = sub_core_reg if core_mode else sub_child_reg
    builder = ArmProofBuilder(
        kinfo, core_mode, observe, decl_ast, prefix="arm",
        tuple_analyzer=tuple_analyzer, subarm_mod=sub_reg, fn_defs=fn_defs,
    )
    root_node, def_lines = builder.build()
    if not write_proof:
        return None, builder.used_multi_ops
    nname = root_node["name"]
    depth = root_node["depth"]

    imports = [
        "import Fn2.Arms.Combinators",
        "import Fn2.Arms.Wrapper",
        "import Fn2.Instances.ServedCertificates.ServedCommon",
        "import Fn2.Instances.ServedCertificates.ServedOps",
        f"import Fn2.Instances.ServedCertificates.Kind{ki}Common",
        f"import Fn2.Instances.ServedCertificates.{ns}",
    ]
    if builder.used_subarms:
        for sm in sorted({m for stg in builder.used_subarms for m in sub_reg[stg]["all_mods"]}):
            imports.append(f"import Fn2.Instances.ServedCertificates.{sm}")

    kcommon_ns = f"Kind{ki}Common"
    lines = [
        *imports,
        "",
        "set_option maxHeartbeats 3200000",
        "set_option maxRecDepth 100000",
        "set_option linter.unusedVariables false",
        "set_option linter.unusedSimpArgs false",
        "",
        f"namespace Fn2.Arms.Served.{ns}Proof",
        "open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core Fn2.Instances.ServedKinds Fn2.Instances.LayerAWorld",
        "open Fn2.Instances.ServedCertificates Fn2.Instances.ServedCertificates.ServedCommon",
        "",
        f"abbrev kObj : Kind := kinds[{ki}]!",
        f"abbrev armObj : Arm := kObj.{part}[{ai}]!",
        "",
        *def_lines,
    ]

    seen_unfolds = set(builder.node_names)
    sub_node_unfolds = []
    for stg in sorted(builder.used_subarms):
        for nn in sub_reg[stg]["node_names"]:
            if nn not in seen_unfolds:
                seen_unfolds.add(nn)
                sub_node_unfolds.append(nn)
    all_node_unfolds = ", ".join(builder.node_names + sub_node_unfolds)

    if is_child_subarm:
        # Family 1: `:CHILDREN` `:SUBARMS` (`runArm world kind arm false`)
        sig_l = as_list(sig_sexp)
        takes = [str(x) for x in as_list(sig_l[0])]
        rets = [str(x) for x in as_list(sig_l[1])]
        results = int(str(sig_l[2]))
        tup = kinfo["tuple"]
        n_child = len(tup)
        take_args = [f"(kids ⟨{tup.index(t)}, by decide⟩)" for t in takes]
        ret_idxs_lean = "[" + ", ".join(f"⟨{tup.index(r)}, by decide⟩" for r in rets) + "]"
        single_b = "true" if (results + len(rets) == 1) else "false"
        helpers = acl2_calls_closure(name, fn_defs)
        acl2_unfolds = ", ".join([ident(name)] + [ident(h) for h in helpers])

        lines += [
            "private theorem hite_app {n : Nat} (p : Prop) [Decidable p] (f g : Fin n → Val) (i : Fin n) :",
            "    (if p then f else g) i = (if p then f i else g i) := by split <;> rfl",
            "private theorem hnat_ite {α : Sort _} (a b : Nat) (x y : α) :",
            "    @ite α (a = b) (Nat.decEq a b) x y = (if (a == b) then x else y) := by",
            "  by_cases h : a = b <;> simp [h]",
            "private theorem hfits_uw_int (w : Nat) (i : Int) :",
            "    ColType.fits (.uw w) (.int i) = (decide (0 ≤ i) && decide (i.toNat < 2 ^ w)) := by",
            "  simp only [ColType.fits]",
            "  by_cases h : 0 ≤ i",
            "  · have hp : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp",
            "    have h3 : i.toNat < 2 ^ w ↔ i < (2 : Int) ^ w := by omega",
            "    simp [h, h3]",
            "  · simp [h]",
            "private theorem hcar_cons (a d : Val) : (Val.cons a d).car = a := rfl",
            "private theorem hcdr_cons (a d : Val) : (Val.cons a d).cdr = d := rfl",
            "private theorem hcar_ite (p : Prop) [Decidable p] (a b : Val) :",
            "    (if p then a else b).car = (if p then a.car else b.car) := by split <;> rfl",
            "private theorem hcdr_ite (p : Prop) [Decidable p] (a b : Val) :",
            "    (if p then a else b).cdr = (if p then a.cdr else b.cdr) := by split <;> rfl",
            "private theorem hnatLt_enum (x : Val) (m : Int) (hm : decide (0 ≤ m) = true) :",
            "    natLt x (.int m) = ColType.fits (.enum m.toNat) x := by",
            "  rw [← natp_lt_eq_natLt, enum_int_truthy m x hm]",
            "",
        ]

        # Prove unchanged indices `j` for `tup[j] not in rets`
        unch_thms = []
        for j, t_name in enumerate(tup):
            if t_name in rets:
                continue
            lines += [
                f"theorem unchanged_{j} (id slot kindTag ordinal budget : Val) (kids : Fin {n_child} → Val) :",
                f"    ({nname} id slot kindTag ordinal budget kids kids).kids ⟨{j}, by decide⟩ = kids ⟨{j}, by decide⟩ := by",
                f"  dsimp only [{all_node_unfolds}]",
                "  simp (config := { zetaDelta := true }) only [ArmOut.kids_ite, hite_app, Combinators.patchKids, Fin.val_mk, hnat_ite, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, ite_eq_right_iff, ite_self]",
                "  repeat' (first | rfl | omega | contradiction | split)",
                "",
            ]
            unch_thms.append((j, f"unchanged_{j} id slot kindTag ordinal budget kids"))

        call_args_sp = " ".join(["id", "slot", "kindTag", "ordinal", "budget"] + take_args)
        lines += [
            f"theorem arm_acl2 (id slot kindTag ordinal budget : Val) (kids : Fin {n_child} → Val) :",
            f"    {ident(name)} {call_args_sp} =",
            f"      ({nname} id slot kindTag ordinal budget kids kids).toSub {ret_idxs_lean} {single_b} := by",
            f"  dsimp only [{acl2_unfolds}, {all_node_unfolds}, ArmOut.toSub, {kcommon_ns}.child_row_reads_env, List.map, List.headD, List.cons_append, List.nil_append]",
            "  simp (config := { zetaDelta := true }) only [",
            "    eq_def, eql_def, num_eq_def, not_def, null_def, atom_def, equal_val_truthy, Val.kw,",
            "    and_truthy, ite_bool_false_eq_and, enum_truthy, enum_and_truthy, enum_int_truthy, enum_int_and_truthy, enum_int_left_and_truthy,",
            "    natp_lt_eq_natLt, natp_lt_and_eq_natLt, natp_lt_left_and_eq_natLt, hnatLt_enum,",
            "    ubp_truthy, ubp_int_truthy, fits_ite, fits_enum_int, hfits_uw_int, Nat.reducePow, Int.reduceLE, Int.toNat, Nat.reduceLT, Nat.reduceBEq, decide_true,",
            "    memberEqual_truthy_codeIn, Combinators.codeIn_singleton_eq_equal_truthy,",
            "    Pres.nth_ite, Pres.nth_cons_zero, Pres.nth_cons_succ, Int.reduceLT, Int.reduceSub, hcar_cons, hcdr_cons, hcar_ite, hcdr_ite,",
            "    ArmOut.ans_ite, ArmOut.kids_ite, hite_app, Combinators.patchKids, Fin.val_mk, hnat_ite,",
            "    Val.ofList, List.cons_append, List.nil_append, Bool.and_assoc, Bool.true_and, Bool.and_true, Bool.and_self, Bool.false_and, Bool.and_false,",
            "    Val.truthy_ite, Val.truthy_ofBool, Val.truthy_t, Val.truthy_nil, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true, ite_self]",
            "  repeat' (first | rfl | (split <;> try simp_all (config := { zetaDelta := true }) only [",
            "    ArmOut.ans_ite, ArmOut.kids_ite, hite_app, Combinators.patchKids, Fin.val_mk, hnat_ite, Nat.reduceBEq,",
            "    hnatLt_enum, fits_ite, fits_enum_int, hfits_uw_int, Nat.reducePow, Int.reduceLE, Int.toNat, Nat.reduceLT, decide_true,",
            "    Pres.nth_ite, Pres.nth_cons_zero, Pres.nth_cons_succ, Int.reduceLT, Int.reduceSub, hcar_cons, hcdr_cons, hcar_ite, hcdr_ite,",
            "    Val.ofList, List.cons_append, List.nil_append, Bool.and_assoc, Bool.true_and, Bool.and_true, Bool.and_self, Bool.false_and, Bool.and_false,",
            "    Val.truthy_ite, Val.truthy_ofBool, Val.truthy_t, Val.truthy_nil, ↓reduceIte, Bool.false_eq_true, ite_self]))",
            "",
            f"theorem validated (id slot kindTag ordinal budget : Val) (kids : Fin {n_child} → Val) :",
            f"    Fn2.Arms.Served.{ns}.contract id slot kindTag ordinal budget kids := by",
            f"  let out := {nname} id slot kindTag ordinal budget kids kids",
            f"  have hlen : out.ans.length = {results} := {nname}_len id slot kindTag ordinal budget kids kids",
            f"  have hrun : runArm world kObj armObj false ([id, slot, kindTag, ordinal, budget] ++ List.ofFn kids) {depth} = .ok out.toChild :=",
            f"    Combinators.runArm_tupleStobjs world kObj kObj.tuple armObj false [id, slot, kindTag, ordinal, budget] kids _ arm_decl {depth} out.toChild",
            f"      rfl rfl (by decide) rfl ({kcommon_ns}.child_row_reads id slot kids) (by with_unfolding_all rfl)",
            f"      ({nname}_run id slot kindTag ordinal budget kids kids {depth} (Nat.le_refl _))",
            f"  refine ⟨{depth}, out.toChild, ({ident(name)} {call_args_sp}), hrun, {ident(name)}.fns_eq {call_args_sp}, ?_⟩",
            "  rw [arm_acl2 id slot kindTag ordinal budget kids]",
            *(f"  have hu_{j} : out.kids ⟨{j}, by decide⟩ = kids ⟨{j}, by decide⟩ := {uthm}" for j, uthm in unch_thms),
            "  generalize ha : out.ans = ans at hlen",
            "  rcases ans with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> simp at hlen",
            "  dsimp only [ArmOut.toChild, ArmOut.toSub]",
            "  rw [ha]",
            "  dsimp only [Val.toList, List.take, List.map, List.ofFn, Fin.foldr, Fin.foldr.loop, List.cons_append, List.nil_append]",
            f"  try simp only [{', '.join(f'hu_{j}' for j, _ in unch_thms) + ', ' if unch_thms else ''}Val.ofList, Val.toList, List.getElem!_cons_zero, List.getElem!_cons_succ]",
            "  rfl",
            "#print axioms validated",
            "",
        ]
        own_c_idx = tup.index(kn)
        dir_c_idx = tup.index("FN2-MACHINES")
        own_cols = len(kinfo["table"])
        knum_v = val(kinfo["consts"][f"*{kn}-KIND*"])
        lines += [
            f"def acceptedKids : Fin {n_child} → Val := fun i =>",
            f"  if i.val = {dir_c_idx} then Val.ofList [Val.ofList [{knum_v}], Val.ofList [.int 0], Val.nil, Val.nil, Val.nil, .int 1]",
            f"  else if i.val = {own_c_idx} then Val.ofList (List.replicate {own_cols} Val.nil ++ [.int 1])",
            "  else .int i.val",
            "",
            "theorem accepted_entry_positive :",
            f"    ({ident(kn + '-ROWS')} (acceptedKids ⟨{own_c_idx}, by decide⟩) = .int 1) ∧",
            f"    Fn2.Arms.Served.{ns}.contract (.int 0) (.int 0) ({knum_v}) (.int 0) (.int 0) acceptedKids := by",
            f"  exact ⟨by decide +kernel, validated (.int 0) (.int 0) ({knum_v}) (.int 0) (.int 0) acceptedKids⟩",
            "",
            "theorem omitted_child_rejected (fuel : Nat) (result : Val) :",
            f"    runArm world kObj armObj false ([.int 0, .int 0, {knum_v}, .int 0, .int 0] ++ (List.ofFn acceptedKids).tail) fuel ≠ .ok result := by",
            "  apply omitted_child_subarm_rejected",
            "  decide +kernel",
            "#print axioms accepted_entry_positive",
            "#print axioms omitted_child_rejected",
        ]

    else:
        # Family 2 & 3: `runCore` roots (`:ARMS`, `:OBSERVE-ARMS`, and `:CORE` `:SUBARMS`)
        n_core = len(kinfo["core_tuple"])
        ctrl_i = kinfo["core_tuple"].index("FN2-CONTROL")
        own_i = kinfo["core_tuple"].index(kn)
        dir_i = kinfo["core_tuple"].index("FN2-MACHINES")
        knum_v = val(kinfo["consts"][f"*{kn}-KIND*"])
        ord_key = f"*{kn}-ADMISSION-ORDINAL*"
        ord_v = val(kinfo["consts"][ord_key]) if ord_key in kinfo["consts"] else ".int 0"
        empty_v = val(kinfo["consts"]["*FN2-WORK-EMPTY*"])
        none_v = val(kinfo["consts"]["*FN2-NONE*"])
        stop_entry_key = "*FN2-STOP-REASON-MACHINE-OBSERVATION*" if observe else "*FN2-STOP-REASON-MACHINE-PHASE*"
        stop_entry_v = val(kinfo["consts"][stop_entry_key])

        lead_vars = ["id", "event", "outcome", "reason", "count", "aux0", "aux1"] if observe else ["id", "budget"]
        lead_binders = " ".join(f"({v} : Val)" for v in lead_vars)
        lead_sp = " ".join(lead_vars)
        lead_comma = ", ".join(lead_vars)
        slot_e = "(«FN2-MACHINE-SLOT» id (Combinators.tupleImage kids))"
        inner_args = (
            f"id {slot_e} ({knum_v}) ({ord_v}) event outcome reason count aux0 aux1"
            if observe else f"id {slot_e} ({knum_v}) ({ord_v}) budget"
        )
        ref_val_lean = (
            f"Val.ofList [{none_v}, Combinators.tupleImage (Combinators.patchKids kids {ctrl_i} "
            f"(«FN2-CONTROL-RECORD-STOP» ({stop_entry_v}) (kids ⟨{ctrl_i}, by decide⟩)))]"
            if observe else
            f"Val.ofList [.int 0, {empty_v}, .int 0, Val.nil, Combinators.tupleImage (Combinators.patchKids kids {ctrl_i} "
            f"(«FN2-CONTROL-RECORD-STOP» ({stop_entry_v}) (kids ⟨{ctrl_i}, by decide⟩)))]"
        )

        lines += [
            "private theorem hite_app {n : Nat} (p : Prop) [Decidable p] (f g : Fin n → Val) (i : Fin n) :",
            "    (if p then f else g) i = (if p then f i else g i) := by split <;> rfl",
            "private theorem hnat_ite {α : Sort _} (a b : Nat) (x y : α) :",
            "    @ite α (a = b) (Nat.decEq a b) x y = (if (a == b) then x else y) := by",
            "  by_cases h : a = b <;> simp [h]",
            "private theorem hfits_uw_int (w : Nat) (i : Int) :",
            "    ColType.fits (.uw w) (.int i) = (decide (0 ≤ i) && decide (i.toNat < 2 ^ w)) := by",
            "  simp only [ColType.fits]",
            "  by_cases h : 0 ≤ i",
            "  · have hp : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp",
            "    have h3 : i.toNat < 2 ^ w ↔ i < (2 : Int) ^ w := by omega",
            "    simp [h, h3]",
            "  · simp [h]",
            "private theorem hcar_cons (a d : Val) : (Val.cons a d).car = a := rfl",
            "private theorem hcdr_cons (a d : Val) : (Val.cons a d).cdr = d := rfl",
            "private theorem hcar_ite (p : Prop) [Decidable p] (a b : Val) :",
            "    (if p then a else b).car = (if p then a.car else b.car) := by split <;> rfl",
            "private theorem hcdr_ite (p : Prop) [Decidable p] (a b : Val) :",
            "    (if p then a else b).cdr = (if p then a.cdr else b.cdr) := by split <;> rfl",
            "private theorem hnatLt_enum (x : Val) (m : Int) (hm : decide (0 ≤ m) = true) :",
            "    natLt x (.int m) = ColType.fits (.enum m.toNat) x := by",
            "  rw [← natp_lt_eq_natLt, enum_int_truthy m x hm]",
            "",
        ]

        # Build `arm_acl2` proof depending on `:CHILDREN` wrapper vs `:CORE` function
        if kinfo["child_form"]:
            helpers = acl2_calls_closure(child_fn_name, fn_defs)
            extra_unfolds = [ident(x) for x in ("FN2-CORE-STOP", "FN2-CORE-KIND-STOP", "FN2-MACHINE-WAKE-ROW") if x in fn_defs]
            acl2_unfolds = ", ".join(dict.fromkeys([ident(name), ident(child_fn_name)] + [ident(h) for h in helpers] + extra_unfolds))
            # Collect core getter/setter lemmas for all children in `kinfo["tuple"]` + directory/control
            seen_c_idxs = set()
            core_get_rws = []
            for t_c in list(kinfo["tuple"]) + ["FN2-MACHINES", "FN2-CONTROL"]:
                if t_c not in kinfo["core_tuple"]:
                    continue
                c_idx = kinfo["core_tuple"].index(t_c)
                if c_idx in seen_c_idxs:
                    continue
                seen_c_idxs.add(c_idx)
                suf = t_c[4:] if t_c.startswith("FN2-") else t_c
                g_fn = f"FN2-CORE-{suf}" if f"FN2-CORE-{suf}" in fn_defs else f"{t_c}-TABLE"
                u_fn = f"UPDATE-{g_fn}"
                if g_fn in fn_defs:
                    core_get_rws.append((c_idx, g_fn, u_fn))
            getter_haves = []
            rw_names = []
            for c_idx, g_fn, u_fn in core_get_rws:
                gh = f"hg_{c_idx}"
                getter_haves.append(
                    f"    have {gh} (k : Fin {n_core} → Val) : {ident(g_fn)} (Combinators.tupleImage k) = k ⟨{c_idx}, by decide⟩ :=\n"
                    f"      Combinators.nth_tupleImage k {c_idx} (by decide)"
                )
                rw_names.append(gh)
                if u_fn in fn_defs:
                    uh = f"hu_{c_idx}"
                    getter_haves.append(
                        f"    have {uh} (v : Val) (k : Fin {n_core} → Val) : {ident(u_fn)} v (Combinators.tupleImage k) = Combinators.tupleImage (Combinators.patchKids k {c_idx} v) :=\n"
                        f"      (Combinators.tupleImage_patchKids k {c_idx} v (by decide)).symm"
                    )
                    rw_names.append(uh)
            neg_stop_unfold = ", «FN2-CORE-STOP»" if "FN2-CORE-STOP" in fn_defs else ""
            lines += [
                f"theorem arm_acl2 {lead_binders} (kids : Fin {n_core} → Val) :",
                f"    {ident(name)} {lead_sp} (Combinators.tupleImage kids) =",
                f"      (if ({ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) == .sym \":OK\")",
                f"       then ({nname} {inner_args} kids kids).toCore",
                f"       else {ref_val_lean}) := by",
                f"  by_cases hok : ({ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) == .sym \":OK\") = true",
                "  · have hs : " + f"{ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) = .sym \":OK\" := beq_iff_eq.mp hok",
                f"    obtain ⟨hslot_m, hown_lt, hdir_lt⟩ := {kcommon_ns}.entry_bounds id kids hs",
                "    rw [hslot_m] at hown_lt ⊢; clear hslot_m",
                *getter_haves,
                f"    dsimp only [{acl2_unfolds}, {all_node_unfolds}, ArmOut.toCore, {kcommon_ns}.core_row_reads_env, List.cons_append, List.nil_append]",
                f"    simp (config := {{ zetaDelta := true }}) only [hok, hs, {', '.join(rw_names)},",
                "      tupleImage_ite, ArmOut.toCore_ite, ArmOut.ans_ite, ArmOut.kids_ite, hite_app, hnat_ite,",
                "      eq_def, eql_def, num_eq_def, not_def, null_def, atom_def, equal_val_truthy, Val.kw,",
                "      and_truthy, ite_bool_false_eq_and, enum_truthy, enum_and_truthy, enum_int_truthy, enum_int_and_truthy, enum_int_left_and_truthy,",
                "      natp_lt_eq_natLt, natp_lt_and_eq_natLt, natp_lt_left_and_eq_natLt, hnatLt_enum,",
                "      ubp_truthy, ubp_int_truthy, fits_ite, fits_enum_int, hfits_uw_int, Nat.reducePow, Int.reduceLE, Int.toNat, Nat.reduceLT, Nat.reduceBEq, decide_true,",
                "      memberEqual_truthy_codeIn, Combinators.codeIn_singleton_eq_equal_truthy,",
                "      hown_lt, hdir_lt, Bool.and_self, Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, Bool.and_assoc,",
                "      Pres.nth_ite, Pres.nth_cons_zero, Pres.nth_cons_succ, Int.reduceLT, Int.reduceSub, hcar_cons, hcdr_cons, hcar_ite, hcdr_ite,",
                "      Val.ofList, List.cons_append, List.nil_append, Val.truthy_ite, Val.truthy_ofBool, Val.truthy_t, Val.truthy_nil, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true, ite_self]",
                "    repeat' (first | rfl | (split <;> try simp_all (config := { zetaDelta := true }) only [",
                f"      {', '.join(rw_names)}, tupleImage_ite, ArmOut.toCore_ite, ArmOut.ans_ite, ArmOut.kids_ite, hite_app, hnat_ite, Nat.reduceBEq,",
                "      hnatLt_enum, fits_ite, fits_enum_int, hfits_uw_int, Nat.reducePow, Int.reduceLE, Int.toNat, Nat.reduceLT, decide_true,",
                "      Pres.nth_ite, Pres.nth_cons_zero, Pres.nth_cons_succ, Int.reduceLT, Int.reduceSub, hcar_cons, hcdr_cons, hcar_ite, hcdr_ite,",
                "      Val.ofList, List.cons_append, List.nil_append, Bool.and_assoc, Bool.true_and, Bool.and_true, Bool.and_self, Bool.false_and, Bool.and_false,",
                "      Val.truthy_ite, Val.truthy_ofBool, Val.truthy_t, Val.truthy_nil, ↓reduceIte, Bool.false_eq_true, ite_self]))",
                "    all_goals try (repeat' (apply congrArg₂ Val.cons rfl); apply congrArg (fun x => Val.cons x Val.nil); apply congrArg Combinators.tupleImage; funext ⟨j, hj⟩; simp only [hite_app, Combinators.patchKids, Fin.val_mk, hnat_ite, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, ite_self]; repeat' (first | rfl | omega | contradiction | (split <;> (try omega) <;> try simp_all only [hite_app, Combinators.patchKids, Fin.val_mk, hnat_ite, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, ite_self])))",
                "  · have hbf : (" + f"{ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) == .sym \":OK\") = false := Bool.eq_false_iff.mpr hok",
                "    have hne : " + f"{ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) ≠ .sym \":OK\" := fun h => hok (beq_iff_eq.mpr h)",
                f"    have hc0 : «FN2-CORE-CONTROL» (Combinators.tupleImage kids) = kids ⟨{ctrl_i}, by decide⟩ := Combinators.nth_tupleImage kids {ctrl_i} (by decide)",
                f"    have hu0 (v : Val) : «UPDATE-FN2-CORE-CONTROL» v (Combinators.tupleImage kids) = Combinators.tupleImage (Combinators.patchKids kids {ctrl_i} v) :=",
                f"      (Combinators.tupleImage_patchKids kids {ctrl_i} v (by decide)).symm",
                f"    dsimp only [{ident(name)}{neg_stop_unfold}]",
                "    simp only [hbf, eq_def, not_def, equal_val_truthy, ↓reduceIte, Val.truthy_ite, Val.truthy_ofBool, Val.truthy_nil, Val.truthy_t, Bool.false_eq_true, hc0, hu0, Pres.nth_cons_zero, Pres.nth_cons_succ, Int.reduceLT, Int.reduceSub, Val.ofList]",
                "",
            ]
        else:
            # Family 3: `:CORE` kind (`not kinfo["child_form"]`)
            helpers = acl2_calls_closure(name, fn_defs)
            acl2_unfolds = ", ".join([ident(name)] + [ident(h) for h in helpers])
            row_rw_list = [f"{kcommon_ns}.row_read_{c.replace('-', '_')} id kids hs" for c, _ in kinfo["columns"] if f"{kn}-ROW-{c}" in fn_defs]
            write_rw_list = [f"{kcommon_ns}.{wthm}" for wthm in kcommon["write_lemmas"].values()]
            extra_core_rws = []
            if "FN2-CORE-STOP" in fn_defs:
                extra_core_rws.append(f"{kcommon_ns}.core_stop_eq")
            if "FN2-CORE-KIND-STOP" in fn_defs:
                extra_core_rws.append(f"{kcommon_ns}.core_kind_stop_eq")
            if "FN2-MACHINE-WAKE-ROW" in fn_defs:
                extra_core_rws.append(f"{kcommon_ns}.core_wake_row_eq")
            step_simp_list = (
                write_rw_list
                + extra_core_rws
                + [
                    "tupleImage_ite", "ArmOut.toCore_ite", "ArmOut.ans_ite", "ArmOut.kids_ite", "hite_app", "hnat_ite",
                    "eq_def", "eql_def", "num_eq_def", "not_def", "null_def", "atom_def", "equal_val_truthy", "Val.kw",
                    "and_truthy", "ite_bool_false_eq_and", "memberEqual_truthy_codeIn", "Combinators.codeIn_singleton_eq_equal_truthy",
                    "Pres.nth_ite", "Pres.nth_cons_zero", "Pres.nth_cons_succ", "Int.reduceLT", "Int.reduceSub", "hcar_cons", "hcdr_cons", "hcar_ite", "hcdr_ite",
                    "hnatLt_enum", "fits_ite", "fits_enum_int", "hfits_uw_int", "Nat.reducePow", "Int.reduceLE", "Int.toNat", "Nat.reduceLT", "Nat.reduceBEq", "decide_true", "Bool.and_self", "Bool.true_and", "Bool.and_true", "Bool.false_and", "Bool.and_false", "Bool.and_assoc", "ite_self",
                    "Val.ofList", "List.cons_append", "List.nil_append", "Val.truthy_ite", "Val.truthy_ofBool", "Val.truthy_t", "Val.truthy_nil", "↓reduceIte", "Bool.false_eq_true", "beq_self_eq_true",
                ]
            )
            pos_simp_init = ", ".join(row_rw_list + ["hs", "hok"] + step_simp_list)
            pos_simp_step = ", ".join(step_simp_list)
            lines += [
                f"theorem arm_acl2 {lead_binders} (kids : Fin {n_core} → Val) :",
                f"    {ident(name)} {lead_sp} (Combinators.tupleImage kids) =",
                f"      (if ({ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) == .sym \":OK\")",
                f"       then ({nname} {inner_args} kids kids).toCore",
                f"       else {ref_val_lean}) := by",
                f"  by_cases hok : ({ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) == .sym \":OK\") = true",
                "  · have hs : " + f"{ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) = .sym \":OK\" := beq_iff_eq.mp hok",
                f"    dsimp only [{acl2_unfolds}, {all_node_unfolds}, ArmOut.toCore, {kcommon_ns}.core_row_reads_env, List.cons_append, List.nil_append]",
                f"    simp (config := {{ zetaDelta := true }}) only [{pos_simp_init}]",
                "    repeat' (first | rfl | (split <;> try simp_all (config := { zetaDelta := true }) only [",
                f"      {pos_simp_step}]))",
                "  · have hbf : (" + f"{ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) == .sym \":OK\") = false := Bool.eq_false_iff.mpr hok",
                "    have hne : " + f"{ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids) ≠ .sym \":OK\" := fun h => hok (beq_iff_eq.mpr h)",
                f"    dsimp only [{ident(name)}]",
                f"    simp only [hbf, eq_def, not_def, equal_val_truthy, ↓reduceIte, Val.truthy_ite, Val.truthy_ofBool, Val.truthy_nil, Val.truthy_t, Bool.false_eq_true, {kcommon_ns}.core_stop_eq, Val.ofList]",
                "",
            ]

        runcore_thm = "runCore_observe_eq" if observe else "runCore_arm_eq"
        pre_len = 10 if observe else 5
        pre_list_lean = (
            f"[id, {slot_e}, {knum_v}, {ord_v}, event, outcome, reason, count, aux0, aux1]"
            if observe else f"[id, {slot_e}, {knum_v}, {ord_v}, budget]"
        )
        run_extra = " rfl hs" if not kinfo["child_form"] else ""
        lines += [
            f"theorem validated {lead_binders} (kids : Fin {n_core} → Val) :",
            f"    Fn2.Arms.Served.{ns}.contract {lead_sp} kids := by",
            f"  have hrc := {runcore_thm} kObj armObj {lead_sp} kids {depth} {ctrl_i}",
            f"    ({ident(kn + '-SNAPSHOT-READ-CODE')} id (Combinators.tupleImage kids))",
            f"    {slot_e} ({knum_v}) ({ord_v}) ({stop_entry_v}) ({none_v}) ({empty_v})",
            f"    ({nname} {inner_args} kids kids)",
            "    (by decide) (by decide +kernel) (by decide)",
            f"    (callFn_world_of_fns {lean_str(kn + '-SNAPSHOT-READ-CODE')} _ _ (by decide +kernel) ({ident(kn + '-SNAPSHOT-READ-CODE')}.fns_eq _ _))",
            "    (fun _ => callFn_world_of_fns \"FN2-MACHINE-SLOT\" _ _ (by decide +kernel) («FN2-MACHINE-SLOT».fns_eq _ _))",
            "    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)",
            "    (fun hs => Combinators.runArm_tupleStobjs (coreWorld world coreTuple) (coreKind kObj coreTuple) coreTuple",
            f"      armObj {'true' if observe else 'false'} {pre_list_lean} kids _ arm_decl {depth} _",
            f"      rfl rfl (by decide) rfl ({kcommon_ns}.core_row_reads id _ kids) (by with_unfolding_all rfl)",
            f"      ({nname}_run {inner_args} kids kids {depth} (Nat.le_refl _){run_extra}))",
            f"    (fun _ => {nname}_len {inner_args} kids kids)",
            f"  refine ⟨{depth}, _, hrc, ?_⟩",
            f"  change Fn2.Instances.LayerAWorld.fns {lean_str(name)} [{lead_comma}, Combinators.tupleImage kids] = _",
            f"  rw [{ident(name)}.fns_eq, arm_acl2 {lead_sp} kids]",
            "#print axioms validated",
            "",
        ]
        own_cols = len(kinfo["table"])
        zero_sp = " ".join(["(.int 0)"] * len(lead_vars))
        zero_comma = ", ".join([".int 0"] * len(lead_vars))
        lines += [
            f"def acceptedKids : Fin {n_core} → Val := fun i =>",
            f"  if i.val = {dir_i} then Val.ofList [Val.ofList [{knum_v}], Val.ofList [.int 0], Val.nil, Val.nil, Val.nil, .int 1]",
            f"  else if i.val = {own_i} then Val.ofList (List.replicate {own_cols} Val.nil ++ [.int 1])",
            "  else .int i.val",
            "",
            "theorem accepted_entry_positive :",
            f"    {ident(kn + '-SNAPSHOT-READ-CODE')} (.int 0) (Fn2.Arms.Served.{ns}.image acceptedKids) = .sym \":OK\" ∧",
            f"    Fn2.Arms.Served.{ns}.contract {zero_sp} acceptedKids := by",
            f"  exact ⟨by decide +kernel, validated {zero_sp} acceptedKids⟩",
            "",
            "theorem omitted_child_rejected (fuel : Nat) (result : Val) :",
            f"    runCore world coreTuple kObj armObj {'true' if observe else 'false'}",
            f"      [{zero_comma}, Val.ofList (List.ofFn acceptedKids).tail] fuel ≠ .ok result := by",
            "  apply Wrapper.omitted_child_rejected",
            "  decide +kernel",
            "#print axioms accepted_entry_positive",
            "#print axioms omitted_child_rejected",
        ]

    lines += [f"end Fn2.Arms.Served.{ns}Proof", ""]
    src = fill_world_bodies(
        as_module("\n".join(lines), expose=True, import_all=CORE_STRING_BODIES, bodies="scan"),
        widx,
    )
    proof_path = out_dir / f"{ns}Proof.lean"
    proof_path.write_text(src)
    return proof_path, builder.used_multi_ops


VALIDATED_GENERATED_ROOTS = frozenset({
    "FN2-BOOT-ON-FENCE-RESULT",
    "FN2-BOOT-ON-READ-RESULT",
    "FN2-BOOT-ON-WRITE-RESULT",
    "FN2-BOOT-RUN-READ-RESULT",
    "FN2-CNS-ON-READ-RESULT",
    "FN2-CONN-ON-CLOSE-RESULT",
    "FN2-CONN-RUN-UPGRADING",
    "FN2-CTL-ON-CLOSE-RESULT",
    "FN2-CTL-ON-RECEIVE-RESULT",
    "FN2-CTL-RUN-WAITING",
    "FN2-CURSOR-ON-READ-RESULT",
    "FN2-CURSOR-RUN-SEND",
    "FN2-CURSOR-SUB-HDR-NEXT-CHILDREN",
    "FN2-ECHO-ON-BORROW-RELEASED",
    "FN2-ECHO-ON-CLOSE-RESULT",
    "FN2-ECHO-ON-RECEIVE-RESULT",
    "FN2-LISTENER-ON-CLOSE-RESULT",
    "FN2-RECOVERY-MACHINE-ON-READ-RESULT",
    "FN2-RECOVERY-MACHINE-SUB-PAYLOAD-AMBIGUOUS",
    "FN2-SCRIBE-ON-FENCE-RESULT",
    "FN2-SCRIBE-ON-READ-RESULT",
    "FN2-SCRIBE-ON-WRITE-RESULT",
    "FN2-SCRIBE-RUN-FENCE-RESULT",
    "FN2-SCRIBE-RUN-READ-RESULT",
    "FN2-SCRIBE-RUN-VERIFY",
    "FN2-SCRIBE-RUN-WRITE-RESULT",
    "FN2-SCRIBE-SUB-RESULT-CHILDREN",
    "FN2-SCRIBE-SUB-STOP-CHILDREN",
    "FN2-TXN-RUN-UNCERTAIN",
    "FN2-UPLOAD-ON-FENCE-RESULT",
    "FN2-UPLOAD-ON-WRITE-RESULT",
})


def emit_served_proofs(kinds, inventory, layout, consts, ops_raw, waits_raw, cw_list,
                       fn_defs, widx, fill_world_bodies, out_dir, roots, base_dir):
    """Main entry point called from `emit_served_certificate.generate`."""
    fn_defs = {k: v for k, v in fn_defs.items() if not widx or k in widx["mod_of"]}
    ops_by_name = parse_ops(ops_raw)
    waits_by_name = parse_waits(waits_raw)
    layout_strs = [str(x) for x in layout]
    cw_map = {
        (str(kn), str(area), str(tag), show(step)): list(as_list(expanded))
        for kn, area, tag, step, expanded in cw_list
    }

    emit_served_common(out_dir, fill_world_bodies, widx)
    tuple_analyzer = TupleShapeAnalyzer(fn_defs, widx)
    all_multi_targets = set()

    kinfos = {}
    kcommons = {}
    sub_child_regs = {}
    sub_core_regs = {}
    bykind = {str(k[0]): (i, k) for i, k in enumerate(kinds)}

    for ki, kd in enumerate(kinds):
        kn = str(kd[0])
        kinfo = build_kind_info(kd, ki, consts, ops_by_name, waits_by_name, cw_map)
        kinfo["core_tuple"] = layout_strs
        kinfos[kn] = kinfo
        kcommons[kn] = emit_kind_common(out_dir, kinfo, layout_strs, fn_defs, fill_world_bodies, widx)
        if kinfo["child_form"]:
            sc, m1 = emit_kind_subarms(ki, kinfo, fn_defs, kcommons[kn], tuple_analyzer, out_dir, fill_world_bodies, widx, False)
            sco, m2 = emit_kind_subarms(ki, kinfo, fn_defs, kcommons[kn], tuple_analyzer, out_dir, fill_world_bodies, widx, True)
            sub_child_regs[kn] = sc
            sub_core_regs[kn] = sco
            all_multi_targets.update(m1 | m2)
        else:
            sub_child_regs[kn] = {}
            sub_core_regs[kn] = {}

    for ri, row in enumerate(inventory):
        rec = roots[ri]
        if "proof" in rec:
            continue
        kn_s = str(row[0])
        area_s = str(row[1])
        tag_s = str(row[2])
        fn_s = str(row[4])
        core_s = str(row[5])
        decl = row[6]
        sig = row[7]
        name = fn_s if core_s == "NIL" else core_s
        if name not in fn_defs:
            continue
        ki, kd = bykind[kn_s]
        key = {":ARMS": ":ARMS", ":OBSERVE-ARMS": ":OBSERVES", ":SUBARMS": ":SUBARMS"}[area_s]
        entries = plist_dict(as_list(kd)[1:])[key]
        ai = next(i for i, a in enumerate(as_list(entries)) if str(a[0]) == tag_s)
        try:
            proof_path, used_mops = emit_root_proof(
                ri, ki, kd, area_s, ai, tag_s, name, sig, decl, kinfos[kn_s], kcommons[kn_s],
                fn_defs, tuple_analyzer, sub_child_regs[kn_s], sub_core_regs[kn_s],
                widx, fill_world_bodies, out_dir,
                write_proof=(name in VALIDATED_GENERATED_ROOTS),
            )
            all_multi_targets.update(used_mops)
            if proof_path is not None:
                rec.update(proof=str(proof_path.relative_to(base_dir)), reason="generated proof has not passed Lean")
        except UnsupportedArmError:
            pass

    emit_served_ops(out_dir, all_multi_targets, fn_defs, fill_world_bodies, widx)
