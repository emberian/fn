import Fn2.Arms
import Fn2.ArmsLemmas

/-!
# Fn2.Arms.Bound: a sound static interval for a step-language expression

`ival w k senv e` is an interval `(lo, hi)` that holds the integer reading (`Val.toInt`) of every
value `e` evaluates to, in any state whose `:let` bindings lie in the intervals `senv` records
(`ival_sound`). It is the bound the derived contracts (`Fn2.Arms.Derive`) charge by.
-/

namespace Fn2.Arms.Bound
open Fn2.ACL2 Fn2.Arms

/-- An interval of integers, `(lo, hi)`. -/
abbrev Bnd := Int × Int

/-- The static environment: per `:let` variable, its interval, or `none` where the variable is
bound to something the analysis does not bound (a call's result, an unbounded `:let`). The first
entry for a name is the one in force, as the interpreter's first binding is. -/
abbrev SEnv := List (String × Option Bnd)

def senvFind (senv : SEnv) (x : String) : Option Bnd :=
  match senv.find? (·.1 == x) with
  | some (_, b) => b
  | none => none

def bAdd (a b : Bnd) : Bnd := (a.1 + b.1, a.2 + b.2)
def bNeg (a : Bnd) : Bnd := (-a.2, -a.1)
def bHull (a b : Bnd) : Bnd := (min a.1 b.1, max a.2 b.2)
def bMul (a b : Bnd) : Bnd :=
  let p1 := a.1 * b.1
  let p2 := a.1 * b.2
  let p3 := a.2 * b.1
  let p4 := a.2 * b.2
  (min (min p1 p2) (min p3 p4), max (max p1 p2) (max p3 p4))

def InB (x : Int) (b : Bnd) : Prop := b.1 ≤ x ∧ x ≤ b.2

/-- One unfolding of the interval analysis, mirroring `readExprF`'s reading of each form it
bounds; every other form is unbounded (`none`). -/
def ivalF (w : World) (k : Kind) (senv : SEnv) (rec : Expr → Option Bnd) : Expr → Option Bnd
  | .int i => some (i, i)
  | .str _ | .chr _ => some (0, 0)
  | .sym n =>
    if n == "T" || n == "NIL" || n.startsWith ":" then some (0, 0)
    else if n == "ROW-SLOT" then none
    else if n == "*" ++ k.name ++ "-KIND*" then none
    else if n == "*" ++ k.name ++ "-ADMISSION-ORDINAL*" then none
    else if n.length > 2 && n.startsWith "*" && n.endsWith "*" then
      match w.consts.find? (·.1 == n) with
      | some (_, v) => some (v.toInt, v.toInt)
      | none => none
    else senvFind senv n
  | .cons (.sym f) rest =>
    match f, rest.toList with
    | "QUOTE", [v] => some (v.toInt, v.toInt)
    | "IF", [_, a, b] => bHull <$> rec a <*> rec b
    | "+", args => args.foldr (fun a acc => bAdd <$> rec a <*> acc) (some (0, 0))
    | "*", [a, b] => bMul <$> rec a <*> rec b
    | "-", [a] => bNeg <$> rec a
    | "-", [a, b] => bAdd <$> rec a <*> (bNeg <$> rec b)
    | "1+", [a] => bAdd (1, 1) <$> rec a
    | "1-", [a] => bAdd (-1, -1) <$> rec a
    | _, _ => none
  | _ => none

def ival (w : World) (k : Kind) (senv : SEnv) : Expr → Option Bnd :=
  fixN 64 (ivalF w k senv) (fun _ => none)

/-- The interpreter state agrees with the static environment: every variable `senv` bounds is
bound in the state's variables, to a value in its interval. -/
def EnvOK (senv : SEnv) (vars : Env) : Prop :=
  ∀ x b, senvFind senv x = some b → ∃ v, vars.get? x = some v ∧ InB v.toInt b

/-! ### Evaluation of the arithmetic the reader writes -/

theorem bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem eval_plus (fns : Fns) (env : Env) (a b : Term) (v : Val)
    (h : Term.eval fns env (.app "BINARY-+" [a, b]) = .ok v) :
    ∃ va vb, Term.eval fns env a = .ok va ∧ Term.eval fns env b = .ok vb ∧
      v.toInt = va.toInt + vb.toInt := by
  simp [Term.eval] at h
  obtain ⟨va, ha, h⟩ := bind_ok h
  obtain ⟨vb, hb, h⟩ := bind_ok h
  have hn : nativeCall "BINARY-+" [va, vb] = some (Prim.plus va vb) := rfl
  rw [hn] at h
  cases h
  exact ⟨va, vb, ha, hb, rfl⟩

theorem eval_times (fns : Fns) (env : Env) (a b : Term) (v : Val)
    (h : Term.eval fns env (.app "BINARY-*" [a, b]) = .ok v) :
    ∃ va vb, Term.eval fns env a = .ok va ∧ Term.eval fns env b = .ok vb ∧
      v.toInt = va.toInt * vb.toInt := by
  simp [Term.eval] at h
  obtain ⟨va, ha, h⟩ := bind_ok h
  obtain ⟨vb, hb, h⟩ := bind_ok h
  have hn : nativeCall "BINARY-*" [va, vb] = some (Prim.times va vb) := rfl
  rw [hn] at h
  cases h
  exact ⟨va, vb, ha, hb, rfl⟩

theorem eval_neg (fns : Fns) (env : Env) (a : Term) (v : Val)
    (h : Term.eval fns env (.app "UNARY--" [a]) = .ok v) :
    ∃ va, Term.eval fns env a = .ok va ∧ v.toInt = - va.toInt := by
  simp [Term.eval] at h
  obtain ⟨va, ha, h⟩ := bind_ok h
  have hn : nativeCall "UNARY--" [va] = some (Prim.neg va) := rfl
  rw [hn] at h
  cases h
  exact ⟨va, ha, rfl⟩

theorem eval_if (fns : Fns) (env : Env) (c a b : Term) (v : Val)
    (h : Term.eval fns env (.app "IF" [c, a, b]) = .ok v) :
    Term.eval fns env a = .ok v ∨ Term.eval fns env b = .ok v := by
  simp [Term.eval] at h
  obtain ⟨vc, _, h⟩ := bind_ok h
  split at h
  · exact Or.inl h
  · exact Or.inr h

theorem eval_quote (fns : Fns) (env : Env) (x v : Val)
    (h : Term.eval fns env (.quote x) = .ok v) : v = x := by
  simp [Term.eval] at h; exact h.symm

theorem eval_var (fns : Fns) (env : Env) (x : String) (v : Val)
    (h : Term.eval fns env (.var x) = .ok v) : env.get? x = some v := by
  simp only [Term.eval] at h
  split at h
  · rename_i v' hv; cases h; exact hv
  · cases h

theorem envGet_append (vars stobjs : Env) (x : String) (v : Val) (h : vars.get? x = some v) :
    (vars ++ stobjs).get? x = some v := by
  unfold Env.get? at h ⊢
  rw [List.find?_append]
  cases hf : vars.find? (·.1 == x) with
  | none => rw [hf] at h; cases h
  | some p => rw [hf] at h; simpa using h

theorem seq_some {α β γ : Type} {f : α → β → γ} {x : Option α} {y : Option β} {b : γ}
    (h : (Option.map f x <*> y) = some b) : ∃ bx by_, x = some bx ∧ y = some by_ ∧ b = f bx by_ := by
  cases x <;> cases y <;> simp [Seq.seq, Option.map] at h ⊢
  exact h.symm

theorem map_some {α β : Type} {f : α → β} {x : Option α} {b : β}
    (h : Option.map f x = some b) : ∃ bx, x = some bx ∧ b = f bx := by
  cases x <;> simp [Option.map] at h ⊢
  exact h.symm

theorem inB_hull {x : Int} {a b : Bnd} (h : InB x a ∨ InB x b) : InB x (bHull a b) := by
  unfold InB bHull at *; rcases h with h | h <;> constructor <;> simp only at * <;> omega

theorem inB_add {x y : Int} {a b : Bnd} (hx : InB x a) (hy : InB y b) : InB (x + y) (bAdd a b) := by
  unfold InB bAdd at *; constructor <;> simp only at * <;> omega

theorem inB_neg {x : Int} {a : Bnd} (hx : InB x a) : InB (-x) (bNeg a) := by
  unfold InB bNeg at *; constructor <;> simp only at * <;> omega

theorem mul_between {lo hi x : Int} (y : Int) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    min (lo * y) (hi * y) ≤ x * y ∧ x * y ≤ max (lo * y) (hi * y) := by
  rcases Int.le_total 0 y with hy | hy
  · have a := Int.mul_le_mul_of_nonneg_right h1 hy
    have b := Int.mul_le_mul_of_nonneg_right h2 hy
    constructor <;> omega
  · have a := Int.mul_le_mul_of_nonpos_right h1 hy
    have b := Int.mul_le_mul_of_nonpos_right h2 hy
    constructor <;> omega

theorem inB_mul {x y : Int} {a b : Bnd} (hx : InB x a) (hy : InB y b) : InB (x * y) (bMul a b) := by
  unfold InB bMul at *
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have m1 := mul_between y hx1 hx2
  have m2 := mul_between a.1 hy1 hy2
  have m3 := mul_between a.2 hy1 hy2
  rw [Int.mul_comm y a.1, Int.mul_comm b.1 a.1, Int.mul_comm b.2 a.1] at m2
  rw [Int.mul_comm y a.2, Int.mul_comm b.1 a.2, Int.mul_comm b.2 a.2] at m3
  simp only
  constructor <;> omega

/-- The `+` of the reader: `(+ x1 ... xn)`, `n ≥ 2`, is `BINARY-+` right-associated over the
read arguments; its value lies in the sum of the arguments' intervals. -/
theorem sum_sound (env : Env) (fns : Fns) (rd : Expr → Except String Term)
    (ib : Expr → Option Bnd)
    (hel : ∀ x t v b, rd x = .ok t → Term.eval fns env t = .ok v → ib x = some b → InB v.toInt b) :
    ∀ (xs : List Expr) (ts : List Term) (bs : Bnd) (v : Val), xs ≠ [] →
      xs.mapM rd = .ok ts →
      xs.foldr (fun a acc => Option.map bAdd (ib a) <*> acc) (some (0, 0)) = some bs →
      Term.eval fns env (ts.dropLast.foldr (fun a acc => Term.app "BINARY-+" [a, acc])
        ts.getLast!) = .ok v →
      InB v.toInt bs := by
  intro xs
  induction xs with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons x xs ih =>
    intro ts bs v _ hm hf he
    simp only [List.mapM_cons] at hm
    obtain ⟨t, ht, hm⟩ := bind_ok hm
    obtain ⟨ts', hts', hm⟩ := bind_ok hm
    simp [pure, Except.pure] at hm; subst hm
    simp only [List.foldr_cons] at hf
    obtain ⟨bx, brest, hbx, hbrest, hbs⟩ := seq_some hf
    subst hbs
    cases xs with
    | nil =>
      simp [pure, Except.pure] at hts'; subst hts'
      simp at hbrest; subst hbrest
      simp at he
      have := hel x t v bx ht he hbx
      unfold InB bAdd at *; simp only at *; constructor <;> omega
    | cons y ys =>
      have hne : ts' ≠ [] := by
        intro h0; subst h0
        simp only [List.mapM_cons] at hts'
        obtain ⟨_, _, hts'⟩ := bind_ok hts'
        obtain ⟨_, _, hts'⟩ := bind_ok hts'
        simp [pure, Except.pure] at hts'
      obtain ⟨t1, ts1, rfl⟩ : ∃ t1 ts1, ts' = t1 :: ts1 := by
        cases ts' with
        | nil => exact absurd rfl hne
        | cons a b => exact ⟨a, b, rfl⟩
      have hgl : (t :: t1 :: ts1).getLast! = (t1 :: ts1).getLast! := by
        simp [List.getLast!_eq_getLast?_getD, List.getLast?_cons_cons]
      rw [List.dropLast_cons_cons, List.foldr_cons, hgl] at he
      obtain ⟨va, vb, ha, hb, hv⟩ := eval_plus _ _ _ _ _ he
      rw [hv]
      exact inB_add (hel x t va bx ht ha hbx)
        (ih (t1 :: ts1) brest vb (List.cons_ne_nil _ _) hts' hbrest hb)

theorem ival_sound (w : World) (k : Kind) (senv : SEnv) (vars stobjs : Env)
    (hok : EnvOK senv vars) (dflt : Expr → Except String Term) (hd : ∀ x t, dflt x ≠ .ok t) :
    ∀ (n m : Nat) (e : Expr) (t : Term) (v : Val) (b : Bnd),
      fixN m (readExprF w k) dflt e = .ok t →
      Term.eval w.fns (vars ++ stobjs) t = .ok v →
      fixN n (ivalF w k senv) (fun _ => none) e = some b → InB v.toInt b := by
  intro n
  induction n with
  | zero => intro m e t v b _ _ hb; simp [fixN] at hb
  | succ n ih =>
    intro m e t v b hr he hb
    cases m with
    | zero => exact absurd hr (hd e t)
    | succ m =>
      simp only [fixN] at hr hb
      cases e with
      | int i =>
        simp [ivalF] at hb; subst hb
        simp [readExprF, pure, Except.pure] at hr; subst hr
        have := eval_quote _ _ _ _ he; subst this
        exact ⟨Int.le_refl _, Int.le_refl _⟩
      | str s =>
        simp [ivalF] at hb; subst hb
        simp [readExprF, pure, Except.pure] at hr; subst hr
        have := eval_quote _ _ _ _ he; subst this
        exact ⟨Int.le_refl _, Int.le_refl _⟩
      | chr c =>
        simp [ivalF] at hb; subst hb
        simp [readExprF, pure, Except.pure] at hr; subst hr
        have := eval_quote _ _ _ _ he; subst this
        exact ⟨Int.le_refl _, Int.le_refl _⟩
      | sym nm =>
        simp only [ivalF] at hb
        simp only [readExprF] at hr
        split at hb
        · rename_i c; rw [if_pos c] at hr
          simp [pure, Except.pure] at hb hr; subst hb hr
          have := eval_quote _ _ _ _ he; subst this
          exact ⟨Int.le_refl _, Int.le_refl _⟩
        rename_i c; rw [if_neg c] at hr
        split at hb
        · cases hb
        rename_i c; rw [if_neg c] at hr
        split at hb
        · cases hb
        rename_i c; rw [if_neg c] at hr
        split at hb
        · cases hb
        rename_i c; rw [if_neg c] at hr
        split at hb
        · rename_i c; rw [if_pos c] at hr
          split at hb
          · rename_i p q hq
            rw [hq] at hr
            simp [pure, Except.pure] at hb hr; subst hb hr
            have := eval_quote _ _ _ _ he; subst this
            exact ⟨Int.le_refl _, Int.le_refl _⟩
          · cases hb
        rename_i c; rw [if_neg c] at hr
        simp [pure, Except.pure] at hr; subst hr
        have hv := eval_var _ _ _ _ he
        obtain ⟨v', hv', hin⟩ := hok nm b hb
        rw [envGet_append vars stobjs nm v' hv'] at hv
        cases hv
        exact hin
      | cons a d =>
        cases a with
        | sym f =>
          simp only [ivalF] at hb
          simp only [readExprF] at hr
          split at hr
          · simp [throw, throwThe, MonadExceptOf.throw] at hr
          rename_i hprop
          have IH := fun e t v b (h1 : fixN m (readExprF w k) dflt e = .ok t) h2 h3 =>
            ih m e t v b h1 h2 h3
          split at hb
          · -- QUOTE
            rename_i hd1; simp [hd1, pure, Except.pure] at hr hb; subst hr hb
            have := eval_quote _ _ _ _ he; subst this
            exact ⟨Int.le_refl _, Int.le_refl _⟩
          · -- IF
            rename_i hd1; simp [hd1, pure, Except.pure] at hr
            obtain ⟨tc, _, hr⟩ := bind_ok hr
            obtain ⟨ta, hta, hr⟩ := bind_ok hr
            obtain ⟨tb, htb, hr⟩ := bind_ok hr
            cases hr
            obtain ⟨ba, bb, hba, hbb, rfl⟩ := seq_some hb
            rcases eval_if _ _ _ _ _ _ he with h | h
            · exact inB_hull (Or.inl (IH _ _ _ _ hta h hba))
            · exact inB_hull (Or.inr (IH _ _ _ _ htb h hbb))
          · -- +
            rename_i args
            simp only [pure, Except.pure] at hr
            split at hr
            · rename_i hd1; cases hr
              rw [hd1] at hb; simp at hb; subst hb
              have := eval_quote _ _ _ _ he; subst this
              exact ⟨Int.le_refl _, Int.le_refl _⟩
            · rename_i a hd1
              obtain ⟨_, _, hr⟩ := bind_ok hr
              obtain ⟨ta, hta, hr⟩ := bind_ok hr
              cases hr
              rw [hd1] at hb; simp only [List.foldr_cons, List.foldr_nil] at hb
              obtain ⟨ba, b0, hba, hb0, rfl⟩ := seq_some hb
              simp at hb0; subst hb0
              obtain ⟨v0, va, h0, hva, hv⟩ := eval_plus _ _ _ _ _ he
              have := eval_quote _ _ _ _ h0; subst this
              have hin := IH _ _ _ _ hta hva hba
              rw [hv]; unfold InB bAdd at *; simp [Val.toInt] at *; constructor <;> omega
            · rename_i xs hn0 hn1
              obtain ⟨_, _, hr⟩ := bind_ok hr
              obtain ⟨ts, hts, hr⟩ := bind_ok hr
              cases hr
              have hne : d.toList ≠ [] := fun h0 => hn0 h0
              exact sum_sound _ _ _ _ IH d.toList ts b v hne hts hb he
          · -- *
            rename_i hd1; simp [hd1, pure, Except.pure] at hr
            obtain ⟨ta, hta, hr⟩ := bind_ok hr
            obtain ⟨tb, htb, hr⟩ := bind_ok hr
            cases hr
            obtain ⟨ba, bb, hba, hbb, rfl⟩ := seq_some hb
            obtain ⟨va, vb, ha, hb', hv⟩ := eval_times _ _ _ _ _ he
            rw [hv]; exact inB_mul (IH _ _ _ _ hta ha hba) (IH _ _ _ _ htb hb' hbb)
          · -- unary -
            rename_i hd1; simp [hd1, pure, Except.pure] at hr
            obtain ⟨ta, hta, hr⟩ := bind_ok hr
            cases hr
            obtain ⟨ba, hba, rfl⟩ := map_some hb
            obtain ⟨va, ha, hv⟩ := eval_neg _ _ _ _ he
            rw [hv]; exact inB_neg (IH _ _ _ _ hta ha hba)
          · -- binary -
            rename_i hd1; simp [hd1, pure, Except.pure] at hr
            obtain ⟨ta, hta, hr⟩ := bind_ok hr
            obtain ⟨tb, htb, hr⟩ := bind_ok hr
            cases hr
            obtain ⟨ba, bnb, hba, hbnb, rfl⟩ := seq_some hb
            obtain ⟨bb, hbb, rfl⟩ := map_some hbnb
            obtain ⟨va, vn, ha, hn, hv⟩ := eval_plus _ _ _ _ _ he
            obtain ⟨vb, hb', hvn⟩ := eval_neg _ _ _ _ hn
            rw [hv, hvn]
            exact inB_add (IH _ _ _ _ hta ha hba) (inB_neg (IH _ _ _ _ htb hb' hbb))
          · -- 1+
            rename_i hd1; simp [hd1, pure, Except.pure] at hr
            obtain ⟨ta, hta, hr⟩ := bind_ok hr
            cases hr
            obtain ⟨ba, hba, rfl⟩ := map_some hb
            obtain ⟨v0, va, h0, ha, hv⟩ := eval_plus _ _ _ _ _ he
            have := eval_quote _ _ _ _ h0; subst this
            rw [hv]; exact inB_add ⟨Int.le_refl _, Int.le_refl _⟩ (IH _ _ _ _ hta ha hba)
          · -- 1-
            rename_i hd1; simp [hd1, pure, Except.pure] at hr
            obtain ⟨ta, hta, hr⟩ := bind_ok hr
            cases hr
            obtain ⟨ba, hba, rfl⟩ := map_some hb
            obtain ⟨v0, va, h0, ha, hv⟩ := eval_plus _ _ _ _ _ he
            have := eval_quote _ _ _ _ h0; subst this
            rw [hv]; exact inB_add ⟨Int.le_refl _, Int.le_refl _⟩ (IH _ _ _ _ hta ha hba)
          · cases hb
        | _ => simp [ivalF] at hb

/-- **The interval is sound for the interpreter's evaluation (`ev_sound`)**: in a state whose
variables agree with `senv`, a value the interpreter computes for `e` lies in `ival w k senv e`. -/
theorem ev_sound (w : World) (k : Kind) (senv : SEnv) (st : St) (e : Expr) (v : Val) (b : Bnd)
    (hok : EnvOK senv st.vars) (hev : ev w k st e = .ok v) (hb : ival w k senv e = some b) :
    InB v.toInt b := by
  unfold ev at hev
  obtain ⟨t, ht, he⟩ := bind_ok hev
  exact ival_sound w k senv st.vars st.stobjs hok _ (fun _ _ h => by cases h) 64 readDepth e t v b
    ht he hb

/-- `evOpt` with a default whose reading lies in the default interval. -/
theorem evOpt_sound (w : World) (k : Kind) (senv : SEnv) (st : St) (e : Option Expr)
    (dflt v : Val) (bd b : Bnd) (hok : EnvOK senv st.vars) (hd : InB dflt.toInt bd)
    (hev : evOpt w k st e dflt = .ok v)
    (hb : (match e with | some x => ival w k senv x | none => some bd) = some b) :
    InB v.toInt b := by
  cases e with
  | none => simp [evOpt] at hev hb; subst hev hb; exact hd
  | some x => exact ev_sound w k senv st x v b hok hev hb

end Fn2.Arms.Bound
