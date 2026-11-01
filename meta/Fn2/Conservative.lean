import Fn2.Coherence

/-!
# Fn2.Conservative: an `ext`-grade revision is conservative over its base

MODAL-KERNEL R4 at grade `ext` and COHERENCE Q9: a revision `T₃ → T₄` that adds new event kinds
(thread annotations) with a declared old meaning `h`, a projection `π : S₄ → S₃` and a converter.
Its certificate is G0 (`π (convert s) = s`) plus one G1 square per new-theory event,
`π (step₄ e s) = run₃ (h e) (π s)` in relational form, plus the lifting of every base event.

`conservative`: under that certificate, for **every** property `φ` of a base word and the base
state it reaches, `φ` holds of every base run from `s₀` iff it holds of every revised run from
`convert s₀`, read through `h` and `π`; `runs_exactly` is its content (the base runs are exactly
the projected, translated revised runs). This is semantic run conservativity: no syntax or
derivability relation of theories is represented, and `Extension.step` is forward simulation of
successful steps, so a new label may be disabled where its translated word succeeds (Astra,
`lean-meta-astra-2.md` finding 6). Model expansion is a different statement and is not claimed.

Witnesses: `revision` (posts and annotations over a post count) is an `Extension` and inherits
the base fact "the count is the number of posts" (`revision_counts`, satisfiable and non-trivial:
the fact quantifies over every word with annotations interleaved); `badRevision`, whose annotation
also bumps the count, breaks the same fact (`badRevision_breaks_counts`): its G1 square for
`annotate` is false (`badRevision_annotate_not_square`), which is exactly the certificate the
conservativity theorem consumes.
-/

namespace Fn2.Conservative

open Fn2.Square Fn2.Coherence

universe u

/-- An `ext`-grade revision of `Base` to `Ext`, with its certificate. -/
structure Extension (Base Ext : Frame.{u}) where
  proj : Ext.State → Base.State
  translate : Ext.Label → List Base.Label
  inj : Base.Label → Ext.Label
  convert : Base.State → Ext.State
  translate_inj : ∀ e, translate (inj e) = [e]
  proj_convert : ∀ s, proj (convert s) = s
  step : ∀ e, Sq (fun x y => proj x = y) (Ext.step e) (run Base.step (translate e))
    (fun x y => proj x = y)
  lift : ∀ e x y, Base.step e (proj x) = some y → ∃ x', Ext.step (inj e) x = some x' ∧ proj x' = y

theorem expand_map {Base Ext : Frame.{u}} (X : Extension Base Ext) (w : List Base.Label) :
    expand X.translate (w.map X.inj) = w := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    show X.translate (X.inj e) ++ expand X.translate (w.map X.inj) = e :: w
    simp [X.translate_inj, ih]

theorem lift_run {Base Ext : Frame.{u}} (X : Extension Base Ext) :
    ∀ (w : List Base.Label) (x : Ext.State) (y : Base.State),
      run Base.step w (X.proj x) = some y →
      ∃ x', run Ext.step (w.map X.inj) x = some x' ∧ X.proj x' = y := by
  intro w
  induction w with
  | nil =>
    intro x y h
    exact ⟨x, rfl, Option.some.inj h⟩
  | cons e w ih =>
    intro x y h
    have h' : (Base.step e (X.proj x)).bind (run Base.step w) = some y := h
    cases hs : Base.step e (X.proj x) with
    | none =>
      rw [hs] at h'
      simp at h'
    | some m =>
      rw [hs] at h'
      have hm : run Base.step w m = some y := h'
      obtain ⟨x₁, hx₁, hp₁⟩ := X.lift e x m hs
      have hm' : run Base.step w (X.proj x₁) = some y := by rw [hp₁]; exact hm
      obtain ⟨x', hx', hp'⟩ := ih x₁ y hm'
      refine ⟨x', ?_, hp'⟩
      show (Ext.step (X.inj e) x).bind (run Ext.step (w.map X.inj)) = some x'
      rw [hx₁]
      exact hx'

/-- **Conservativity.** Every property of base runs from `s₀` holds iff it holds of the revised
runs from `convert s₀`, read through the translation and the projection. -/
theorem conservative {Base Ext : Frame.{u}} (X : Extension Base Ext) (s₀ : Base.State)
    (φ : List Base.Label → Base.State → Prop) :
    (∀ w s', run Base.step w s₀ = some s' → φ w s') ↔
    (∀ w s', run Ext.step w (X.convert s₀) = some s' → φ (expand X.translate w) (X.proj s')) := by
  constructor
  · intro hb w s' hrun
    obtain ⟨b', hb', he⟩ :=
      Sq.paste X.translate (fun x y => X.proj x = y) X.step w (X.convert s₀) s₀ s'
        (X.proj_convert s₀) hrun
    have he' : X.proj s' = b' := he
    rw [he']
    exact hb _ _ hb'
  · intro hx w s' hrun
    have hrun' : run Base.step w (X.proj (X.convert s₀)) = some s' := by
      rw [X.proj_convert]; exact hrun
    obtain ⟨x', hx', hp⟩ := lift_run X w (X.convert s₀) s' hrun'
    have := hx _ _ hx'
    rwa [expand_map X, hp] at this

/-- The semantic content made explicit (Astra's proposed statement): the base runs from `s₀` are
exactly the projections of the revised runs from `convert s₀`, read through the translation. -/
theorem runs_exactly {Base Ext : Frame.{u}} (X : Extension Base Ext) (s₀ : Base.State)
    (w : List Base.Label) (b : Base.State) :
    run Base.step w s₀ = some b ↔
      ∃ w' x', run Ext.step w' (X.convert s₀) = some x' ∧ expand X.translate w' = w ∧
        X.proj x' = b := by
  constructor
  · intro h
    have h' : run Base.step w (X.proj (X.convert s₀)) = some b := by
      rw [X.proj_convert]; exact h
    obtain ⟨x', hx', hp⟩ := lift_run X w (X.convert s₀) b h'
    exact ⟨w.map X.inj, x', hx', expand_map X w, hp⟩
  · rintro ⟨w', x', hx', hw, hp⟩
    obtain ⟨b', hb', he⟩ :=
      Sq.paste X.translate (fun x y => X.proj x = y) X.step w' (X.convert s₀) s₀ x'
        (X.proj_convert s₀) hx'
    have he' : X.proj x' = b' := he
    subst hw
    subst hp
    rw [he']
    exact hb'

/-! ## The toy: posts, and a revision that adds thread annotations -/

/-- The base theory: a post count. -/
abbrev base : Frame.{0} where
  State := Nat
  Label := Unit
  step _ n := some (n + 1)

inductive E4
  | post | annotate
  deriving DecidableEq, Repr

/-- The revision: a post count and an annotation count; an annotation means nothing old. -/
abbrev revised : Frame.{0} where
  State := Nat × Nat
  Label := E4
  step e s := match e with
    | .post => some (s.1 + 1, s.2)
    | .annotate => some (s.1, s.2 + 1)

/-- The faulty revision: its annotation also bumps the post count. -/
abbrev badRevised : Frame.{0} where
  State := Nat × Nat
  Label := E4
  step e s := match e with
    | .post => some (s.1 + 1, s.2)
    | .annotate => some (s.1 + 1, s.2 + 1)

def translate4 : E4 → List Unit
  | .post => [()]
  | .annotate => []

def revision : Extension base revised where
  proj s := s.1
  translate := translate4
  inj _ := .post
  convert n := (n, 0)
  translate_inj _ := rfl
  proj_convert _ := rfl
  step e := by
    intro x y x' hxy hx
    have hxy' : x.1 = y := hxy
    subst hxy'
    cases e with
    | post =>
      have e' : x' = (x.1 + 1, x.2) := (Option.some.inj hx).symm
      subst e'
      exact ⟨x.1 + 1, rfl, rfl⟩
    | annotate =>
      have e' : x' = (x.1, x.2 + 1) := (Option.some.inj hx).symm
      subst e'
      exact ⟨x.1, rfl, rfl⟩
  lift _ x _ h := ⟨(x.1 + 1, x.2), rfl, Option.some.inj h⟩

/-- The base fact: from `n`, the count is `n` plus the number of posts. -/
def postsCount (s₀ : Nat) (w : List Unit) (n : Nat) : Prop := n = s₀ + w.length

theorem base_counts : ∀ (w : List Unit) (n s' : Nat), run base.step w n = some s' →
    postsCount n w s' := by
  intro w
  induction w with
  | nil =>
    intro n s' h
    have e : n = s' := Option.some.inj h
    subst e
    show n = n + 0
    simp
  | cons e w ih =>
    intro n s' h
    have h' : run base.step w (n + 1) = some s' := h
    have := ih (n + 1) s' h'
    show s' = n + (w.length + 1)
    have hc : s' = n + 1 + w.length := this
    omega

/-- Satisfiable: the revision inherits the base fact over every word, annotations included. -/
theorem revision_counts : ∀ w s', run revised.step w (revision.convert 0) = some s' →
    postsCount 0 (expand revision.translate w) (revision.proj s') :=
  (conservative revision 0 (postsCount 0)).mp (fun w s' h => base_counts w 0 s' h)

/-- Teeth: the faulty revision breaks the inherited fact at one annotation. -/
theorem badRevision_breaks_counts :
    ¬ ∀ w s', run badRevised.step w (0, 0) = some s' → postsCount 0 (expand translate4 w) s'.1 := by
  intro h
  have h1 := h [E4.annotate] (1, 1) rfl
  have h2 : (1 : Nat) = 0 := h1
  exact absurd h2 (by decide)

/-- ...and the certificate fails exactly there: its `annotate` square is false. -/
theorem badRevision_annotate_not_square :
    ¬ Sq (fun (x : Nat × Nat) (y : Nat) => x.1 = y) (badRevised.step E4.annotate)
      (run base.step (translate4 E4.annotate)) (fun (x : Nat × Nat) (y : Nat) => x.1 = y) := by
  intro h
  obtain ⟨b', hb, hR⟩ := h (0, 0) 0 (1, 1) rfl rfl
  have hb' : (0 : Nat) = b' := Option.some.inj hb
  have hR' : (1 : Nat) = b' := hR
  omega

end Fn2.Conservative
