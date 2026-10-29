import Mathlib.CategoryTheory.Category.RelCat

/-!
# Fn2.Square: the double category of fn2 squares

HIGHER-STRUCTURES entry 4: the reference-versus-fused square is a square of a double category of
state sets, transitions and representation relations, and it is **thin** (its content
is a proposition). This file gives that double category as plain structure, because Mathlib (at
the pinned revision) has no double categories:

* objects: state types of a representation;
* loose morphisms (`Loose A B`): partial transitions `A → Option B` (`none` is "not enabled");
* tight morphisms (`Tight A B`): representation relations `A → B → Prop`, which are the morphisms
  of Mathlib's `CategoryTheory.RelCat` (`Tight.toRelCat`, `Tight.toRelCat_comp`);
* squares (`Sq R f g R'`): the simulation condition of COHERENCE "Notation", step form.

Both compositions of squares are proved (`Sq.seq` along transitions, `Sq.stack` along relations),
with identities; the interchange law is a theorem by proof irrelevance (`Sq.interchange`), which is
exactly the sense in which "the composition laws are free" (HIGHER-STRUCTURES 4(b)). `Sq.paste` is
COHERENCE's vertical pasting along a word with a stuttering label interpretation (TR Experiment A's
`fc-rel-fold`); `Sq.paste_cover` is the catalogue form a correspondence uses: squares for the cases
of a catalogue cover every word over that catalogue.
-/

namespace Fn2.Square

universe u

/-- A loose morphism: a partial transition. -/
abbrev Loose (A B : Type u) : Type u := A → Option B

/-- A tight morphism: a representation relation. -/
abbrev Tight (A B : Type u) : Type u := A → B → Prop

namespace Loose

def ident (A : Type u) : Loose A A := fun a => some a

def comp {A B C : Type u} (f : Loose A B) (g : Loose B C) : Loose A C :=
  fun a => (f a).bind g

theorem id_comp {A B : Type u} (f : Loose A B) : comp (ident A) f = f := by
  funext a
  rfl

theorem comp_id {A B : Type u} (f : Loose A B) : comp f (ident B) = f := by
  funext a
  show (f a).bind (fun b => some b) = f a
  cases hfa : f a <;> rfl

theorem assoc {A B C D : Type u} (f : Loose A B) (g : Loose B C) (h : Loose C D) :
    comp (comp f g) h = comp f (comp g h) := by
  funext a
  show ((f a).bind g).bind h = (f a).bind (fun b => (g b).bind h)
  cases hfa : f a <;> rfl

end Loose

namespace Tight

def ident (A : Type u) : Tight A A := fun a a' => a = a'

def comp {A B C : Type u} (R : Tight A B) (S : Tight B C) : Tight A C :=
  fun a c => ∃ b, R a b ∧ S b c

open CategoryTheory in
/-- A tight edge as a morphism of Mathlib's category of relations. -/
def toRelCat {A B : Type u} (R : Tight A B) : @Quiver.Hom RelCat.{u} _ A B :=
  RelCat.Hom.ofRel {p : A × B | R p.1 p.2}

open CategoryTheory in
/-- Stacking tight edges is composition in `RelCat`. -/
theorem toRelCat_comp {A B C : Type u} (R : Tight A B) (S : Tight B C) (a : A) (c : C) :
    (a, c) ∈ (toRelCat R ≫ toRelCat S).rel ↔ comp R S a c :=
  Iff.rfl

end Tight

/-- The square with left edge `R`, top `f`, bottom `g` and right edge `R'` commutes: every related
pair whose top transition fires has a bottom transition that fires into a related pair. -/
def Sq {A A' B B' : Type u} (R : Tight A B) (f : Loose A A') (g : Loose B B') (R' : Tight A' B') :
    Prop :=
  ∀ a b a', R a b → f a = some a' → ∃ b', g b = some b' ∧ R' a' b'

/-- The greatest input relation making a forward-simulation square with the given top transition,
bottom transition and output relation: the weakest precondition on the input pair. For partial
transitions this is **not** a cartesian lift in Shulman's sense (restrictions do not compose along
transitions that never fire; Astra, `lean-meta-astra-2.md` finding 1), so no framing is claimed. -/
def restrict {A A' B B' : Type u} (f : Loose A A') (g : Loose B B') (R' : Tight A' B') :
    Tight A B :=
  fun a b => ∀ a', f a = some a' → ∃ b', g b = some b' ∧ R' a' b'

theorem Sq.iff_le_restrict {A A' B B' : Type u} {R : Tight A B} {f : Loose A A'} {g : Loose B B'}
    {R' : Tight A' B'} : Sq R f g R' ↔ ∀ a b, R a b → restrict f g R' a b :=
  ⟨fun h a b hR a' hf => h a b a' hR hf, fun h a b a' hR hf => h a b hR a' hf⟩

/-- Pasting along transitions (COHERENCE's vertical pasting, one step). -/
theorem Sq.seq {A A' A'' B B' B'' : Type u} {R : Tight A B} {R' : Tight A' B'}
    {R'' : Tight A'' B''} {f : Loose A A'} {f' : Loose A' A''} {g : Loose B B'}
    {g' : Loose B' B''} (h₁ : Sq R f g R') (h₂ : Sq R' f' g' R'') :
    Sq R (Loose.comp f f') (Loose.comp g g') R'' := by
  intro a b a'' hR hf
  cases hfa : f a with
  | none => simp [Loose.comp, hfa] at hf
  | some a' =>
    have hf' : f' a' = some a'' := by simpa [Loose.comp, hfa] using hf
    obtain ⟨b', hg, hR'⟩ := h₁ a b a' hR hfa
    obtain ⟨b'', hg', hR''⟩ := h₂ a' b' a'' hR' hf'
    exact ⟨b'', by simp [Loose.comp, hg, hg'], hR''⟩

/-- Stacking along representation relations (composition of tight edges). -/
theorem Sq.stack {A A' B B' C C' : Type u} {R : Tight A B} {R' : Tight A' B'} {S : Tight B C}
    {S' : Tight B' C'} {f : Loose A A'} {g : Loose B B'} {k : Loose C C'}
    (h₁ : Sq R f g R') (h₂ : Sq S g k S') : Sq (Tight.comp R S) f k (Tight.comp R' S') := by
  rintro a c a' ⟨b, hR, hS⟩ hf
  obtain ⟨b', hg, hR'⟩ := h₁ a b a' hR hf
  obtain ⟨c', hk, hS'⟩ := h₂ b c b' hS hg
  exact ⟨c', hk, b', hR', hS'⟩

/-- The identity square on a tight edge (no transition). -/
theorem Sq.idLoose {A B : Type u} (R : Tight A B) : Sq R (Loose.ident A) (Loose.ident B) R := by
  intro a b a' hR hf
  have e : a = a' := Option.some.inj hf
  subst e
  exact ⟨b, rfl, hR⟩

/-- The identity square on a loose edge (the identity representation relation). -/
theorem Sq.idTight {A A' : Type u} (f : Loose A A') : Sq (Tight.ident A) f f (Tight.ident A') := by
  intro a b a' hab hf
  have e : a = b := hab
  subst e
  exact ⟨a', hf, rfl⟩

/-- Thinness: a square has at most one proof. -/
theorem Sq.thin {A A' B B' : Type u} {R : Tight A B} {f : Loose A A'} {g : Loose B B'}
    {R' : Tight A' B'} (h₁ h₂ : Sq R f g R') : h₁ = h₂ :=
  rfl

/-- The interchange law of the double category, free by thinness. -/
theorem Sq.interchange {A A' A'' B B' B'' C C' C'' : Type u}
    {R : Tight A B} {R' : Tight A' B'} {R'' : Tight A'' B''}
    {S : Tight B C} {S' : Tight B' C'} {S'' : Tight B'' C''}
    {f : Loose A A'} {f' : Loose A' A''} {g : Loose B B'} {g' : Loose B' B''}
    {k : Loose C C'} {k' : Loose C' C''}
    (α : Sq R f g R') (β : Sq S g k S') (γ : Sq R' f' g' R'') (δ : Sq S' g' k' S'') :
    Sq.seq (Sq.stack α β) (Sq.stack γ δ) = Sq.stack (Sq.seq α γ) (Sq.seq β δ) :=
  rfl

/-! ## Runs and pasting along words -/

/-- The run of a word of labels. -/
def run {S L : Type u} (step : L → Loose S S) : List L → Loose S S
  | [] => Loose.ident S
  | t :: w => Loose.comp (step t) (run step w)

theorem run_append {S L : Type u} (step : L → Loose S S) (v w : List L) :
    run step (v ++ w) = Loose.comp (run step v) (run step w) := by
  induction v with
  | nil => exact (Loose.id_comp _).symm
  | cons t v ih =>
    show Loose.comp (step t) (run step (v ++ w)) =
      Loose.comp (Loose.comp (step t) (run step v)) (run step w)
    rw [ih, Loose.assoc]

theorem run_pair {S L : Type u} (step : L → Loose S S) (t u : L) (s : S) :
    run step [t, u] s = (step t s).bind (step u) := by
  show (step t s).bind (fun x => (step u x).bind (fun y => some y)) = (step t s).bind (step u)
  congr 1
  funext x
  cases hx : step u x <;> rfl

/-- A label interpretation into words of the other side (the square may stutter), extended to
words. -/
def expand {L M : Type u} (h : L → List M) : List L → List M
  | [] => []
  | t :: w => h t ++ expand h w

/-- Vertical pasting (COHERENCE §2.2; TR Experiment A's `fc-rel-fold`): a square for every label
is a square for every word. -/
theorem Sq.paste {S T L M : Type u} {stepA : L → Loose S S} {stepB : M → Loose T T}
    (h : L → List M) (R : Tight S T) (hstep : ∀ t, Sq R (stepA t) (run stepB (h t)) R) :
    ∀ w, Sq R (run stepA w) (run stepB (expand h w)) R := by
  intro w
  induction w with
  | nil => exact Sq.idLoose R
  | cons t w ih =>
    show Sq R (Loose.comp (stepA t) (run stepA w)) (run stepB (h t ++ expand h w)) R
    rw [run_append]
    exact Sq.seq (hstep t) ih

/-- The catalogue form: squares for the cases of a catalogue cover every word whose labels are in
the catalogue. A correspondence binds one statement per case (DSL-METATHEORY §3.2); this is the
implication that makes the bound cases sufficient. -/
theorem Sq.paste_cover {S T L M : Type u} {stepA : L → Loose S S} {stepB : M → Loose T T}
    (h : L → List M) (R : Tight S T) (cat : List L)
    (hstep : ∀ t ∈ cat, Sq R (stepA t) (run stepB (h t)) R) :
    ∀ w : List L, (∀ t ∈ w, t ∈ cat) → Sq R (run stepA w) (run stepB (expand h w)) R := by
  intro w
  induction w with
  | nil => intro _; exact Sq.idLoose R
  | cons t w ih =>
    intro hw
    show Sq R (Loose.comp (stepA t) (run stepA w)) (run stepB (h t ++ expand h w)) R
    rw [run_append]
    exact Sq.seq (hstep t (hw t (by simp))) (ih fun x hx => hw x (by simp [hx]))

end Fn2.Square
