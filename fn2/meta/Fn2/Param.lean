/-!
# Fn2.Param: parametricity for a declaration client that never inspects the representation

HIGHER-STRUCTURES entry 1: Reynolds' General Type Definition Theorem, for the first-order client
language fn2's declarations admit. An interface is a carrier with an initial state, commands and
an observation (`Impl`); a client (`Client`) may issue commands and read observations and nothing
else. That restriction is Reynolds' `e ∈ E_{π-t}`, which `defmachine-callback` will check
syntactically in ACL2 (`all-fnnames` of the admitted body contained in the declared `:uses`,
HIGHER-STRUCTURES 1(b) item 1).

`abstraction`: if two implementations' primitives are related (initial states related, every
command preserves the relation, related states observe alike), then every client gets the same
result from related states. Lean has no internal parametricity, so the client language is a deep
embedding and the theorem is an induction over it; the premise (`Related`) is the irreducible
content, as TR Experiment B's 20 correspondence lines were.

Witnesses: `counter` and `doubled` (a count, and twice the count with halving on observation) are
related (`counter_doubled_related`), so every client agrees on them (`counter_doubled_clients`):
satisfiable, over every client. Teeth: a client language with one representation-inspecting
primitive (`PeekClient.peek`, Wadler's polymorphic equality in fn2 dress) separates the same two
related implementations (`peek_breaks_abstraction`), so the syntactic restriction is necessary; and
dropping the premise's command clause while keeping initial states and observations related lets a
permitted client separate them (`drop_exec_breaks`), so the premise is necessary too.
-/

namespace Fn2.Param

/-- One representation of an interface. -/
structure Impl (Cmd Obs : Type) where
  σ : Type
  init : σ
  exec : Cmd → σ → σ
  obs : σ → Obs

/-- A client that never inspects the representation. -/
inductive Client (Cmd Obs R : Type)
  | done (r : R)
  | cmd (c : Cmd) (k : Client Cmd Obs R)
  | observe (k : Obs → Client Cmd Obs R)

def Client.run {Cmd Obs R : Type} (I : Impl Cmd Obs) : Client Cmd Obs R → I.σ → R
  | .done r, _ => r
  | .cmd c k, s => Client.run I k (I.exec c s)
  | .observe k, s => Client.run I (k (I.obs s)) s

/-- The primitives of two implementations are related by `R`. -/
structure Related {Cmd Obs : Type} (I J : Impl Cmd Obs) (R : I.σ → J.σ → Prop) : Prop where
  init : R I.init J.init
  exec : ∀ c s t, R s t → R (I.exec c s) (J.exec c t)
  obs : ∀ s t, R s t → I.obs s = J.obs t

/-- **Abstraction.** Related primitives give every client the same result. -/
theorem abstraction {Cmd Obs R' : Type} {I J : Impl Cmd Obs} {R : I.σ → J.σ → Prop}
    (h : Related I J R) :
    ∀ (p : Client Cmd Obs R') (s : I.σ) (t : J.σ), R s t → Client.run I p s = Client.run J p t := by
  intro p
  induction p with
  | done r => intro s t _; rfl
  | cmd c k ih => intro s t hst; exact ih _ _ (h.exec c s t hst)
  | observe k ih =>
    intro s t hst
    show Client.run I (k (I.obs s)) s = Client.run J (k (J.obs t)) t
    rw [h.obs s t hst]
    exact ih _ _ _ hst

/-- From the initial states: the client cannot tell the implementations apart. -/
theorem independent {Cmd Obs R' : Type} {I J : Impl Cmd Obs} {R : I.σ → J.σ → Prop}
    (h : Related I J R) (p : Client Cmd Obs R') : Client.run I p I.init = Client.run J p J.init :=
  abstraction h p _ _ h.init

/-! ## Witnesses -/

def counter : Impl Unit Nat where
  σ := Nat
  init := 0
  exec _ n := n + 1
  obs n := n

def doubled : Impl Unit Nat where
  σ := Nat
  init := 0
  exec _ n := n + 2
  obs n := n / 2

theorem counter_doubled_related : Related counter doubled (fun (a b : Nat) => b = 2 * a) :=
  { init := rfl
    exec := fun _ s t h => by
      have h' : t = 2 * s := h
      show t + 2 = 2 * (s + 1)
      omega
    obs := fun s t h => by
      have h' : t = 2 * s := h
      show s = t / 2
      omega }

/-- Satisfiable over every client. -/
theorem counter_doubled_clients {R' : Type} (p : Client Unit Nat R') :
    Client.run counter p counter.init = Client.run doubled p doubled.init :=
  independent counter_doubled_related p

/-- Teeth for the premise: keep the initial states and the observation related and drop command
preservation, and a permitted client (one command, then observe) separates the two. -/
def fast : Impl Unit Nat where
  σ := Nat
  init := 0
  exec _ n := n + 2
  obs n := n

def cmdObserve : Client Unit Nat Nat := .cmd () (.observe fun o => .done o)

theorem drop_exec_breaks :
    (fun (a b : Nat) => b = a) counter.init fast.init ∧
    (∀ s t : Nat, t = s → counter.obs s = fast.obs t) ∧
    Client.run counter cmdObserve counter.init ≠ Client.run fast cmdObserve fast.init :=
  ⟨rfl, fun s t h => by subst h; rfl, by decide⟩

/-- A client language with one primitive that reads the raw representation. -/
inductive PeekClient (Cmd Obs R : Type)
  | done (r : R)
  | cmd (c : Cmd) (k : PeekClient Cmd Obs R)
  | observe (k : Obs → PeekClient Cmd Obs R)
  | peek (k : Nat → PeekClient Cmd Obs R)

def PeekClient.run {Cmd Obs R : Type} (I : Impl Cmd Obs) (raw : I.σ → Nat) :
    PeekClient Cmd Obs R → I.σ → R
  | .done r, _ => r
  | .cmd c k, s => PeekClient.run I raw k (I.exec c s)
  | .observe k, s => PeekClient.run I raw (k (I.obs s)) s
  | .peek k, s => PeekClient.run I raw (k (raw s)) s

/-- Issue one command, then report the raw representation. -/
def peekClient : PeekClient Unit Nat Nat := .cmd () (.peek fun n => .done n)

/-- Teeth: inspecting the representation separates two related implementations. -/
theorem peek_breaks_abstraction :
    PeekClient.run counter (fun (n : Nat) => n) peekClient counter.init ≠
      PeekClient.run doubled (fun (n : Nat) => n) peekClient doubled.init := by
  decide

end Fn2.Param
