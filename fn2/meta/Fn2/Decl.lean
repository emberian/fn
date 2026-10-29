/-!
# Fn2.Decl: the declaration kinds and the registry

The Lean presentation of DSL-METATHEORY §1-2. A declaration is a presentation
`(kind, name, signature, laws, provenance)` of one of fourteen kinds in four families; its
identity is qualified, `(:machine fn2-echo)`; the registry is the world tables the forms write.

Each structure below is the row one ACL2 form writes today, field for field (the emitter,
`emit/emit_lean.py`, refuses a row with a key it does not know). Symbols are a parameter `S`: an
emitted registry instantiates it with its own finite alphabet (`Fn2.Instances.LayerA.Sym`), so every
well-formedness check is decidable by evaluation. ACL2 terms (formulas, initialisers, capacities)
are `Opaque`: their printed text, never an interpreted Lean term (LEAN-METATHEORY §3).

`MachineDecl.WF` is the part of `defmachine`'s expansion guard (`machines.lisp:243-258`) that the
recorded row can express (symbol classes, initial-value syntax and the common columns are not modelled);
`Registry.WF` adds the cross-row facts the registry promises (qualified identities unique, every
machine's columns table present, every core child's stobj declared). The model omits, by name, what
DSL-METATHEORY deletes or does not yet trust (`:packed`, `:obligations`, `:layout`,
`:calling-convention`).
-/

namespace Fn2.Decl

/-- DSL-METATHEORY §1.1: the four families. -/
inductive Family
  | data | behaviour | relation | obligation
  deriving DecidableEq, Repr

/-- DSL-METATHEORY §1.1: the fourteen kinds. -/
inductive Kind
  | columns | coreChild | layout | shape
  | machine | callback | command
  | projection | summary | port | migration | correspondence
  | owed | square
  deriving DecidableEq, Repr

def Kind.family : Kind → Family
  | .columns | .coreChild | .layout | .shape => .data
  | .machine | .callback | .command => .behaviour
  | .projection | .summary | .port | .migration | .correspondence => .relation
  | .owed | .square => .obligation

def Kind.all : List Kind :=
  [.columns, .coreChild, .layout, .shape, .machine, .callback, .command,
   .projection, .summary, .port, .migration, .correspondence, .owed, .square]

theorem Kind.mem_all (k : Kind) : k ∈ Kind.all := by
  cases k <;> decide

theorem Kind.all_length : Kind.all.length = 14 := rfl

/-- DSL-METATHEORY §1.2's nine artifacts, and the tenth: the declaration's Lean presentation
(LEAN-METATHEORY §3). Nothing on this list may be hand-written beside the declaration. -/
inductive Artifact
  | carrier | access | codec | logicalView | registryRow | obligations
  | simulatorHooks | owedStubs | atcLowering | leanPresentation
  deriving DecidableEq, Repr

/-- A qualified identity, `(:machine fn2-echo)`. -/
structure DeclId (S : Type) where
  kind : Kind
  name : S
  deriving DecidableEq, Repr

/-- An ACL2 term as the world printed it. The Lean side never interprets it. -/
structure Opaque where
  text : String
  deriving DecidableEq, Repr

/-- A column's carrier kind (`fn2-columns-kindp`, `columns.lisp`). -/
inductive ColKind (S : Type)
  | u8 | u16 | u32 | u60 | u64 | bool
  | enum (name : S) (tags : List S)
  deriving DecidableEq, Repr

/-- `fn2-columns-width`: an enum is stored in 8 bits. -/
def ColKind.width {S : Type} : ColKind S → Nat
  | .u8 => 8 | .u16 => 16 | .u32 => 32 | .u60 => 60 | .u64 => 64 | .bool => 1
  | .enum _ _ => 8

def ColKind.tags? {S : Type} : ColKind S → Option (List S)
  | .enum _ tags => some tags
  | _ => none

structure Column (S : Type) where
  name : S
  kind : ColKind S
  deriving DecidableEq, Repr

structure Budget where
  bytes : Nat
  steps : Nat
  descriptors : Nat
  deriving DecidableEq, Repr

/-- The row `defcolumns` writes to `fn2-columns` (`columns.lisp:602-605`). -/
structure ColumnsDecl (S : Type) where
  name : S
  columns : List (Column S)
  rowsBound : Opaque
  extraFields : List S
  initName : S
  deriving Repr

/-- The row `defmachine` writes to `fn2-machine-kinds` (`machines.lisp:234-240`). -/
structure MachineDecl (S : Type) where
  name : S
  states : List S
  columns : List (Column S)
  accounts : List S
  budget : Budget
  continuations : List (S × S)
  observes : List (S × S)
  capacity : Opaque
  initial : List (S × Opaque)
  deriving Repr

inductive RefTreatment
  | state | environment
  deriving DecidableEq, Repr

inductive Stratum
  | foundation | machine | extension
  deriving DecidableEq, Repr

/-- The row `defcorechild` writes to `fn2-core-children` (`core-children.lisp:38`). -/
structure CoreChildDecl (S : Type) where
  field : S
  stobj : S
  init : Opaque
  profilep : Opaque
  reference : RefTreatment
  order : Stratum
  why : String
  deriving Repr

/-- The row `defthm-owed` writes to `fn2-owed` (`owed.lisp:18`). -/
structure OwedDecl (S : Type) where
  name : S
  vars : List S
  formula : Opaque
  teeth : List S
  doc : String
  status : S
  deriving Repr

/-- The registry: the world tables, in declaration order. -/
structure Registry (S : Type) where
  machines : List (MachineDecl S)
  columns : List (ColumnsDecl S)
  coreChildren : List (CoreChildDecl S)
  owed : List (OwedDecl S)
  deriving Repr

variable {S : Type} [DecidableEq S]

def MachineDecl.columnNames (m : MachineDecl S) : List S := m.columns.map Column.name

/-- Recorded-row consistency, the part of `defmachine`'s guard (`machines.lisp:243-258`) the row
can express: non-empty distinct states with at most 256 tags; continuation keys equal the states in
order; distinct observation, column and initialisation keys; initialisation keys name columns; the
first column is an enum whose tags equal the states. It does not check symbol classes, initial-value
syntax (opaque here), the first column's name or the presence of the common columns. -/
abbrev MachineDecl.WF (m : MachineDecl S) : Prop :=
  m.states ≠ [] ∧ m.states.Nodup ∧ m.states.length ≤ 256 ∧
  m.continuations.map Prod.fst = m.states ∧
  (m.observes.map Prod.fst).Nodup ∧
  m.columnNames.Nodup ∧
  (m.initial.map Prod.fst).Nodup ∧
  (∀ x ∈ m.initial.map Prod.fst, x ∈ m.columnNames) ∧
  (m.columns.head?.bind fun c => c.kind.tags?) = some m.states

def Registry.ids (r : Registry S) : List (DeclId S) :=
  r.machines.map (fun m => ⟨.machine, m.name⟩) ++
  r.columns.map (fun c => ⟨.columns, c.name⟩) ++
  r.coreChildren.map (fun c => ⟨.coreChild, c.field⟩) ++
  r.owed.map (fun o => ⟨.owed, o.name⟩)

def Registry.columnsNames (r : Registry S) : List S := r.columns.map ColumnsDecl.name

/-- What the registry promises across rows (DSL-METATHEORY §2.2-2.3): qualified identities are
unique; `defmachine NAME` emitted `defcolumns NAME` with the same columns (`machines.lisp:213`);
every core child requires `(:columns STOBJ)`. -/
abbrev Registry.WF (r : Registry S) : Prop :=
  r.ids.Nodup ∧
  (∀ m ∈ r.machines, m.WF) ∧
  (∀ m ∈ r.machines, ∃ c ∈ r.columns, c.name = m.name ∧ c.columns = m.columns) ∧
  (∀ c ∈ r.coreChildren, c.stobj ∈ r.columnsNames)

/-! ## The case catalogue (DSL-METATHEORY §3.2), and the squares a correspondence binds -/

/-- The executor's case source (DSL-METATHEORY §3.2): it is not a machine, and contributes seven
labels from the hand-written executor (`executor.lisp`). -/
inductive ExecutorCase
  | clock | signal | service (i : Fin 4) | emptyPrincipal
  deriving DecidableEq, Repr

/-- A case label of a correspondence. Machines contribute one per continuation phase and one per
observed event; the generated router contributes the fallback; the executor contributes its seven. -/
inductive CaseLabel (S : Type)
  | phase (machine phase : S)
  | event (machine event : S)
  | routerFallback
  | executor (c : ExecutorCase)
  deriving DecidableEq, Repr

def MachineDecl.cases (m : MachineDecl S) : List (CaseLabel S) :=
  m.continuations.map (fun p => .phase m.name p.1) ++
  m.observes.map (fun o => .event m.name o.1)

def Registry.machineCases (r : Registry S) : List (CaseLabel S) :=
  r.machines.flatMap MachineDecl.cases

/-- COHERENCE §2.1 and §2.5's schemata, with DSL-METATHEORY §3.1's three non-square schemata. -/
inductive Schema
  | g0 | g1 | g1q | g2 | route | crash | bound | invariant | assertion
  deriving DecidableEq, Repr

/-- One row of the obligation store `fn2-squares` (DSL-METATHEORY §3.1), reduced to what the
model can check: its schema, its owning correspondence and its case. -/
structure SquareDecl (S : Type) where
  schema : Schema
  owner : String
  case : CaseLabel S
  deriving DecidableEq, Repr

/-- What `defsquare OWNER :template :q1-loop-iteration :cases-from (...)` binds: one G1 row per
case of its case sources. -/
def bindG1 (owner : String) (cases : List (CaseLabel S)) : List (SquareDecl S) :=
  cases.map fun c => ⟨.g1, owner, c⟩

end Fn2.Decl
