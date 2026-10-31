import Fn2.ACL2.Val

/-!
# Fn2.Decl: the declaration kinds and the registry

The Lean presentation of DSL-METATHEORY §1-2. A declaration is a presentation
`(kind, name, signature, laws, provenance)` of one of fourteen kinds in four families; its
identity is qualified, `(:machine fn2-echo)`; the registry is the world tables the forms write.

Each structure below is the row one ACL2 form writes on dev, field for field (the emitter,
`emit/emit_lean.py`, refuses a row with a key it neither consumes nor omits by name). Symbols are a
parameter `S`: an emitted registry instantiates it with its own finite alphabet
(`Fn2.Instances.LayerA.Sym`), so every well-formedness check is decidable by evaluation. Where the
vocabulary is closed a value is a term or data, never printed text: an ACL2 term (a capacity, an
initialiser, a cost bound, a square's statement) is a `Term` ACL2 translated; a structured value (a
field specification, a callback map, an effect list) is a `Datum`, the ACL2 object itself.

`MachineDecl.WF` is the part of `defmachine`'s expansion guard the recorded row can express;
`Registry.WF` adds the cross-row facts the registry promises.
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

/-- The world's declaration tables (`fn2-decl-table`, `declare.lisp`), plus the two tables a form
writes outside the protocol: B's `fn2-layouts` and the generator's `fn2-machine-arm-contracts`. -/
inductive Table
  | columns | machine | operationSet | coreChild | square | correspondence | command | cost
  | schema | port | wait | layout | armContract
  deriving DecidableEq, Repr

/-- A qualified identity, `(:machine fn2-echo)`: a table and a name. -/
structure DeclId (S : Type) where
  table : Table
  name : S
  deriving DecidableEq, Repr

/-- An ACL2 object carried as data (a field specification, a grammar's syntax, a callback map):
a `Val`, structural and comparable, never printed text. -/
abbrev Datum := Fn2.ACL2.Val

/-- An ACL2 term, translated by ACL2 (a capacity, an initialiser, a square's statement). -/
abbrev Term := Fn2.ACL2.Term

/-- A column's carrier kind (`fn2-columns-kindp`, `columns.lisp`). -/
inductive ColKind (S : Type)
  | u8 | u16 | u32 | u60 | u64 | bool | link
  | enum (name : S) (tags : List S)
  deriving DecidableEq, Repr

/-- `fn2-columns-width`: a link is 32 bits, an enum is stored in 8. -/
def ColKind.width {S : Type} : ColKind S → Nat
  | .u8 => 8 | .u16 => 16 | .u32 => 32 | .u60 => 60 | .u64 => 64 | .bool => 1 | .link => 32
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

/-- DSL-METATHEORY §2.2's common keys, on every row the protocol writes: the owning layer, the
book, and the requirements (`:decl-id` is the row's identity, checked by the emitter; `:generated`,
`:signature` and `:reuse` are event text, omitted by name). -/
structure Common (S : Type) where
  layer : S
  book : String
  requires : Datum
  deriving Repr

/-- The row `defcolumns` writes to `fn2-columns`. -/
structure ColumnsDecl (S : Type) where
  name : S
  columns : List (Column S)
  rowsBound : Nat
  extraFields : Datum
  initName : S
  putPolicy : List S
  common : Common S
  deriving Repr

/-- A machine's initial value for a column: a constant, or an initialiser function of the row's
slot, base, count and generation (`machines-a.lisp`). -/
inductive Init (S : Type)
  | value (t : Term)
  | function (f : S)
  deriving Repr

/-- The row `defmachine` writes to `fn2-machine-kinds` (`machines.lisp`, `fn2-machine-events`).
The step-language arms (`:arms :subarms :observe-arms`) are consumed translated, from the
embedding (`Fn2.Instances.LayerAKinds`); `:layout` (a duplicate of `:columns`), `:packed` and
`:calling-convention` are omitted by name. -/
structure MachineDecl (S : Type) where
  name : S
  states : List S
  columns : List (Column S)
  table : List (Column S)
  holds : List (S × List S)
  admission : Datum
  taken : Datum
  budget : Budget
  /-- `(phase, arm function, contract)`: a step-form kind's contract is derived (the
  `armContract` rows); an older kind's hand contract is carried as data -/
  continuations : List (S × S × Datum)
  observes : List (S × S × Datum)
  capacity : Term
  initial : List (S × Init S)
  cases : List (S × S × S)
  stops : List S
  stepForm : Bool
  common : Common S
  deriving Repr

inductive RefTreatment
  | state | environment
  deriving DecidableEq, Repr

inductive Stratum
  | foundation | machine | extension
  deriving DecidableEq, Repr

/-- The row `defcorechild` writes to `fn2-core-children`. Its initialiser and profile condition are
terms over `PROFILE` and the child's stobj (translated where the world includes the assembly). -/
structure CoreChildDecl (S : Type) where
  field : S
  stobj : S
  init : Term
  profilep : Term
  reference : RefTreatment
  order : Stratum
  why : String
  common : Common S
  deriving Repr

/-- A row of the obligation store `fn2-squares` (DSL-METATHEORY §3.1): `defthm-owed` and the
correspondences write it. Its statement is carried translated (`translated`), its source as data. -/
structure SquareRow (S : Type) where
  name : S
  schema : S
  template : Datum
  owner : Datum
  origin : Datum
  case : Datum
  caseSource : Datum
  boundary : Datum
  contract : Datum
  sides : Datum
  shared : Datum
  claim : Datum
  sharedHandlerMutation : Datum
  statement : Datum
  vars : List S
  teeth : Datum
  doc : String
  checker : Datum
  proof : Datum
  checks : Datum
  translated : Term
  common : Common S
  deriving Repr

/-- The row `defcost` writes to `fn2-costs` (`arms.lisp`): a declared operation's work bounds (as
terms: a number or a constant), the tables it touches, its own writes, its D0 effects, its answer
set and its child-form body. -/
structure CostDecl (S : Type) where
  fn : S
  bytes : Term
  steps : Term
  descriptors : Term
  tables : Datum
  ownWrites : Datum
  effects : Datum
  target : Datum
  answers : Datum
  child : Option S
  doc : String
  proof : Datum
  common : Common S
  deriving Repr

/-- The row `defwait` writes to `fn2-waits` (`machines.lisp`). -/
structure WaitDecl (S : Type) where
  name : S
  kind : S
  ready : S
  grant : S
  park : Option S
  doc : String
  common : Common S
  deriving Repr

/-- A row of the other tables (`defport`'s and `defcarrier`'s and `defgrammar`'s commands, ports,
operation sets, C's schemas, correspondences, B's layouts, the derived arm contracts): every key the
emitter knows for that table, each value as data. -/
structure DeclRow (S : Type) where
  table : Table
  name : S
  fields : List (S × Datum)
  deriving Repr

/-- The registry: the world tables, in declaration order. -/
structure Registry (S : Type) where
  machines : List (MachineDecl S)
  columns : List (ColumnsDecl S)
  coreChildren : List (CoreChildDecl S)
  squares : List (SquareRow S)
  costs : List (CostDecl S)
  waits : List (WaitDecl S)
  rows : List (DeclRow S)
  deriving Repr

variable {S : Type} [DecidableEq S]

def MachineDecl.columnNames (m : MachineDecl S) : List S := m.columns.map Column.name

/-- Recorded-row consistency, the part of `defmachine`'s guard (`machines.lisp`, `defmachine`) the
row can express: non-empty distinct states with at most 256 tags; continuation keys equal the
states in order; distinct observation, column and initialisation keys; initialisation keys name
columns; the first column is an enum whose tags equal the states; the table is the columns less
the directory's three (P1); the case catalogue is one `:run` per state and one `:observe` per
observed event, in order. It does not check symbol classes or the common columns. -/
abbrev MachineDecl.WF (m : MachineDecl S) (run observe : S) (directory : List S) : Prop :=
  m.states ≠ [] ∧ m.states.Nodup ∧ m.states.length ≤ 256 ∧
  m.continuations.map Prod.fst = m.states ∧
  (m.observes.map Prod.fst).Nodup ∧
  m.columnNames.Nodup ∧
  (m.initial.map Prod.fst).Nodup ∧
  (∀ x ∈ m.initial.map Prod.fst, x ∈ m.columnNames) ∧
  (m.columns.head?.bind fun c => c.kind.tags?) = some m.states ∧
  m.table = m.columns.filter (fun c => c.name ∉ directory) ∧
  m.cases = m.states.map (fun p => (run, m.name, p)) ++ m.observes.map (fun o => (observe, m.name, o.1))

def Registry.ids (r : Registry S) : List (DeclId S) :=
  r.machines.map (fun m => ⟨.machine, m.name⟩) ++
  r.columns.map (fun c => ⟨.columns, c.name⟩) ++
  r.coreChildren.map (fun c => ⟨.coreChild, c.field⟩) ++
  r.squares.map (fun o => ⟨.square, o.name⟩) ++
  r.costs.map (fun o => ⟨.cost, o.fn⟩) ++
  r.waits.map (fun o => ⟨.wait, o.name⟩) ++
  r.rows.map (fun o => ⟨o.table, o.name⟩)

def Registry.columnsNames (r : Registry S) : List S := r.columns.map ColumnsDecl.name

/-- What the registry promises across rows (DSL-METATHEORY §2.2-2.3): qualified identities are
unique; `defmachine NAME` emitted `defcolumns NAME` with the machine's table (P1: the directory's
fields are not its columns); every core child's stobj has its columns row. -/
abbrev Registry.WF (r : Registry S) (run observe : S) (directory : List S) : Prop :=
  r.ids.Nodup ∧
  (∀ m ∈ r.machines, m.WF run observe directory) ∧
  (∀ m ∈ r.machines, ∃ c ∈ r.columns, c.name = m.name ∧ c.columns = m.table) ∧
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

/-- The machine's case catalogue as labels: one per continuation phase, one per observed event (the
row's `:cases` is checked equal to this by `MachineDecl.WF`). -/
def MachineDecl.caseLabels (m : MachineDecl S) : List (CaseLabel S) :=
  m.continuations.map (fun p => .phase m.name p.1) ++
  m.observes.map (fun o => .event m.name o.1)

def Registry.machineCases (r : Registry S) : List (CaseLabel S) :=
  r.machines.flatMap MachineDecl.caseLabels

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
