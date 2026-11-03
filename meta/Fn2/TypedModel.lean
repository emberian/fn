/-
  Fn2.TypedModel — PW4 Typed `BitVec w` Column & Operation Refinement

  Formalizes the PW4 typed state and operation layer from `docs/design/LEAN-METATHEORY.md`
  (§9.2 PW4 & §9.5 item 3):
  - `ColSpec` and `TableSchema`: typed column specifications using `ColKind.width`.
  - `TypedCell c := BitVec c.width`, `TypedCol c := List (TypedCell c)`, and
    heterogeneous column list `TypedCols cols` stored inside `TypedTable t`.
  - Abstraction function `α : TypedTable t → Val` encoding the typed table into the
    ACL2 list-stobj layout `(rows (col₀ ...) (col₁ ...) ...)`.
  - Representation invariant `Inv : TypedTable t → Prop` and ACL2 `Val`-level
    well-formedness predicate `TableWfp : TableSchema S → Val → Prop`, with
    `inv_implies_tableWfp : Inv s → TableWfp t (α s)`.
  - Typed primitive operations (`readCell`, `writeCell`, `updateRow`, `appendRow`,
    and machine step `F_typed`) and their `Val`-level counterparts (`valReadCell`,
    `valWriteCell`, `valUpdateRow`, `valAppendRow`, `F_val`).
  - PW4 Refinement Theorems (`pw4_table_refinement`, `pw4_op_refinement`):
    `Inv s ∧ InputOK s i →
      Inv s' ∧ α s' = s'_val ∧ ResultRelated (F_typed s i) (F_val (α s) (encode i))`
  - Positive satisfiable witness (`pw4_scribe_witness_satisfiable`) on `scribeTable`
    (`:u60` deadline column writing `2^40` and `:u32` sequence column).
  - Negative narrowed-width tooth (`pw4_deadline_u32_breaks_refinement`): narrowing
    the `:u60` deadline column to `:u32` (`BitVec 32`) while writing a legal `:u60`
    value `2^40` truncates `mod 2^32 = 0` and falsifies refinement.
-/

import Fn2.Decl
import Fn2.ACL2.Val

namespace Fn2.TypedModel

open Fn2.ACL2
open Fn2.Decl

/-- Embed a natural number as an ACL2 integer `Val`. -/
@[match_pattern] abbrev _root_.Fn2.ACL2.Val.nat (n : Nat) : Val :=
  .int (Int.ofNat n)

/-! ## 1. Column & Table Schemas and Typed `BitVec w` Representation -/

/-- A single column specification: column name and typed `ColKind`. -/
structure ColSpec (S : Type) where
  name : String
  kind : ColKind S
  deriving Repr, DecidableEq

/-- A table schema: table name, maximum capacity `maxRows`, and column specs. -/
structure TableSchema (S : Type) where
  name    : String
  maxRows : Nat
  cols    : List (ColSpec S)
  deriving Repr, DecidableEq

/-- A typed cell in column `c` is a machine word `BitVec c.width`. -/
abbrev TypedCell {S : Type} (c : ColKind S) : Type :=
  BitVec c.width

/-- A typed column is a list of `BitVec c.width` cells (one per allocated row). -/
abbrev TypedCol {S : Type} (c : ColKind S) : Type :=
  List (TypedCell c)

/-- Heterogeneous column store indexed by the schema's `List (ColSpec S)`. -/
inductive TypedCols {S : Type} : List (ColSpec S) → Type where
  | nil  : TypedCols []
  | cons : {c : ColSpec S} → {cs : List (ColSpec S)} →
           TypedCol c.kind → TypedCols cs → TypedCols (c :: cs)

/-- A typed table for schema `t : TableSchema S`: active `rows`, capacity `maxRows`,
    and heterogeneous `BitVec w` columns. -/
structure TypedTable {S : Type} (t : TableSchema S) where
  rows    : Nat
  maxRows : Nat
  cols    : TypedCols t.cols

/-! ## 2. Abstraction Function `α : TypedTable t → Val` and Invariants -/

/-- Encode a single `BitVec w` column as an ACL2 proper list of natural-number `Val`s. -/
def colToVal {w : Nat} : List (BitVec w) → Val
  | []      => .nil
  | x :: xs => .cons (.nat x.toNat) (colToVal xs)

/-- Encode all columns in `TypedCols` as an ACL2 proper list of column lists. -/
def colsToVal {S : Type} : {cs : List (ColSpec S)} → TypedCols cs → Val
  | [],      .nil          => .nil
  | _ :: _,  .cons col rest => .cons (colToVal col) (colsToVal rest)

/-- Abstraction function `α`: maps a typed table to its ACL2 list-stobj `Val`
    representation `(rows (col₀ ...) (col₁ ...) ...)`. -/
def α {S : Type} {t : TableSchema S} (s : TypedTable t) : Val :=
  .cons (.nat s.rows) (colsToVal s.cols)

/-- Well-formedness predicate for a single encoded column in the `Val` model:
    a proper list of length `rows` whose elements are non-negative integers `< 2^w`. -/
def ColWfp (w : Nat) : Nat → Val → Prop
  | 0,     v => v = .nil
  | n + 1, v => ∃ (k : Nat) (rest : Val),
      k < 2 ^ w ∧ v = .cons (.nat k) rest ∧ ColWfp w n rest

/-- Well-formedness predicate for encoded columns matching `cs : List (ColSpec S)`. -/
def ColsWfp {S : Type} (rows : Nat) : List (ColSpec S) → Val → Prop
  | [],      v => v = .nil
  | c :: cs, v => ∃ (colVal rest : Val),
      v = .cons colVal rest ∧
      ColWfp c.kind.width rows colVal ∧
      ColsWfp rows cs rest

/-- ACL2 `Val`-level table well-formedness predicate (`table-wfp` in the untyped model). -/
def TableWfp {S : Type} (t : TableSchema S) (v : Val) : Prop :=
  ∃ (rows : Nat) (colsVal : Val),
    rows ≤ t.maxRows ∧
    v = .cons (.nat rows) colsVal ∧
    ColsWfp rows t.cols colsVal

/-- Every column in `TypedCols` has exact length `rows`. -/
@[reducible] def ColsLengthInv {S : Type} (rows : Nat) : {cs : List (ColSpec S)} → TypedCols cs → Prop
  | [],      .nil          => True
  | _ :: _,  .cons col rest => col.length = rows ∧ ColsLengthInv rows rest

/-- Representation invariant `Inv` on `TypedTable t`. -/
@[reducible] def Inv {S : Type} {t : TableSchema S} (s : TypedTable t) : Prop :=
  s.maxRows = t.maxRows ∧
  s.rows ≤ s.maxRows ∧
  ColsLengthInv s.rows s.cols

theorem colToVal_wfp {w : Nat} (col : List (BitVec w)) :
    ColWfp w col.length (colToVal col) := by
  induction col with
  | nil =>
      simp [ColWfp, colToVal]
  | cons x xs ih =>
      refine ⟨x.toNat, colToVal xs, x.isLt, rfl, ih⟩

theorem colsToVal_wfp {S : Type} {cs : List (ColSpec S)} (rows : Nat)
    (cols : TypedCols cs) (hLen : ColsLengthInv rows cols) :
    ColsWfp rows cs (colsToVal cols) := by
  induction cols with
  | nil =>
      simp [ColsWfp, colsToVal]
  | cons col rest ih =>
      rcases hLen with ⟨hColLen, hRestLen⟩
      refine ⟨colToVal col, colsToVal rest, rfl, ?_, ih hRestLen⟩
      rw [← hColLen]
      exact colToVal_wfp col

/-- `Inv s` implies that the abstracted ACL2 value `α s` satisfies `TableWfp t (α s)`. -/
theorem inv_implies_tableWfp {S : Type} {t : TableSchema S} {s : TypedTable t}
    (hInv : Inv s) :
    TableWfp t (α s) := by
  rcases hInv with ⟨hMax, hRows, hCols⟩
  refine ⟨s.rows, colsToVal s.cols, by omega, rfl, colsToVal_wfp s.rows s.cols hCols⟩

/-! ## 3. Typed and Untyped Column Read / Write / Row Operations -/

/-- Read a cell from a single `BitVec w` column at row `slot` (defaulting to `0#w`). -/
def colRead {w : Nat} : List (BitVec w) → Nat → BitVec w
  | [],      _     => 0#w
  | x :: _,  0     => x
  | _ :: xs, n + 1 => colRead xs n

/-- Read a cell from an encoded `Val` column at row `slot` (defaulting to `.nat 0`). -/
def valColRead : Val → Nat → Val
  | .cons x _,  0     => x
  | .cons _ xs, n + 1 => valColRead xs n
  | _,          _     => .nat 0

theorem colRead_refines {w : Nat} (col : List (BitVec w)) (slot : Nat) :
    Val.nat (colRead col slot).toNat = valColRead (colToVal col) slot := by
  induction col generalizing slot with
  | nil => rfl
  | cons x xs ih =>
      cases slot with
      | zero => rfl
      | succ n => exact ih n

/-- Read column `colIdx` at row `slot` from `TypedCols`, returning `Val.nat bv.toNat`. -/
def colsRead {S : Type} : {cs : List (ColSpec S)} → TypedCols cs → Nat → Nat → Val
  | [],      .nil,           _,      _    => .nat 0
  | _ :: _,  .cons col _,    0,      slot => .nat (colRead col slot).toNat
  | _ :: _,  .cons _ rest,   ci + 1, slot => colsRead rest ci slot

/-- Read column `colIdx` at row `slot` from an encoded `Val` column list. -/
def valColsRead : Val → Nat → Nat → Val
  | .cons colVal _, 0,      slot => valColRead colVal slot
  | .cons _ rest,   ci + 1, slot => valColsRead rest ci slot
  | _,              _,      _    => .nat 0

/-- Typed table cell read (`readCell`). -/
def readCell {S : Type} {t : TableSchema S} (s : TypedTable t) (colIdx slot : Nat) : Val :=
  colsRead s.cols colIdx slot

/-- Untyped `Val`-level table cell read (`valReadCell`). -/
def valReadCell (v : Val) (colIdx slot : Nat) : Val :=
  match v with
  | .cons _ colsVal => valColsRead colsVal colIdx slot
  | _               => .nat 0

theorem colsRead_refines {S : Type} {cs : List (ColSpec S)}
    (cols : TypedCols cs) (colIdx slot : Nat) :
    colsRead cols colIdx slot = valColsRead (colsToVal cols) colIdx slot := by
  induction cols generalizing colIdx with
  | nil => rfl
  | cons col rest ih =>
      cases colIdx with
      | zero =>
          simp [colsRead, colsToVal, valColsRead, colRead_refines]
      | succ ci =>
          simp [colsRead, colsToVal, valColsRead, ih ci]

/-- Reading any cell from the typed table refines `valReadCell` on `α s`. -/
theorem readCell_refines {S : Type} {t : TableSchema S}
    (s : TypedTable t) (colIdx slot : Nat) :
    readCell s colIdx slot = valReadCell (α s) colIdx slot := by
  simp [readCell, valReadCell, α, colsRead_refines]

/-- Write a `BitVec w` cell at row `slot` in a single column. -/
def colWrite {w : Nat} : List (BitVec w) → Nat → BitVec w → List (BitVec w)
  | [],      _,     _ => []
  | _ :: xs, 0,     v => v :: xs
  | x :: xs, n + 1, v => x :: colWrite xs n v

/-- Write a `Val` cell at row `slot` in an encoded `Val` column. -/
def valColWrite : Val → Nat → Val → Val
  | .cons _ xs, 0,     v => .cons v xs
  | .cons x xs, n + 1, v => .cons x (valColWrite xs n v)
  | v,          _,     _ => v

theorem colWrite_length {w : Nat} (col : List (BitVec w)) (slot : Nat) (v : BitVec w) :
    (colWrite col slot v).length = col.length := by
  induction col generalizing slot with
  | nil => rfl
  | cons x xs ih =>
      cases slot with
      | zero => rfl
      | succ n => simp [colWrite, ih n]

theorem colToVal_colWrite {w : Nat} (col : List (BitVec w)) (slot : Nat) (v : BitVec w) :
    colToVal (colWrite col slot v) = valColWrite (colToVal col) slot (.nat v.toNat) := by
  induction col generalizing slot with
  | nil =>
      rfl
  | cons x xs ih =>
      cases slot with
      | zero => rfl
      | succ n =>
          simp [colWrite, colToVal, valColWrite, ih n]

/-- Write raw natural value `rawVal` (truncated via `BitVec.ofNat c.kind.width rawVal`)
    into column `colIdx` at row `slot`. -/
def colsWrite {S : Type} : {cs : List (ColSpec S)} → TypedCols cs → Nat → Nat → Nat → TypedCols cs
  | [],      .nil,          _,      _,    _      => .nil
  | c :: _,  .cons col rest, 0,     slot, rawVal =>
      .cons (colWrite col slot (BitVec.ofNat c.kind.width rawVal)) rest
  | _ :: _,  .cons col rest, ci + 1, slot, rawVal =>
      .cons col (colsWrite rest ci slot rawVal)

/-- Write `.nat rawVal` into column `colIdx` at row `slot` in the `Val` column list. -/
def valColsWrite : Val → Nat → Nat → Val → Val
  | .cons colVal rest, 0,      slot, v => .cons (valColWrite colVal slot v) rest
  | .cons colVal rest, ci + 1, slot, v => .cons colVal (valColsWrite rest ci slot v)
  | v,                 _,      _,    _ => v

/-- Typed table cell write (`writeCell`). -/
def writeCell {S : Type} {t : TableSchema S}
    (s : TypedTable t) (colIdx slot rawVal : Nat) : TypedTable t :=
  { s with cols := colsWrite s.cols colIdx slot rawVal }

/-- Untyped `Val`-level table cell write (`valWriteCell`). -/
def valWriteCell (v : Val) (colIdx slot : Nat) (cellVal : Val) : Val :=
  match v with
  | .cons rowsVal colsVal => .cons rowsVal (valColsWrite colsVal colIdx slot cellVal)
  | _                     => v

/-- Predicate asserting that writing `rawVal` to `colIdx` obeys the column's bit-width bound. -/
@[reducible] def ColWriteOK {S : Type} : List (ColSpec S) → Nat → Nat → Prop
  | [],      _,      _      => False
  | c :: _,  0,      rawVal => rawVal < 2 ^ c.kind.width
  | _ :: cs, ci + 1, rawVal => ColWriteOK cs ci rawVal

/-- Predicate asserting a single cell write `(colIdx, rawVal)` at `slot` is within bounds. -/
@[reducible] def WriteOK {S : Type} (t : TableSchema S) (rows slot colIdx rawVal : Nat) : Prop :=
  slot < rows ∧ ColWriteOK t.cols colIdx rawVal

theorem colsWrite_lengthInv {S : Type} {cs : List (ColSpec S)}
    (rows : Nat) (cols : TypedCols cs) (colIdx slot rawVal : Nat)
    (hLen : ColsLengthInv rows cols) :
    ColsLengthInv rows (colsWrite cols colIdx slot rawVal) := by
  induction cols generalizing colIdx with
  | nil =>
       trivial
  | cons col rest ih =>
      rcases hLen with ⟨hCol, hRest⟩
      cases colIdx with
      | zero =>
          exact ⟨(colWrite_length col slot _).trans hCol, hRest⟩
      | succ ci =>
          exact ⟨hCol, ih ci hRest⟩

theorem colsWrite_refines {S : Type} {cs : List (ColSpec S)}
    (cols : TypedCols cs) (colIdx slot rawVal : Nat)
    (hOK : ColWriteOK cs colIdx rawVal) :
    colsToVal (colsWrite cols colIdx slot rawVal) =
      valColsWrite (colsToVal cols) colIdx slot (.nat rawVal) := by
  induction cols generalizing colIdx with
  | nil =>
      cases hOK
  | @cons c cs' col rest ih =>
      cases colIdx with
      | zero =>
          have hLt : rawVal < 2 ^ c.kind.width := hOK
          have hToNat : (BitVec.ofNat c.kind.width rawVal).toNat = rawVal := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt]
          simp [colsWrite, colsToVal, valColsWrite, colToVal_colWrite, hToNat]
      | succ ci =>
          simp [colsWrite, colsToVal, valColsWrite, ih ci hOK]

/-- `writeCell` preserves `Inv` and commutes with `α` whenever `WriteOK` holds. -/
theorem writeCell_refines {S : Type} {t : TableSchema S}
    (s : TypedTable t) (colIdx slot rawVal : Nat)
    (hInv : Inv s) (hOK : WriteOK t s.rows slot colIdx rawVal) :
    Inv (writeCell s colIdx slot rawVal) ∧
    α (writeCell s colIdx slot rawVal) = valWriteCell (α s) colIdx slot (.nat rawVal) := by
  rcases hInv with ⟨hMax, hRows, hCols⟩
  rcases hOK with ⟨_, hColOK⟩
  refine ⟨⟨hMax, hRows, colsWrite_lengthInv s.rows s.cols colIdx slot rawVal hCols⟩, ?_⟩
  simp [writeCell, valWriteCell, α, colsWrite_refines s.cols colIdx slot rawVal hColOK]

/-- Update multiple `(colIdx, rawVal)` pairs at row `slot` in a `TypedTable`. -/
def updateRow {S : Type} {t : TableSchema S}
    (s : TypedTable t) (slot : Nat) : List (Nat × Nat) → TypedTable t
  | []                  => s
  | (ci, rv) :: updates => updateRow (writeCell s ci slot rv) slot updates

/-- Update multiple `(colIdx, Val)` pairs at row `slot` in an encoded `Val` table. -/
def valUpdateRow (v : Val) (slot : Nat) : List (Nat × Val) → Val
  | []                  => v
  | (ci, cv) :: updates => valUpdateRow (valWriteCell v ci slot cv) slot updates

/-- Encode a list of `(colIdx, rawVal)` writes as `List (Nat × Val)`. -/
def encodeWrites (writes : List (Nat × Nat)) : List (Nat × Val) :=
  writes.map (fun (ci, rv) => (ci, .nat rv))

/-- All writes in a batch satisfy `WriteOK`. -/
@[reducible] def WritesOK {S : Type} (t : TableSchema S) (rows slot : Nat) : List (Nat × Nat) → Prop
  | []                  => True
  | (ci, rv) :: updates => WriteOK t rows slot ci rv ∧ WritesOK t rows slot updates

theorem updateRow_refines {S : Type} {t : TableSchema S}
    (s : TypedTable t) (slot : Nat) (writes : List (Nat × Nat))
    (hInv : Inv s) (hOK : WritesOK t s.rows slot writes) :
    Inv (updateRow s slot writes) ∧
    α (updateRow s slot writes) = valUpdateRow (α s) slot (encodeWrites writes) := by
  induction writes generalizing s with
  | nil =>
      exact ⟨hInv, rfl⟩
  | cons w ws ih =>
      rcases w with ⟨ci, rv⟩
      rcases hOK with ⟨hHead, hTail⟩
      have ⟨hInv', hAlpha'⟩ := writeCell_refines s ci slot rv hInv hHead
      have ⟨hInvFinal, hAlphaFinal⟩ := ih (writeCell s ci slot rv) hInv' hTail
      refine ⟨hInvFinal, ?_⟩
      simpa [updateRow, valUpdateRow, encodeWrites, hAlpha'] using hAlphaFinal

/-- Extract a natural number from `Val.nat n` (`.int (Int.ofNat n)`). -/
def valToNat : Val → Nat
  | .int (.ofNat n) => n
  | _               => 0

@[simp] theorem valToNat_nat (n : Nat) : valToNat (.nat n) = n := rfl

/-- Append a single cell to a `Val`-encoded column proper list. -/
def valColAppend : Val → Val → Val
  | .cons x xs, v => .cons x (valColAppend xs v)
  | _,          v => .cons v .nil

theorem colToVal_append_singleton {w : Nat} (col : List (BitVec w)) (v : BitVec w) :
    colToVal (col ++ [v]) = valColAppend (colToVal col) (.nat v.toNat) := by
  induction col with
  | nil => rfl
  | cons x xs ih => simp [colToVal, valColAppend, ih]

/-- Append one new cell to every column in `TypedCols` from `vals : List Nat`. -/
def colsAppend {S : Type} : {cs : List (ColSpec S)} → TypedCols cs → List Nat → TypedCols cs
  | [],      .nil,           _    => .nil
  | c :: _,  .cons col rest, vals =>
      .cons (col ++ [BitVec.ofNat c.kind.width (vals.headD 0)]) (colsAppend rest vals.tail)

/-- Append one new cell to every column in a `Val`-encoded column list. -/
def valColsAppend : Val → List Val → Val
  | .cons colVal rest, v :: vs => .cons (valColAppend colVal v) (valColsAppend rest vs)
  | .cons colVal rest, []      => .cons (valColAppend colVal (.nat 0)) (valColsAppend rest [])
  | _,                 _       => .nil

/-- Typed row append (`appendRow`): increments `rows` and appends a cell to each column. -/
def appendRow {S : Type} {t : TableSchema S} (s : TypedTable t) (vals : List Nat) : TypedTable t :=
  { s with rows := s.rows + 1, cols := colsAppend s.cols vals }

/-- Untyped `Val`-level row append (`valAppendRow`). -/
def valAppendRow (v : Val) (vals : List Val) : Val :=
  match v with
  | .cons rowsVal colsVal => .cons (.nat (valToNat rowsVal + 1)) (valColsAppend colsVal vals)
  | _                     => v

/-- Validity predicate for column values in a newly appended row. -/
@[reducible] def RowValsOK {S : Type} : List (ColSpec S) → List Nat → Prop
  | [],      []        => True
  | c :: cs, rv :: rvs => rv < 2 ^ c.kind.width ∧ RowValsOK cs rvs
  | _,       _         => False

/-- Validity predicate for `appendRow`: capacity remains within `maxRows` and each column value
    fits in its declared bit-width. -/
@[reducible] def AppendOK {S : Type} (t : TableSchema S) (s : TypedTable t) (vals : List Nat) : Prop :=
  s.rows < s.maxRows ∧ RowValsOK t.cols vals

theorem colsAppend_lengthInv {S : Type} {cs : List (ColSpec S)}
    (rows : Nat) (cols : TypedCols cs) (vals : List Nat)
    (hLen : ColsLengthInv rows cols) :
    ColsLengthInv (rows + 1) (colsAppend cols vals) := by
  induction cols generalizing vals with
  | nil => trivial
  | cons col rest ih =>
      rcases hLen with ⟨hCol, hRest⟩
      refine ⟨?_, ih vals.tail hRest⟩
      simp [hCol]

theorem colsAppend_refines {S : Type} {cs : List (ColSpec S)}
    (cols : TypedCols cs) (vals : List Nat)
    (hOK : RowValsOK cs vals) :
    colsToVal (colsAppend cols vals) = valColsAppend (colsToVal cols) (vals.map Val.nat) := by
  induction cols generalizing vals with
  | nil =>
      cases vals with
      | nil => rfl
      | cons _ _ => cases hOK
  | @cons c cs' col rest ih =>
      cases vals with
      | nil => cases hOK
      | cons rv rvs =>
          rcases hOK with ⟨hLt, hRestOK⟩
          have hToNat : (BitVec.ofNat c.kind.width rv).toNat = rv := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt]
          simp [colsAppend, colsToVal, valColsAppend, colToVal_append_singleton, hToNat, ih rvs hRestOK]

/-- `appendRow` preserves `Inv` and commutes with `α` whenever `AppendOK` holds. -/
theorem appendRow_refines {S : Type} {t : TableSchema S}
    (s : TypedTable t) (vals : List Nat)
    (hInv : Inv s) (hOK : AppendOK t s vals) :
    Inv (appendRow s vals) ∧
    α (appendRow s vals) = valAppendRow (α s) (vals.map Val.nat) := by
  rcases hInv with ⟨hMax, _, hCols⟩
  rcases hOK with ⟨hCap, hVals⟩
  refine ⟨⟨hMax, Nat.succ_le_of_lt hCap, colsAppend_lengthInv s.rows s.cols vals hCols⟩, ?_⟩
  simp [appendRow, valAppendRow, α, colsAppend_refines s.cols vals hVals]

/-! ## 4. PW4 Machine Step Operation (`F_typed` vs `F_val`) and Refinement Theorem -/

/-- Resource charge vector emitted by a step operation. -/
structure Charges where
  bytes : Nat
  slots : Nat
  deriving Repr, DecidableEq

/-- Child operation descriptor emitted by a step operation. -/
structure ChildOp where
  childKind : String
  childSlot : Nat
  arg       : Nat
  deriving Repr, DecidableEq

/-- Typed input to a table-backed step operation:
    target `slot`, a batch of `(colIdx, rawVal)` writes, a list of `readCols` to
    return after updating, resource `charges`, optional `stopReason`, and `childOps`. -/
structure OpInput where
  slot       : Nat
  writes     : List (Nat × Nat)
  readCols   : List Nat
  charges    : Charges
  stopReason : Option Nat
  childOps   : List ChildOp
  deriving Repr, DecidableEq

/-- Result tuple of a typed operation:
    `(updatedTable, returnVals, charges, stopReason, childOps)`. -/
abbrev TypedResult {S : Type} (t : TableSchema S) : Type :=
  TypedTable t × List Val × Charges × Option Nat × List ChildOp

/-- Result tuple of an untyped `Val` operation:
    `(updatedValTable, returnVals, charges, stopReason, childOps)`. -/
abbrev ValResult : Type :=
  Val × List Val × Charges × Option Nat × List ChildOp

/-- Encode a write batch as an ACL2 proper list of `(colIdx . rawVal)` pairs. -/
def encodeWritesVal : List (Nat × Nat) → Val
  | []             => .nil
  | (ci, rv) :: ws => .cons (.cons (.nat ci) (.nat rv)) (encodeWritesVal ws)

/-- Decode a `Val` write batch into `List (Nat × Val)`. -/
def decodeWritesVal : Val → List (Nat × Val)
  | .cons (.cons ci cv) rest => (valToNat ci, cv) :: decodeWritesVal rest
  | _                        => []

@[simp] theorem decodeWritesVal_encodeWritesVal (ws : List (Nat × Nat)) :
    decodeWritesVal (encodeWritesVal ws) = encodeWrites ws := by
  induction ws with
  | nil => rfl
  | cons w rest ih =>
      rcases w with ⟨ci, rv⟩
      simp [encodeWritesVal, decodeWritesVal, encodeWrites, ih]

/-- Encode a list of read column indices as an ACL2 proper list of naturals. -/
def encodeReadColsVal : List Nat → Val
  | []        => .nil
  | ci :: cis => .cons (.nat ci) (encodeReadColsVal cis)

/-- Decode an ACL2 proper list of column indices. -/
def decodeReadColsVal : Val → List Nat
  | .cons ci rest => valToNat ci :: decodeReadColsVal rest
  | _             => []

@[simp] theorem decodeReadColsVal_encodeReadColsVal (cis : List Nat) :
    decodeReadColsVal (encodeReadColsVal cis) = cis := by
  induction cis with
  | nil => rfl
  | cons ci rest ih => simp [encodeReadColsVal, decodeReadColsVal, ih]

/-- Encode a `Charges` struct as a `Val` pair `(bytes . slots)`. -/
def Charges.toVal (c : Charges) : Val :=
  .cons (.nat c.bytes) (.nat c.slots)

/-- Decode a `Val` pair `(bytes . slots)` into `Charges`. -/
def decodeChargesVal : Val → Charges
  | .cons b s => { bytes := valToNat b, slots := valToNat s }
  | _         => { bytes := 0, slots := 0 }

@[simp] theorem decodeChargesVal_toVal (c : Charges) :
    decodeChargesVal c.toVal = c := by
  cases c; rfl

/-- Encode an `Option Nat` stop reason as a `Val`. -/
def encodeStopReason : Option Nat → Val
  | none   => .nil
  | some r => .cons (.nat r) .nil

/-- Decode an `Option Nat` stop reason from a `Val`. -/
def decodeStopReasonVal : Val → Option Nat
  | .cons r _ => some (valToNat r)
  | _         => none

@[simp] theorem decodeStopReasonVal_encode (sr : Option Nat) :
    decodeStopReasonVal (encodeStopReason sr) = sr := by
  cases sr <;> rfl

/-- Encode a `ChildOp` as a `Val` triple `(childKind childSlot . arg)`. -/
def ChildOp.toVal (op : ChildOp) : Val :=
  .cons (.str op.childKind) (.cons (.nat op.childSlot) (.nat op.arg))

/-- Encode a list of `ChildOp`s as an ACL2 proper list. -/
def encodeChildOpsVal : List ChildOp → Val
  | []        => .nil
  | op :: ops => .cons op.toVal (encodeChildOpsVal ops)

/-- Decode an ACL2 proper list of `ChildOp`s. -/
def decodeChildOpsVal : Val → List ChildOp
  | .cons (.cons (.str k) (.cons cs arg)) rest =>
      { childKind := k, childSlot := valToNat cs, arg := valToNat arg } :: decodeChildOpsVal rest
  | _ => []

@[simp] theorem decodeChildOpsVal_encode (ops : List ChildOp) :
    decodeChildOpsVal (encodeChildOpsVal ops) = ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      cases op
      simp [encodeChildOpsVal, ChildOp.toVal, decodeChildOpsVal, ih]

/-- Encode a typed `OpInput` into a pure ACL2 `Val` 6-element list:
    `(slot writes readCols charges stopReason childOps)`. -/
def encode (i : OpInput) : Val :=
  .cons (.nat i.slot)
    (.cons (encodeWritesVal i.writes)
      (.cons (encodeReadColsVal i.readCols)
        (.cons i.charges.toVal
          (.cons (encodeStopReason i.stopReason)
            (.cons (encodeChildOpsVal i.childOps) .nil)))))

/-- Input validity predicate `InputOK`: row `slot` is active (when writing) and every
    column write in `i.writes` satisfies the schema's bit-width bound `WriteOK`. -/
@[reducible] def InputOK {S : Type} {t : TableSchema S} (s : TypedTable t) (i : OpInput) : Prop :=
  WritesOK t s.rows i.slot i.writes

/-- Execute a typed step operation `F_typed` (`TypedOp`) on `TypedTable t`. -/
def F_typed {S : Type} {t : TableSchema S} (s : TypedTable t) (i : OpInput) : TypedResult t :=
  let s' := updateRow s i.slot i.writes
  let rets := i.readCols.map (fun ci => readCell s' ci i.slot)
  (s', rets, i.charges, i.stopReason, i.childOps)

/-- Execute the corresponding `Val`-level step operation `F_val` (`ValOp`) on an encoded
    table `v` and an encoded ACL2 `Val` input `iv`. -/
def F_val (v : Val) (iv : Val) : ValResult :=
  match iv with
  | .cons slotV (.cons writesV (.cons readColsV (.cons chargesV (.cons stopV (.cons childOpsV _))))) =>
      let slot := valToNat slotV
      let v' := valUpdateRow v slot (decodeWritesVal writesV)
      let rets := (decodeReadColsVal readColsV).map (fun ci => valReadCell v' ci slot)
      (v', rets, decodeChargesVal chargesV, decodeStopReasonVal stopV, decodeChildOpsVal childOpsV)
  | _ => (v, [], { bytes := 0, slots := 0 }, none, [])

abbrev TypedOp := @F_typed
abbrev ValOp := F_val

/-- Refinement relation `ResultRelated` between `TypedResult t` and `ValResult`:
    the updated table abstracts via `α` to the updated `Val` table, and all return values,
    charges, stop reasons, and child operations agree identically. -/
@[reducible] def ResultRelated {S : Type} {t : TableSchema S}
    (resT : TypedResult t) (resV : ValResult) : Prop :=
  α resT.1 = resV.1 ∧
  resT.2.1 = resV.2.1 ∧
  resT.2.2.1 = resV.2.2.1 ∧
  resT.2.2.2.1 = resV.2.2.2.1 ∧
  resT.2.2.2.2 = resV.2.2.2.2

/-- **PW4 Operation Refinement Theorem (`pw4_op_refinement`)**:
    For any typed table `s` satisfying `Inv s` and any input `i` satisfying `InputOK s i`,
    stepping via `F_typed` preserves `Inv`, commutes with `α`, preserves `TableWfp` on
    `α s'`, and satisfies `ResultRelated (F_typed s i) (F_val (α s) (encode i))`. -/
theorem pw4_op_refinement {S : Type} {t : TableSchema S}
    (s : TypedTable t) (i : OpInput)
    (h : Inv s ∧ InputOK s i) :
    let resT := F_typed s i
    let resV := F_val (α s) (encode i)
    Inv resT.1 ∧
    α resT.1 = resV.1 ∧
    TableWfp t (α resT.1) ∧
    ResultRelated resT resV := by
  rcases h with ⟨hInv, hInput⟩
  simp only [F_typed, F_val, encode, valToNat_nat, decodeWritesVal_encodeWritesVal,
    decodeReadColsVal_encodeReadColsVal, decodeChargesVal_toVal,
    decodeStopReasonVal_encode, decodeChildOpsVal_encode]
  have ⟨hInv', hAlpha'⟩ := updateRow_refines s i.slot i.writes hInv hInput
  have hRets :
      List.map (fun ci => readCell (updateRow s i.slot i.writes) ci i.slot) i.readCols =
      List.map (fun ci => valReadCell (valUpdateRow (α s) i.slot (encodeWrites i.writes)) ci i.slot) i.readCols := by
    apply List.map_congr_left
    intro ci _
    rw [readCell_refines, hAlpha']
  refine ⟨hInv', hAlpha', inv_implies_tableWfp hInv', ?_⟩
  exact ⟨hAlpha', hRets, rfl, rfl, rfl⟩

/-- **PW4 Table Refinement Theorem (`pw4_table_refinement`)**:
    Direct formulation matching `docs/design/LEAN-METATHEORY.md` §9.2 PW4. -/
theorem pw4_table_refinement {S : Type} {t : TableSchema S}
    (s : TypedTable t) (i : OpInput) :
    Inv s ∧ InputOK s i →
      Inv (F_typed s i).1 ∧
      α (F_typed s i).1 = (F_val (α s) (encode i)).1 ∧
      ResultRelated (F_typed s i) (F_val (α s) (encode i)) := by
  intro h
  have ⟨hInv', hAlpha', _, hRel⟩ := pw4_op_refinement s i h
  exact ⟨hInv', hAlpha', hRel⟩

/-! ## 5. Positive Witness (`pw4_scribe_witness_satisfiable`) -/

/-- Representative `scribeTable` schema with a `:u60` deadline column (col 0)
    and a `:u32` sequence column (col 1). -/
def scribeTable : TableSchema String where
  name    := "scribe"
  maxRows := 4
  cols    := [
    { name := "deadline", kind := .u60 },
    { name := "seq",      kind := .u32 }
  ]

/-- Concrete 2-row `TypedTable scribeTable` instance. -/
def scribeInitTable : TypedTable scribeTable where
  rows    := 2
  maxRows := 4
  cols    := .cons [BitVec.ofNat 60 100, BitVec.ofNat 60 200]
              (.cons [BitVec.ofNat 32 1, BitVec.ofNat 32 2] .nil)

/-- Concrete legal `OpInput` writing `2^40` (requires > 32 bits, legal in `:u60`)
    into column 0 (`deadline`) and `42` into column 1 (`seq`) at row 0, then reading both. -/
def scribeWitnessInput : OpInput where
  slot       := 0
  writes     := [(0, 2 ^ 40), (1, 42)]
  readCols   := [0, 1]
  charges    := { bytes := 64, slots := 1 }
  stopReason := none
  childOps   := [{ childKind := "worker", childSlot := 0, arg := 7 }]

/-- **Positive Witness Theorem (`pw4_scribe_witness_satisfiable`)**:
    `scribeInitTable` and `scribeWitnessInput` satisfy `Inv` and `InputOK`, and stepping
    produces the exact `:u60` value `2^40` and `:u32` value `42` in both the typed
    `BitVec` model and the `Val` model. -/
theorem pw4_scribe_witness_satisfiable :
    Inv scribeInitTable ∧
    InputOK scribeInitTable scribeWitnessInput ∧
    Inv (F_typed scribeInitTable scribeWitnessInput).1 ∧
    ResultRelated
      (F_typed scribeInitTable scribeWitnessInput)
      (F_val (α scribeInitTable) (encode scribeWitnessInput)) ∧
    (F_typed scribeInitTable scribeWitnessInput).2.1 = [.nat (2 ^ 40), .nat 42] := by
  have hInv : Inv scribeInitTable := by
     refine ⟨rfl, by decide, rfl, rfl, trivial⟩
  have hOK : InputOK scribeInitTable scribeWitnessInput := by
    refine ⟨⟨by decide, show 2 ^ 40 < 2 ^ 60 by decide⟩,
            ⟨by decide, show 42 < 2 ^ 32 by decide⟩,
            trivial⟩
  have ⟨hInv', _, _, hRel⟩ := pw4_op_refinement scribeInitTable scribeWitnessInput ⟨hInv, hOK⟩
  refine ⟨hInv, hOK, hInv', hRel, ?_⟩
  decide

/-! ## 6. Negative Narrowed-Width Tooth (`pw4_deadline_u32_breaks_refinement`) -/

/-- Defective schema narrowing `deadline` from `:u60` to `:u32` (`BitVec 32`),
    modeling a codegen bug where a 60-bit deadline column is emitted as a 32-bit word. -/
def scribeTableNarrowedU32 : TableSchema String where
  name    := "scribe-narrowed-u32"
  maxRows := 4
  cols    := [
    { name := "deadline", kind := .u32 },
    { name := "seq",      kind := .u32 }
  ]

/-- Initial 2-row table under the narrowed `:u32` schema, with the same initial `α`
    encoding as `scribeInitTable`. -/
def scribeInitTableNarrowedU32 : TypedTable scribeTableNarrowedU32 where
  rows    := 2
  maxRows := 4
  cols    := .cons [BitVec.ofNat 32 100, BitVec.ofNat 32 200]
              (.cons [BitVec.ofNat 32 1, BitVec.ofNat 32 2] .nil)

/-- Initial abstractions of `scribeInitTable` and `scribeInitTableNarrowedU32` agree. -/
theorem scribeInit_alpha_eq :
    α scribeInitTableNarrowedU32 = α scribeInitTable := by
  decide

/-- **Negative Narrowed-Width Tooth (`pw4_deadline_u32_breaks_refinement`)**:
    Although `scribeWitnessInput` is a legal `:u60` deadline write (`InputOK scribeInitTable`),
    executing the same step on the narrowed `:u32` table (`BitVec 32` deadline column)
    truncates `2^40 mod 2^32 = 0`, causing both the table abstraction `α` and
    `ResultRelated` to diverge from the `Val` model (`0 ≠ 2^40`). -/
theorem pw4_deadline_u32_breaks_refinement :
    Inv scribeInitTableNarrowedU32 ∧
    InputOK scribeInitTable scribeWitnessInput ∧
    α scribeInitTableNarrowedU32 = α scribeInitTable ∧
    (F_typed scribeInitTableNarrowedU32 scribeWitnessInput).2.1 = [.nat 0, .nat 42] ∧
    (F_val (α scribeInitTableNarrowedU32) (encode scribeWitnessInput)).2.1 =
      [.nat (2 ^ 40), .nat 42] ∧
    α (F_typed scribeInitTableNarrowedU32 scribeWitnessInput).1 ≠
      (F_val (α scribeInitTableNarrowedU32) (encode scribeWitnessInput)).1 ∧
    ¬ ResultRelated
        (F_typed scribeInitTableNarrowedU32 scribeWitnessInput)
        (F_val (α scribeInitTableNarrowedU32) (encode scribeWitnessInput)) := by
  refine ⟨⟨rfl, by decide, rfl, rfl, trivial⟩,
          ⟨⟨by decide, show 2 ^ 40 < 2 ^ 60 by decide⟩,
           ⟨by decide, show 42 < 2 ^ 32 by decide⟩,
           trivial⟩,
          by decide,
          by decide,
          by decide,
          by decide,
          ?_⟩
  intro hRel
  have hAlphaEq := hRel.1
  revert hAlphaEq
  decide

end Fn2.TypedModel
