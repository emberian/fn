import Fn2.ACL2.Val

/-!
# Fn2.ACL2.Read: ACL2's printed objects as `Val`

A reader for what ACL2's printer writes with `*package*` `ACL2` (the recorder's lines): integers,
symbols (kept as printed, so `:OK`, `NIL`, `FN2-NONE`), strings, `#\` characters, proper and
dotted lists, and `'x` as `(QUOTE x)`. Anything else is an error, never a guess.
-/

namespace Fn2.ACL2.Read
open Fn2.ACL2

structure P where
  s : ByteArray
  i : Nat

def isDelim (c : UInt8) : Bool :=
  c == 32 || c == 10 || c == 13 || c == 9 || c == 40 || c == 41 || c == 34 || c == 39 || c == 59

partial def skipWs (p : P) : P :=
  if h : p.i < p.s.size then
    let c := p.s[p.i]
    if c == 32 || c == 10 || c == 13 || c == 9 then skipWs { p with i := p.i + 1 }
    else if c == 59 then
      let rec line (j : Nat) : Nat :=
        if h : j < p.s.size then (if p.s[j] == 10 then j else line (j + 1)) else j
      skipWs { p with i := line p.i }
    else p
  else p

def sub (p : P) (a b : Nat) : String :=
  String.fromUTF8! (p.s.extract a b)

def charNamed (n : String) : Option Char :=
  match n with
  | "Space" => some ' ' | "Newline" => some '\n' | "Tab" => some '\t' | "Page" => some '\x0c'
  | "Rubout" => some '\x7f' | "Return" => some '\r' | "Linefeed" => some '\n'
  | "Null" => some '\x00'
  | _ => if n.length == 1 then some (n.get 0) else none

def atomOf (t : String) : Val :=
  let digits (u : List Char) := !u.isEmpty && u.all Char.isDigit
  let cs := t.toList
  let num (u : List Char) : Nat := u.foldl (fun n c => 10 * n + (c.toNat - 48)) 0
  match cs with
  | '-' :: rest => if digits rest then .int (- (num rest : Int)) else .sym t
  | '+' :: rest => if digits rest then .int (num rest) else .sym t
  | _ => if digits cs then .int (num cs) else .sym t

partial def readVal (p : P) : Except String (Val × P) := do
  let p := skipWs p
  if h : p.i < p.s.size then
    let c := p.s[p.i]
    if c == 40 then readList { p with i := p.i + 1 } #[]
    else if c == 41 then throw s!"unexpected ) at {p.i}"
    else if c == 39 then
      let (v, p) ← readVal { p with i := p.i + 1 }
      pure (Val.ofList [.sym "QUOTE", v], p)
    else if c == 34 then
      let rec str (j : Nat) (acc : ByteArray) : Except String (ByteArray × Nat) :=
        if h : j < p.s.size then
          let d := p.s[j]
          if d == 34 then .ok (acc, j + 1)
          else if d == 92 then
            if h2 : j + 1 < p.s.size then str (j + 2) (acc.push p.s[j + 1]) else .error "eof in string"
          else str (j + 1) (acc.push d)
        else .error "eof in string"
      let (bs, j) ← str (p.i + 1) ByteArray.empty
      pure (.str (String.fromUTF8! bs), { p with i := j })
    else if c == 35 then
      -- #\c
      if h2 : p.i + 2 < p.s.size then
        let rec scanc (j : Nat) : Nat :=
          if h : j < p.s.size then (if isDelim p.s[j] then j else scanc (j + 1)) else j
        let j := max (scanc (p.i + 3)) (p.i + 3)
        match charNamed (sub p (p.i + 2) j) with
        | some ch => pure (.chr ch, { p with i := j })
        | none => throw s!"unknown character {sub p p.i j}"
      else throw "eof after #"
    else if c == 124 then
      -- |...|: a symbol printed with bars, kept as printed
      let rec bar (j : Nat) : Nat :=
        if h : j < p.s.size then (if p.s[j] == 124 then j + 1 else bar (j + 1)) else j
      let j := bar (p.i + 1)
      pure (.sym (sub p p.i j), { p with i := j })
    else
      let rec scan (j : Nat) : Nat :=
        if h : j < p.s.size then (if isDelim p.s[j] then j else scan (j + 1)) else j
      let j := scan p.i
      pure (atomOf (sub p p.i j), { p with i := j })
  else throw "eof"
where
  readList (p : P) (acc : Array Val) : Except String (Val × P) := do
    let p := skipWs p
    if h : p.i < p.s.size then
      let c := p.s[p.i]
      if c == 41 then pure (acc.foldr Val.cons Val.nil, { p with i := p.i + 1 })
      else if c == 46 && p.i + 1 < p.s.size && isDelim (p.s.get! (p.i + 1)) then
        let (tl, p) ← readVal { p with i := p.i + 1 }
        let p := skipWs p
        if p.i < p.s.size && p.s.get! p.i == 41 then pure (acc.foldr Val.cons tl, { p with i := p.i + 1 })
        else throw "malformed dotted list"
      else
        let (v, p) ← readVal p
        readList p (acc.push v)
    else throw "eof in list"

/-- Expand the recorder's run-length encoding, `(FN2-META-RLE N1 V1 N2 V2 ...)`, anywhere in `v`,
back into the list it stands for (N1 copies of V1, then N2 of V2, ...). -/
partial def expandRle (v : Val) : Val :=
  match v with
  | .cons (.sym "FN2-META-RLE") rest => Id.run do
    let mut pairs : Array (Nat × Val) := #[]
    let mut cur := rest
    while cur.isCons do
      pairs := pairs.push (cur.car.nfix, cur.cdr.car)
      cur := cur.cdr.cdr
    let mut out := Val.nil
    for (n, x) in pairs.reverse do
      for _ in [0:n] do
        out := .cons x out
    return out
  | .cons a d => Id.run do
    -- iterate along the spine, recurse only into elements
    let mut items : Array Val := #[]
    let mut cur := Val.cons a d
    while cur.isCons do
      items := items.push (expandRle cur.car)
      cur := cur.cdr
    return items.foldr Val.cons cur
  | x => x

/-- Read one object from the start of `s`. -/
def parse (s : String) : Except String Val := do
  let (v, _) ← readVal ⟨s.toUTF8, 0⟩
  pure v

end Fn2.ACL2.Read
