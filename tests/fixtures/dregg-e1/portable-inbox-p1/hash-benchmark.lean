/- Diagnostic only: time the existing Mini Lean cSHAKE implementation on one
exact public inbox file. This makes no admission, receipt or authority claim. -/
import Compiler.Sp800185Cshake256

open Minidregg.Compiler.Sp800185Cshake256

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "expected input path")
  let bytes ← IO.FS.readBinFile path
  let input := bytes.toList
  IO.println s!"inputBytes={input.length}"
  for index in [0:3] do
    let started : Nat ← IO.monoNanosNow
    let output := hash "DREGG.MEASURE/v1".toUTF8.toList input
    IO.println s!"sample={index} digest={output.digest.value}"
    let finished : Nat ← IO.monoNanosNow
    IO.println s!"sample={index} nanos={finished - started}"
  return 0
