module

public import Fn2.Arms.Syntax
import all Fn2.Arms.Syntax
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section
namespace Fn2.Arms.SyntaxControls
open Fn2.ACL2 Fn2.Arms.Syntax

/-- Data names that collide with internal syntax remain exact under QUOTE. -/
example : (expression 8 (Val.ofList [.sym "COMMON-LISP::QUOTE", .sym "ACL2:::SIZE"])).map
    (·.value) = .ok (Val.ofList [.sym "QUOTE", .sym "ACL2:::SIZE"]) := by decide +kernel

/-- CASE keys are data, even when they look like a variable used nearby. -/
example : (expression 8 (Val.ofList [.sym "COMMON-LISP::CASE", .sym "ACL2::X",
    Val.ofList [Val.ofList [.sym "ACL2::X"], .int 7]])).map (·.value) =
    .ok (Val.ofList [.sym "CASE", .sym "X", Val.ofList [Val.ofList [.sym "ACL2::X"], .int 7]]) := by
  decide +kernel

/-- One binder/reference environment must not flatten distinct package symbols. -/
example : readDeclaration 8 (Val.ofList [
    Val.ofList [.sym ":LET", .sym "ACL2::COUNT", .int 1],
    Val.ofList [.sym ":LET", .sym "ACL2::X", .sym "COMMON-LISP::COUNT"]]) =
    .error "distinct package symbols collide in declaration syntax" := by decide +kernel

example : readDeclaration 8 (Val.ofList [
    Val.ofList [.sym ":LET", .sym "ACL2::COUNT", .int 1],
    Val.ofList [.sym ":LET", .sym "ACL2::X", .sym "ACL2::COUNT"]]) =
    .ok (Val.ofList [Val.ofList [.sym ":LET", .sym "COUNT", .int 1],
      Val.ofList [.sym ":LET", .sym "X", .sym "COUNT"]]) := by decide +kernel

/-- An ACL2 symbol named QUOTE does not acquire COMMON-LISP:QUOTE semantics. -/
example : (expression 8 (Val.ofList [.sym "ACL2::QUOTE", .int 7])).map (·.value) =
    .error "operator has the wrong home package" := by decide +kernel

example : readDeclaration 8 (Val.ofList [Val.ofList [.sym ":LET", .sym "X", .int 1]]) =
    .error "syntax name lacks its home package" := by decide +kernel

/-- Matching failures are not successful expansion evidence. -/
example : expansionAgrees 8 Val.nil Val.nil (fun _ => .error "control") = false := by decide +kernel

end Fn2.Arms.SyntaxControls
end
