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

deriving instance DecidableEq for Except


/-- Data names that collide with internal syntax remain exact under QUOTE. -/
theorem quote_keeps_data : (expression 8 (Val.ofList [.sym "COMMON-LISP::QUOTE", .sym "ACL2:::SIZE"])).map
    (·.value) = .ok (Val.ofList [.sym "QUOTE", .sym "ACL2:::SIZE"]) := by decide +kernel

/-- CASE keys are data, even when they look like a variable used nearby. -/
theorem case_keeps_keys : (expression 8 (Val.ofList [.sym "COMMON-LISP::CASE", .sym "ACL2::X",
    Val.ofList [Val.ofList [.sym "ACL2::X"], .int 7]])).map (·.value) =
    .ok (Val.ofList [.sym "CASE", .sym "X", Val.ofList [Val.ofList [.sym "ACL2::X"], .int 7]]) := by
  decide +kernel

/-- One binder/reference environment must not flatten distinct package symbols. -/
theorem mixed_package_names_refused : readDeclaration 8 (Val.ofList [
    Val.ofList [.sym ":LET", .sym "ACL2::COUNT", .int 1],
    Val.ofList [.sym ":LET", .sym "ACL2::X", .sym "COMMON-LISP::COUNT"]]) =
    .error "distinct package symbols collide in declaration syntax" := by decide +kernel

theorem same_package_names_accepted : readDeclaration 8 (Val.ofList [
    Val.ofList [.sym ":LET", .sym "ACL2::COUNT", .int 1],
    Val.ofList [.sym ":LET", .sym "ACL2::X", .sym "ACL2::COUNT"]]) =
    .ok (Val.ofList [Val.ofList [.sym ":LET", .sym "COUNT", .int 1],
      Val.ofList [.sym ":LET", .sym "X", .sym "COUNT"]]) := by decide +kernel

/-- An ACL2 symbol named QUOTE does not acquire COMMON-LISP:QUOTE semantics. -/
theorem wrong_quote_package_refused : (expression 8 (Val.ofList [.sym "ACL2::QUOTE", .int 7])).map (·.value) =
    .error "operator has the wrong home package" := by decide +kernel

theorem unqualified_names_refused : readDeclaration 8 (Val.ofList [Val.ofList [.sym ":LET", .sym "X", .int 1]]) =
    .error "syntax name lacks its home package" := by decide +kernel

/-- Matching failures are not successful expansion evidence. -/
theorem matching_errors_refused : expansionAgrees 8 Val.nil Val.nil (fun _ => .error "control") = false := by decide +kernel

/-- Whole antecedent and concrete conclusion for the expansion soundness bridge. -/
def witnessWord : Val := Val.ofList [.sym ":LET", .sym "ACL2::X", .int 1]
def witnessInternal : Val := Val.ofList [.sym ":LET", .sym "X", .int 1]
def echoExpansion (v : Val) : Except String (List Val) := .ok [v]

theorem expansion_whole_success : expansionAgrees 8 witnessWord (Val.ofList [witnessWord]) echoExpansion = true ∧
    readStep 8 witnessWord = .ok witnessInternal ∧
    readSteps 8 (Val.ofList [witnessWord]) = .ok (Val.ofList [witnessInternal]) ∧
    echoExpansion witnessInternal = .ok [witnessInternal] := by decide +kernel

/-- Removing successful agreement permits an input with no successful projection. -/
theorem expansion_hypothesis_removal : expansionAgrees 8 Val.nil Val.nil echoExpansion = false ∧
    ¬ ∃ w e, readStep 8 Val.nil = .ok w ∧ readSteps 8 Val.nil = .ok e ∧
      echoExpansion w = .ok e.toList := by
  constructor
  · decide +kernel
  · rintro ⟨w, e, hw, _, _⟩
    have bad : readStep 8 Val.nil = .error "step lacks a keyword head" := by decide +kernel
    rw [bad] at hw
    cases hw

#print axioms Fn2.Arms.Syntax.expansionAgrees_sound
#print axioms quote_keeps_data
#print axioms case_keeps_keys
#print axioms mixed_package_names_refused
#print axioms same_package_names_accepted
#print axioms wrong_quote_package_refused
#print axioms unqualified_names_refused
#print axioms matching_errors_refused
#print axioms expansion_whole_success
#print axioms expansion_hypothesis_removal
end Fn2.Arms.SyntaxControls
end
