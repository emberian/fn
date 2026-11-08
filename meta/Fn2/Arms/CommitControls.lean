import Fn2.Arms
namespace Fn2.Arms.CommitControls
open Fn2.ACL2
deriving instance DecidableEq for Except
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
def submitting : CommitCtx := {tag := ":COMMIT", phases := [":COMMIT", ":COMMITTED"], tickets := ["WSTEP"]}
def waiting : CommitCtx := {submitting with tag := ":COMMITTED"}
def submit : Val := (Val.ofList [(Val.sym ":COMMIT"), (Val.sym "ROW-TX"), (Val.sym ":WORKSPACE"), (Val.ofList [(Val.sym "ROW-WS"), (Val.sym "ROW-WGEN")]), (Val.sym ":TICKET"), (Val.sym "WSTEP"), (Val.sym ":WAIT"), (Val.sym ":COMMITTED"), (Val.sym ":WHY"), (Val.sym "WHY"), (Val.sym ":DEPENDENCIES"), (Val.ofList [(Val.ofList [(Val.sym ":YIELD")])]), (Val.sym ":UNCHANGED"), (Val.ofList [(Val.ofList [(Val.sym ":IDLE")])]), (Val.sym ":REFUSED"), (Val.ofList [(Val.ofList [(Val.sym ":STOP"), (Val.sym ":MACHINE-PHASE")])])])
def settle : Val := (Val.ofList [(Val.sym ":COMMIT"), (Val.sym "ROW-TX"), (Val.sym ":WORKSPACE"), (Val.ofList [(Val.sym "ROW-WS"), (Val.sym "ROW-WGEN")]), (Val.sym ":TICKET"), (Val.sym "WSTEP"), (Val.sym ":WAIT"), (Val.sym ":COMMITTED"), (Val.sym ":WHY"), (Val.sym "WHY"), (Val.sym ":ACCEPTED"), (Val.ofList [(Val.ofList [(Val.sym ":WAKE")])]), (Val.sym ":REFUSED"), (Val.ofList [(Val.ofList [(Val.sym ":NOWAKE")])]), (Val.sym ":UNCERTAIN"), (Val.ofList [(Val.ofList [(Val.sym ":IDLE")])])])
def settledExpansion : Val := (Val.ofList [(Val.ofList [(Val.sym ":DO"), (Val.ofList [(Val.sym "COMMIT-TCODE"), (Val.sym "COMMIT-BATCH"), (Val.sym "COMMIT-EVENT"), (Val.sym "COMMIT-OUTCOME")]), (Val.ofList [(Val.sym "FN2-COMMIT-TAKE")]), (Val.sym ":EFFECTS"), (Val.ofList [(Val.ofList [(Val.sym ":RELEASE"), (Val.ofList [(Val.sym ":BATCH-MEMBERSHIP")])])]), (Val.sym ":ACCEPT"), (Val.ofList []), (Val.sym ":CASE"), (Val.ofList [(Val.ofList [(Val.ofList [(Val.sym ":PENDING")]), (Val.ofList [(Val.sym ":CHARGE"), (Val.sym ":STEPS"), (Val.sym "*FN2-WORK-EMPTY*")])]), (Val.ofList [(Val.ofList [(Val.sym ":OK")]), (Val.ofList [(Val.sym ":COND"), (Val.ofList [(Val.ofList [(Val.sym "EQUAL"), (Val.sym "COMMIT-OUTCOME"), (Val.sym "*FN2-COMMIT-OUTCOME-ACCEPTED*")]), (Val.ofList [(Val.sym ":DO"), (Val.ofList [(Val.sym "COMMIT-RCODE")]), (Val.ofList [(Val.sym "FN2-SUCCESSOR-RELEASE"), (Val.sym "ROW-TX")])]), (Val.ofList [(Val.sym ":WAKE")])]), (Val.ofList [(Val.ofList [(Val.sym "EQUAL"), (Val.sym "COMMIT-OUTCOME"), (Val.sym "*FN2-COMMIT-OUTCOME-UNCERTAIN*")]), (Val.ofList [(Val.sym ":IDLE")])]), (Val.ofList [Val.t, (Val.ofList [(Val.sym ":DO"), (Val.ofList [(Val.sym "COMMIT-RCODE")]), (Val.ofList [(Val.sym "FN2-SUCCESSOR-RELEASE"), (Val.sym "ROW-TX")])]), (Val.ofList [(Val.sym ":LET"), (Val.sym "WHY"), (Val.sym ":OUTCOME")]), (Val.ofList [(Val.sym ":NOWAKE")])])])])])])])

private theorem ok_exists {α : Type} (r : Except String α) (h : r.isOk = true) :
    ∃ v, r = .ok v := by
  cases r with
  | error e => simp [Except.isOk, Except.toBool] at h
  | ok v => exact ⟨v, rfl⟩

theorem submitting_expands : ∃ steps, Commit.expand submitting submit = .ok steps := ok_exists _ (by decide +kernel)
theorem settling_expansion : Commit.expand waiting settle = .ok settledExpansion.toList := by decide +kernel
theorem submit_independently_read : ∃ declaration,
    Arm.read {tag := ":COMMIT", sig := none, fn := "fixture", decl := Val.ofList [submit], commit := submitting} = .ok declaration := ok_exists _ (by decide +kernel)
theorem settle_independently_read : ∃ declaration,
    Arm.read {tag := ":COMMITTED", sig := none, fn := "fixture", decl := Val.ofList [settle], commit := waiting} = .ok declaration := ok_exists _ (by decide +kernel)
theorem wrong_ticket_rejected : Commit.expand {submitting with tickets := []} submit =
    .error ":ticket must be a u60 field" := by decide +kernel
theorem wrong_phase_rejected : Commit.expand {submitting with phases := []} submit =
    .error ":wait must be a phase" := by decide +kernel
theorem submitting_paths_cannot_settle : Commit.expand waiting submit =
    .error "invalid :commit options" := by decide +kernel
theorem subarm_uses_generator_context : ∃ declaration,
    Arm.read {tag := ":COMMITTED", sig := none, fn := "subarm-fixture", decl := Val.ofList [submit], commit := {submitting with tag := "NIL"}} = .ok declaration := ok_exists _ (by decide +kernel)
#print axioms settling_expansion
#print axioms submit_independently_read
#print axioms settle_independently_read
#print axioms wrong_ticket_rejected
#print axioms subarm_uses_generator_context
end Fn2.Arms.CommitControls
