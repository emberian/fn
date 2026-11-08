module

public import Fn2.ACL2.Val

@[expose] public section

namespace Fn2.Arms
open Fn2.ACL2

/-- Declaration facts needed by the durable mutation word. No expanded ACL2
body is supplied to this reader. -/
structure CommitCtx where
  tag : String := ""
  phases : List String := []
  tickets : List String := []
  deriving Inhabited, Repr

namespace Commit
def s := Val.sym
def l := Val.ofList
def form (head : String) (args : List Val := []) := l (s head :: args)
def proper : Val → Bool
  | .cons _ d => proper d
  | v => v == Val.nil
def get (key : String) : List Val → Val
  | .sym k :: v :: rest => if k == key then v else get key rest
  | _ => Val.nil
def has (key : String) : List Val → Bool
  | .sym k :: _ :: rest => k == key || has key rest
  | _ => false
def keys : List Val → List String → Bool
  | [], _ => true
  | .sym k :: _ :: rest, allowed => allowed.contains k && keys rest allowed
  | _, _ => false
def validVariable : Val → Bool
  | .sym n => !["NIL", "T", "ID", "BUDGET", "SLOT", "KIND", "ORDINAL", "EVENT",
      "OUTCOME", "REASON", "COUNT", "AUX0", "AUX1", "FN2-CORE", "FN2-MACHINES",
      "FN2-POOL", "FN2-OPS", "FN2-CONTROL"].contains n &&
      !n.startsWith ":" && !n.startsWith "*" && !n.startsWith "ROW-"
  | _ => false
def branch (codes : List String) (steps : List Val) := l (l (codes.map s) :: steps)
def doCase (vars : List String) (call : Val) (cases : List Val)
    (effects : List Val := []) :=
  form ":DO" ([l (vars.map s), call] ++ effects ++ [s ":ACCEPT", Val.nil, s ":CASE", l cases])

/-- Independently read `:commit`: submitting stages, emits, admits and binds;
settling releases on accepted/refused but preserves the uncertain successor. -/
def expand (ctx : CommitCtx) (step : Val) : Except String (List Val) := do
  if !proper step then throw ":commit has a dotted tail"
  let xs := step.toList
  if xs.length < 2 || xs.headD Val.nil != s ":COMMIT" then throw "expected :commit SUCC"
  let succ := xs[1]!
  let opts := xs.drop 2
  let ws := get ":WORKSPACE" opts
  let ticket := get ":TICKET" opts
  let wait := get ":WAIT" opts
  let why := get ":WHY" opts
  let bytes := if has ":BYTES" opts then get ":BYTES" opts else .int 24576
  let waiting := wait == s ctx.tag
  let paths := if waiting then [":ACCEPTED", ":REFUSED", ":UNCERTAIN"]
               else [":DEPENDENCIES", ":UNCHANGED", ":REFUSED"]
  if !keys opts ([":WORKSPACE", ":TICKET", ":WAIT", ":WHY", ":BYTES"] ++ paths) then
    throw "invalid :commit options"
  if !proper ws || ws.toList.length != 2 then throw ":workspace must be (SLOT GEN)"
  if !ctx.tickets.any (fun f => ticket == s f) then throw ":ticket must be a u60 field"
  if !ctx.phases.any (fun p => p.startsWith ":" && wait == s p) then throw ":wait must be a phase"
  if !paths.all (fun k => let p := get k opts; proper p && !p.toList.isEmpty) then
    throw "missing :commit continuation"
  if why != Val.nil && !validVariable why then throw "invalid :why variable"
  if !(match bytes with | .int n => n > 0 | _ => false) then throw "nonpositive :bytes"
  let path := fun k => (get k opts).toList
  let release := form ":DO" [l [s "COMMIT-RCODE"], form "FN2-SUCCESSOR-RELEASE" [succ]]
  let refuse := fun w => [release] ++
    (if why == Val.nil then [] else [form ":LET" [why, s w]]) ++ path ":REFUSED"
  let stop := form ":STOP" [s ":MACHINE-PHASE"]
  let charge := fun work => form ":CHARGE" [s ":STEPS", s work]
  if waiting then
    return [doCase ["COMMIT-TCODE", "COMMIT-BATCH", "COMMIT-EVENT", "COMMIT-OUTCOME"]
      (form "FN2-COMMIT-TAKE")
      [branch [":PENDING"] [charge "*FN2-WORK-EMPTY*"],
       branch [":OK"] [form ":COND"
        [l (form "EQUAL" [s "COMMIT-OUTCOME", s "*FN2-COMMIT-OUTCOME-ACCEPTED*"] ::
              release :: path ":ACCEPTED"),
         l (form "EQUAL" [s "COMMIT-OUTCOME", s "*FN2-COMMIT-OUTCOME-UNCERTAIN*"] :: path ":UNCERTAIN"),
         l (Val.t :: refuse ":OUTCOME")]]]
      [s ":EFFECTS", l [form ":RELEASE" [l [s ":BATCH-MEMBERSHIP"]]]]]
  let slot := ws.toList[0]!
  let gen := ws.toList[1]!
  let bounded := form "AND" [form "POSP" [s "COMMIT-B"],
    form "UNSIGNED-BYTE-P" [.int 60, s "COMMIT-B"], form "POSP" [s "COMMIT-EV"],
    form "UNSIGNED-BYTE-P" [.int 60, s "COMMIT-EV"]]
  let bind := [form ":DO" [l [s "COMMIT-BCODE"], form "FN2-SUCCESSOR-BIND" [succ, s "COMMIT-B", s "COMMIT-EV"]],
    form ":SET" [l [ticket, s "COMMIT-EV"]], form ":NEXT" [wait],
    form ":CHARGE" [s ":BYTES", bytes, s ":STEPS", s "*FN2-WORK-TRANSITION*"]]
  let admit := doCase ["COMMIT-ACODE", "COMMIT-B", "COMMIT-EV"]
    (form "FN2-COMMIT-ADMIT-TXN" [slot, gen, s "COMMIT-ELEN"])
    [branch [":OK"] [form ":IF" [bounded, l bind, l [stop]]],
     branch [":EXHAUSTED"] [form ":PARK" [s ":BATCH-MEMBERSHIP", s ":STEPS", s "*FN2-WORK-TRANSITION*"]],
     branch [":ADMISSION"] (refuse ":ADMISSION")]
    [s ":EFFECTS", l [form ":ACQUIRE" [l [s ":BATCH-MEMBERSHIP"]]]]
  let emit := doCase ["COMMIT-ECODE", "COMMIT-ELEN"]
    (form "FN2-SUCCESSOR-EMIT" [succ, slot, gen, .int 0, s "COMMIT-CAP"])
    [branch [":OK"] [form ":IF" [form "EQUAL" [s "COMMIT-ELEN", .int 0],
      l (release :: path ":UNCHANGED"), l [admit]]], branch [":ROOM"] (refuse ":ROOM")]
  let stage := doCase ["COMMIT-SCODE", "COMMIT-SLOT"] (form "FN2-SUCCESSOR-STAGE" [succ])
    [branch [":OK"] [emit],
     branch [":FULL"] [form ":CHARGE" [s ":BYTES", bytes, s ":STEPS", s "*FN2-WORK-TRANSITION*", s ":RUNNABLE", Val.t]],
     branch [":STALE", ":CHANGED"] (release :: path ":DEPENDENCIES"),
     branch [":DUPLICATE"] (refuse ":DUPLICATE"),
     branch [":REFUSED", ":EVIDENCE", ":CAPACITY", ":INCONSISTENT", ":RANGE"] (refuse ":REFUSED")]
  return [form ":IF" [form "EQ" [form "FN2-COMMIT-POSTURE", s ":DRAINING"], l (refuse ":DRAINING"),
    l [form ":IF" [form "NOT" [form "EQ" [form "FN2-MACHINE-POOL-CAPACITY-READ-CODE" [slot], s ":OK"]],
      l [stop], l [form ":LET" [s "COMMIT-CAP", form "FN2-MACHINE-POOL-CAPACITY" [slot]], stage]]]]]

end Commit
end Fn2.Arms

end
