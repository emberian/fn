import Fn2.Decl
import Fn2.Arms
import Fn2.Arms.Derive
import Fn2.Pathway
import Fn2.Instances.LayerA
import Fn2.Instances.LayerAFacts
import Fn2.Instances.LayerAKinds

/-!
# Fn2.MachineProofs: Per-Machine Contract Proofs & PW3 Wrapper Instantiation (Brick H6)

This module instantiates the universal `Step` structural induction theorems
(`Step.eval_wfp`, `Step.eval_frame`, `Step.eval_budget`, `Step.eval_holds_sublist`)
from `Fn2.Arms.Derive` and the PW3 wrapper preservation theorems
(`project_reconstruct`, `reconstruct_frame_entry`, `entering_frame_entry`,
`armCorrect_project_preserve`) from `Fn2.Pathway` across the exported machine registry:
- `fn2-listener` (`FN2-LISTENER`)
- `fn2-echo` (`FN2-ECHO`)
- `fn2-scribe` (`FN2-SCRIBE`)
- `fn2-cursor` (`FN2-CURSOR`)
- `fn2-txn` (`FN2-TXN`)
- `fn2-ctl` (`FN2-CTL`)
- `fn2-cns` (`FN2-CNS`)
as well as across all 22 kinds in `Fn2.Instances.LayerAKinds.kinds`.
-/

namespace Fn2.MachineProofs
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Derive Fn2.Pathway

/-! ## 1. Exported Machine Kind Definitions (`fn2-listener`, `fn2-echo`, `fn2-scribe`, `fn2-cursor`, `fn2-txn`, `fn2-ctl`, `fn2-cns`) -/

def findKind (name : String) : Kind :=
  (Fn2.Instances.LayerAKinds.kinds.find? (·.name == name)).getD toothKind

/-- `fn2-listener`: Layer A listener machine from `LayerAKinds.kinds`. -/
def listenerKind : Kind := findKind "FN2-LISTENER"

/-- `fn2-echo`: Layer A echo machine from `LayerAKinds.kinds`. -/
def echoKind : Kind := findKind "FN2-ECHO"

/-- `fn2-scribe`: Layer A scribe machine from `LayerAKinds.kinds`. -/
def scribeKind : Kind := findKind "FN2-SCRIBE"

/-- `fn2-cursor`: Layer D reader cursor machine from `LayerAKinds.kinds`. -/
def cursorKind : Kind := findKind "FN2-CURSOR"

/-- `fn2-txn`: Layer D article/post transaction machine (`books/txn-kind.lisp`, `books/txn.lisp`). -/
def txnKind : Kind :=
  { name := "FN2-TXN"
    childForm := true
    tuple := ["FN2-TXN", "FN2-UPLOAD", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL",
              "FN2-CLAIMS", "FN2-SUCC-TXNS", "FN2-SUCC-SLOTS", "FN2-ID-DECIDES", "FN2-FIELDS"]
    states := [":FREE", ":ADMIT", ":RESERVE", ":LOOKUP", ":GROUPS", ":COUNT", ":STAGE",
               ":BIND", ":COMMIT", ":REFUSED", ":RELEASING", ":DRAINING", ":RETIRED"]
    phases := [(":FREE", 0), (":ADMIT", 1), (":RESERVE", 2), (":LOOKUP", 3), (":GROUPS", 4),
               (":COUNT", 5), (":STAGE", 6), (":BIND", 7), (":COMMIT", 8), (":REFUSED", 9),
               (":RELEASING", 10), (":DRAINING", 11), (":RETIRED", 12)]
    columns := [("PHASE", .enum 13), ("GENERATION", .uw 60), ("PRINCIPAL-SLOT", .uw 16),
                ("WAIT-REASON", .enum 26), ("UPLOAD", .uw 32), ("UPLOAD-GEN", .uw 60),
                ("CONN", .uw 32), ("CONN-GEN", .uw 60), ("REQUEST", .uw 60),
                ("OFFERED", .uw 1), ("NGROUPS", .uw 16), ("GCUR", .uw 32), ("GSKIP", .uw 1),
                ("LINES", .uw 32), ("WORD", .uw 8), ("NEXT-FREE", .uw 32), ("STOPPED", .uw 1)]
    table := ["PHASE", "GENERATION", "PRINCIPAL-SLOT", "UPLOAD", "UPLOAD-GEN", "CONN", "CONN-GEN",
              "REQUEST", "OFFERED", "NGROUPS", "GCUR", "GSKIP", "LINES", "WORD", "NEXT-FREE", "STOPPED"]
    stops := []
    links := []
    subarms := [
      { tag := "REPLY"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL", "FN2-SUCC-TXNS"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "WORD", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":RELEASING"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-SUB-REPLY-CHILDREN" }
    ]
    arms := [
      { tag := ":FREE"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-TXN-RUN-FREE-CHILDREN" },
      { tag := ":ADMIT"
        sig := some ⟨["FN2-TXN", "FN2-UPLOAD", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL", "FN2-CLAIMS"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "OFFERED", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":RESERVE"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 256, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-RUN-ADMIT-CHILDREN" },
      { tag := ":RESERVE"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL", "FN2-CLAIMS"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":LOOKUP"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 4096, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-RUN-RESERVE-CHILDREN" },
      { tag := ":LOOKUP"
        sig := some ⟨["FN2-TXN", "FN2-UPLOAD", "FN2-MACHINES", "FN2-CONTROL", "FN2-SUCC-TXNS", "FN2-ID-DECIDES", "FN2-FIELDS"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "OFFERED", .int 1]],
          Val.ofList [.sym ":NEXT", .sym ":GROUPS"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 4096, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-RUN-LOOKUP-CHILDREN" },
      { tag := ":GROUPS"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "NGROUPS", .int 1]],
          Val.ofList [.sym ":NEXT", .sym ":COUNT"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 8192, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-RUN-GROUPS-CHILDREN" },
      { tag := ":COUNT"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "LINES", .int 1]],
          Val.ofList [.sym ":NEXT", .sym ":STAGE"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 2048, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-RUN-COUNT-CHILDREN" },
      { tag := ":STAGE"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":BIND"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 4096, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-RUN-STAGE-CHILDREN" },
      { tag := ":BIND"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":COMMIT"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-RUN-BIND-CHILDREN" },
      { tag := ":COMMIT"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL", "FN2-SUCC-TXNS"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":GOTO", .sym "REPLY"]
        ]
        fn := "FN2-TXN-RUN-COMMIT-CHILDREN" },
      { tag := ":REFUSED"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL", "FN2-SUCC-TXNS"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":GOTO", .sym "REPLY"]
        ]
        fn := "FN2-TXN-RUN-REFUSED-CHILDREN" },
      { tag := ":RELEASING"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":DRAINING"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-TXN-RUN-RELEASING-CHILDREN" },
      { tag := ":DRAINING"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-TXN", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":DO", Val.nil, Val.ofList [.sym "FN2-MACHINE-RECLAIM", .sym "ID", .int 0, Val.nil]],
          Val.ofList [.sym ":NEXT", .sym ":FREE"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-RELEASE*"]
        ]
        fn := "FN2-TXN-RUN-DRAINING-CHILDREN" },
      { tag := ":RETIRED"
        sig := some ⟨["FN2-TXN", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-TXN-RUN-RETIRED-CHILDREN" }
    ]
    observes := [] }

/-- `fn2-ctl`: Layer E control-port carrier machine (`books/cns-kind.lisp`, `books/cns.lisp`). -/
def ctlKind : Kind :=
  { name := "FN2-CTL"
    childForm := true
    tuple := ["FN2-CTL", "FN2-MACHINES", "FN2-POOL", "FN2-OPS", "FN2-CONTROL", "FN2-CNS"]
    states := [":FREE", ":GREETING", ":FRAME", ":DISPATCH", ":WAITING", ":REPLY", ":CLOSING", ":DRAINING", ":RETIRED"]
    phases := [(":FREE", 0), (":GREETING", 1), (":FRAME", 2), (":DISPATCH", 3), (":WAITING", 4),
               (":REPLY", 5), (":CLOSING", 6), (":DRAINING", 7), (":RETIRED", 8)]
    columns := [("PHASE", .enum 9), ("GENERATION", .uw 60), ("PRINCIPAL-SLOT", .uw 16),
                ("WAIT-REASON", .enum 26), ("CAP-INDEX", .uw 32), ("CAP-NONCE", .uw 32),
                ("RX-SLOT", .uw 32), ("RX-GEN", .uw 60), ("TX-SLOT", .uw 32), ("TX-GEN", .uw 60),
                ("PENDING", .uw 32), ("BORROWS", .uw 32), ("OWNER", .uw 1), ("POSTURE", .uw 8),
                ("CMD", .uw 8), ("FKIND", .uw 8), ("POS", .uw 32), ("FILL", .uw 32), ("FLEN", .uw 32),
                ("TX-OFF", .uw 32), ("TX-LEN", .uw 32), ("REQUEST", .uw 60), ("CNS", .uw 32),
                ("CNS-GEN", .uw 60), ("NEXT-FREE", .uw 32), ("STOPPED", .uw 1)]
    table := ["PHASE", "GENERATION", "PRINCIPAL-SLOT", "CAP-INDEX", "CAP-NONCE", "RX-SLOT", "RX-GEN",
              "TX-SLOT", "TX-GEN", "PENDING", "BORROWS", "OWNER", "POSTURE", "CMD", "FKIND", "POS",
              "FILL", "FLEN", "TX-OFF", "TX-LEN", "REQUEST", "CNS", "CNS-GEN", "NEXT-FREE", "STOPPED"]
    stops := []
    links := []
    subarms := []
    arms := [
      { tag := ":FREE"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-CTL-RUN-FREE-CHILDREN" },
      { tag := ":GREETING"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "OWNER", .int 1], Val.ofList [.sym "FILL", .int 0], Val.ofList [.sym "POS", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":FRAME"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CTL-RUN-GREETING-CHILDREN" },
      { tag := ":FRAME"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES", "FN2-POOL", "FN2-OPS", "FN2-CONTROL"],
                     ["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "POS", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":DISPATCH"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 4096, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CTL-RUN-FRAME-CHILDREN" },
      { tag := ":DISPATCH"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "TX-OFF", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":WAITING"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CTL-RUN-DISPATCH-CHILDREN" },
      { tag := ":WAITING"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":REPLY"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CTL-RUN-WAITING-CHILDREN" },
      { tag := ":REPLY"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES", "FN2-POOL", "FN2-OPS", "FN2-CONTROL"],
                     ["FN2-CTL", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":DO", Val.ofList [.sym "CODE"], Val.ofList [.sym "FN2-CORE-RESET", .sym "ROW-RX-SLOT", .sym "ROW-RX-GEN"]],
          Val.ofList [.sym ":SET", Val.ofList [.sym "TX-OFF", .int 0], Val.ofList [.sym "TX-LEN", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":FRAME"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CTL-RUN-REPLY-CHILDREN" },
      { tag := ":CLOSING"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES", "FN2-POOL", "FN2-OPS", "FN2-CONTROL"],
                     ["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":WAIT", .sym ":COMPLETION", .sym ":BYTES", .int 0]
        ]
        fn := "FN2-CTL-RUN-CLOSING-CHILDREN" },
      { tag := ":DRAINING"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL"],
                     ["FN2-CTL", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":DO", Val.ofList [.sym "RCODE"], Val.ofList [.sym "FN2-CORE-RELEASE", .sym "ROW-RX-SLOT", .sym "ROW-RX-GEN"]],
          Val.ofList [.sym ":DO", Val.nil, Val.ofList [.sym "FN2-MACHINE-RECLAIM", .sym "ID", .int 0, Val.nil]],
          Val.ofList [.sym ":NEXT", .sym ":FREE"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-RELEASE*"]
        ]
        fn := "FN2-CTL-RUN-DRAINING-CHILDREN" },
      { tag := ":RETIRED"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-CTL-RUN-RETIRED-CHILDREN" }
    ]
    observes := [
      { tag := ":CLOSE-RESULT"
        sig := some ⟨["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CTL", "FN2-MACHINES", "FN2-CONTROL"], 1⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":DRAINING"],
          Val.ofList [.sym ":WAKE"]
        ]
        fn := "FN2-CTL-ON-CLOSE-RESULT-CHILDREN" }
    ] }

/-- `fn2-cns`: Layer E consumer request machine (`books/cns-kind.lisp`, `books/cns.lisp`). -/
def cnsKind : Kind :=
  { name := "FN2-CNS"
    childForm := true
    tuple := ["FN2-CNS", "FN2-CTL", "FN2-MACHINES", "FN2-POOL", "FN2-CONTROL",
              "FN2-ID-ENGINE", "FN2-READS", "FN2-RANGES", "FN2-SEEKS", "FN2-WAIT-EDGES"]
    states := [":FREE", ":DECODE", ":CHECK", ":LOOKUP", ":READ", ":PAGE", ":PARK", ":COMMIT", ":DRAINING", ":RETIRED"]
    phases := [(":FREE", 0), (":DECODE", 1), (":CHECK", 2), (":LOOKUP", 3), (":READ", 4),
               (":PAGE", 5), (":PARK", 6), (":COMMIT", 7), (":DRAINING", 8), (":RETIRED", 9)]
    columns := [("PHASE", .enum 10), ("GENERATION", .uw 60), ("PRINCIPAL-SLOT", .uw 16),
                ("WAIT-REASON", .enum 26), ("DEADLINE", .uw 60), ("CTL", .uw 32), ("CTL-GEN", .uw 60),
                ("REQUEST", .uw 60), ("FKIND", .uw 8), ("VERB", .uw 8), ("OUTCOME", .uw 8),
                ("REASON", .uw 8), ("EPOCH", .uw 60), ("CPOS", .uw 60), ("TO", .uw 60),
                ("PUB-FRONTIER", .uw 60), ("PAGE-LIMIT", .uw 32), ("WAIT-MS", .uw 60),
                ("COUNT", .uw 32), ("MORE", .uw 1), ("EDGE", .uw 32), ("TX-SLOT", .uw 32),
                ("TX-GEN", .uw 60), ("TX-LEN", .uw 32), ("NEXT-FREE", .uw 32), ("STOPPED", .uw 1)]
    table := ["PHASE", "GENERATION", "PRINCIPAL-SLOT", "DEADLINE", "CTL", "CTL-GEN", "REQUEST",
              "FKIND", "VERB", "OUTCOME", "REASON", "EPOCH", "CPOS", "TO", "PUB-FRONTIER",
              "PAGE-LIMIT", "WAIT-MS", "COUNT", "MORE", "EDGE", "TX-SLOT", "TX-GEN", "TX-LEN",
              "NEXT-FREE", "STOPPED"]
    stops := []
    links := []
    subarms := [
      { tag := "HAND"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":WAKE-ROW", .sym "ROW-CTL"],
          Val.ofList [.sym ":NEXT", .sym ":DRAINING"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 512, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CNS-SUB-HAND-CHILDREN" },
      { tag := "ANSWER"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "TX-LEN", .int 6]],
          Val.ofList [.sym ":GOTO", .sym "HAND"]
        ]
        fn := "FN2-CNS-SUB-ANSWER-CHILDREN" },
      { tag := "REFUSE"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "OUTCOME", .int 2]],
          Val.ofList [.sym ":GOTO", .sym "ANSWER"]
        ]
        fn := "FN2-CNS-SUB-REFUSE-CHILDREN" }
    ]
    arms := [
      { tag := ":FREE"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-CNS-RUN-FREE-CHILDREN" },
      { tag := ":DECODE"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "EPOCH", .int 1]],
          Val.ofList [.sym ":NEXT", .sym ":CHECK"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 4096, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CNS-RUN-DECODE-CHILDREN" },
      { tag := ":CHECK"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":LOOKUP"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CNS-RUN-CHECK-CHILDREN" },
      { tag := ":LOOKUP"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":READ"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 4096, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CNS-RUN-LOOKUP-CHILDREN" },
      { tag := ":READ"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "COUNT", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":PAGE"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 4096, .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CNS-RUN-READ-CHILDREN" },
      { tag := ":PAGE"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":GOTO", .sym "ANSWER"]
        ]
        fn := "FN2-CNS-RUN-PAGE-CHILDREN" },
      { tag := ":PARK"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":READ"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-TRANSITION*", .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-CNS-RUN-PARK-CHILDREN" },
      { tag := ":COMMIT"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "OUTCOME", .int 1]],
          Val.ofList [.sym ":GOTO", .sym "ANSWER"]
        ]
        fn := "FN2-CNS-RUN-COMMIT-CHILDREN" },
      { tag := ":DRAINING"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-CNS", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":DO", Val.nil, Val.ofList [.sym "FN2-MACHINE-RECLAIM", .sym "ID", .int 0, Val.nil]],
          Val.ofList [.sym ":NEXT", .sym ":FREE"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .sym "*FN2-WORK-RELEASE*"]
        ]
        fn := "FN2-CNS-RUN-DRAINING-CHILDREN" },
      { tag := ":RETIRED"
        sig := some ⟨["FN2-CNS", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-CNS-RUN-RETIRED-CHILDREN" }
    ]
    observes := [] }

/-- All 7 named machines of the Brick H6 machine registry. -/
def machineRegistryKinds : List Kind :=
  [listenerKind, echoKind, scribeKind, cursorKind, txnKind, ctlKind, cnsKind]

/-! ## 2. Per-Machine Contract Checking & PW3 `ArmWF` Verification -/

def checkMachineKind (w : World) (k : Kind) : Bool :=
  let allArms := k.subarms ++ k.arms ++ k.observes
  allArms.all (fun a => a.read.isOk && derivedFuel w k a > 0) &&
  (!k.childForm ||
    (k.arms.all (fun a => ArmWF k a false && (returns k a).all (derivedTables w k a).contains) &&
     k.subarms.all (fun a => ArmWF k a false && (returns k a).all (derivedTables w k a).contains) &&
     k.observes.all (fun a => ArmWF k a true && (returns k a).all (derivedTables w k a).contains)))

theorem listener_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world listenerKind = true := by
  decide +kernel

theorem echo_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world echoKind = true := by
  decide +kernel

theorem scribe_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world scribeKind = true := by
  decide +kernel

theorem cursor_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world cursorKind = true := by
  decide +kernel

theorem txn_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world txnKind = true := by
  decide +kernel

theorem ctl_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world ctlKind = true := by
  decide +kernel

theorem cns_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world cnsKind = true := by
  decide +kernel

theorem machineRegistry_contracts_hold :
    (machineRegistryKinds.all (checkMachineKind Fn2.Instances.LayerAKinds.world)) = true := by
  decide +kernel

theorem layerAKinds_contracts_hold :
    (Fn2.Instances.LayerAKinds.kinds.all
      (checkMachineKind Fn2.Instances.LayerAKinds.world)) = true := by
  decide +kernel

/-! ## 3. Per-Machine Instantiations of `Step.eval_wfp`, `Step.eval_frame`, `Step.eval_budget`, `Step.eval_holds_sublist` -/

/-- Universal per-machine `Step.eval_wfp` instantiation: next-phase membership in `derivedNext`
    and fuel bounded by `derivedFuel`. -/
theorem machine_eval_wfp (k : Kind) (a : Arm) (observe : Bool)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (subSteps : String → List Step)
    (hsubN : ∀ hn name,
      let subN := subNext k (k.subarms.length + 1)
      let refN := fun h =>
        if decl.onRefusal.isEmpty then ([], !h)
        else stepsNext k (fun h' => ([], !h')) subN h decl.onRefusal
      (∀ p ∈ (stepsNext k refN subN hn (subSteps name)).1, p ∈ (subN hn name).1) ∧
      ((stepsNext k refN subN hn (subSteps name)).2 = true → (subN hn name).2 = true))
    (hsubF : ∀ env name,
      let subF := subFuel Fn2.Instances.LayerAKinds.world k (k.subarms.length + 1)
      let refF := fun e =>
        if decl.onRefusal.isEmpty then 1
        else stepsFuel Fn2.Instances.LayerAKinds.world (fun _ => 1) subF e decl.onRefusal
      stepsFuel Fn2.Instances.LayerAKinds.world refF subF env (subSteps name) ≤ subF env name)
    (initPhase : String)
    (hinit : if k.states.contains a.tag then initPhase = a.tag else initPhase ∈ decl.from_)
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec Fn2.Instances.LayerAKinds.world k observe decl.onRefusal subSteps
      [] false decl.steps c ts ws ph fu) :
    (ph.getD initPhase) ∈ derivedNext Fn2.Instances.LayerAKinds.world k a ∧
    fu ≤ derivedFuel Fn2.Instances.LayerAKinds.world k a := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hstep1, hstep2⟩ := Step.eval_wfp Fn2.Instances.LayerAKinds.world k observe
      decl.onRefusal subSteps _ _ hsubN hexec
    unfold derivedNext
    rw [hread]
    simp only [List.mem_eraseDups, List.mem_append]
    cases ph with
    | some p => exact Or.inl (hstep1 p rfl)
    | none =>
      have hstay := hstep2 rfl rfl
      right
      simp only [hstay, Bool.not_true, Bool.false_eq_true, if_false]
      split at hinit
      · rename_i hst; simp only [hst, if_true, List.mem_singleton, Option.getD_none]; exact hinit
      · rename_i hst; simp only [hst, Bool.false_eq_true, if_false, Option.getD_none]; exact hinit
  · unfold derivedFuel
    rw [hread]
    exact stepsExec_fuel_le Fn2.Instances.LayerAKinds.world k observe
      decl.onRefusal subSteps _ _ hsubF hexec

/-- Universal per-machine `Step.eval_frame` instantiation: any table `tbl ∈ k.tuple` outside
    `derivedTables` and any column outside `derivedWrites` is preserved. -/
theorem machine_eval_frame (k : Kind) (a : Arm) (observe : Bool)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (subSteps : String → List Step)
    (hsubT : ∀ name t,
      t ∈ stepsTables Fn2.Instances.LayerAKinds.world k
        (stepsTables Fn2.Instances.LayerAKinds.world k []
          (subTables Fn2.Instances.LayerAKinds.world k (k.subarms.length + 1)) decl.onRefusal)
        (subTables Fn2.Instances.LayerAKinds.world k (k.subarms.length + 1)) (subSteps name) →
      t ∈ subTables Fn2.Instances.LayerAKinds.world k (k.subarms.length + 1) name)
    (hsubW : ∀ name f,
      f ∈ stepsWrites Fn2.Instances.LayerAKinds.world
        (stepsWrites Fn2.Instances.LayerAKinds.world []
          (subWrites Fn2.Instances.LayerAKinds.world k (k.subarms.length + 1)) decl.onRefusal)
        (subWrites Fn2.Instances.LayerAKinds.world k (k.subarms.length + 1)) (subSteps name) →
      f ∈ subWrites Fn2.Instances.LayerAKinds.world k (k.subarms.length + 1) name)
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec Fn2.Instances.LayerAKinds.world k observe decl.onRefusal subSteps
      [] false decl.steps c ts ws ph fu) :
    (∀ tbl ∈ k.tuple, tbl ∈ ts → tbl ∈ derivedTables Fn2.Instances.LayerAKinds.world k a) ∧
    (∀ col ∈ ws, col ∈ derivedWrites Fn2.Instances.LayerAKinds.world k a) := by
  refine ⟨fun tbl htup hts => ?_, fun col hcol => ?_⟩
  · unfold derivedTables
    rw [hread]
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨htup, Step.eval_frame Fn2.Instances.LayerAKinds.world k observe
      decl.onRefusal subSteps _ _ hsubT hexec tbl hts⟩
  · unfold derivedWrites
    rw [hread]
    simp only [List.mem_eraseDups]
    exact stepsExec_writes_sub Fn2.Instances.LayerAKinds.world k observe
      decl.onRefusal subSteps _ _ hsubW hexec col hcol

/-- Universal per-machine `Step.eval_budget` instantiation: cost triple `c` is bounded by
    `derivedCost`. -/
theorem machine_eval_budget (k : Kind) (a : Arm) (observe : Bool)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (subSteps : String → List Step)
    (hsubC : ∀ env name,
      let w := Fn2.Instances.LayerAKinds.world
      let subC := subCost w k observe (k.subarms.length + 1)
      let refC := fun e =>
        if decl.onRefusal.isEmpty then
          if observe then costZero else (0, constInt w "*FN2-WORK-EMPTY*" 1, 0)
        else stepsCost w observe (fun _ => costZero) subC e decl.onRefusal
      CostLe (stepsCost w observe refC subC env (subSteps name)) (subC env name))
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec Fn2.Instances.LayerAKinds.world k observe decl.onRefusal subSteps
      [] false decl.steps c ts ws ph fu) :
    CostLe c (derivedCost Fn2.Instances.LayerAKinds.world k a observe) := by
  unfold derivedCost
  rw [hread]
  exact Step.eval_budget Fn2.Instances.LayerAKinds.world k observe
    decl.onRefusal subSteps _ _ hsubC hexec

/-- Universal per-machine `Step.eval_holds_sublist` instantiation: every hold effect `h ∈ hs`
    is a member of `derivedHolds`. -/
theorem machine_eval_holds_sublist (k : Kind) (a : Arm)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (subSteps : String → List Step)
    (hsubH : ∀ name h,
      h ∈ stepsHolds
        (stepsHolds [] (subHolds k (k.subarms.length + 1)) decl.onRefusal)
        (subHolds k (k.subarms.length + 1)) (subSteps name) →
      h ∈ subHolds k (k.subarms.length + 1) name)
    {hs : List String}
    (hexec : StepsExecHolds decl.onRefusal subSteps decl.steps hs) :
    ∀ h ∈ hs, h ∈ derivedHolds Fn2.Instances.LayerAKinds.world k a := by
  intro h hh
  unfold derivedHolds
  rw [hread]
  simp only [List.mem_eraseDups]
  exact Step.eval_holds_sublist decl.onRefusal subSteps _ _ hsubH hexec h hh

-- Per-machine specializations for all 7 machines:
abbrev listener_eval_wfp := @machine_eval_wfp listenerKind
abbrev listener_eval_frame := @machine_eval_frame listenerKind
abbrev listener_eval_budget := @machine_eval_budget listenerKind
abbrev listener_eval_holds_sublist := @machine_eval_holds_sublist listenerKind

abbrev echo_eval_wfp := @machine_eval_wfp echoKind
abbrev echo_eval_frame := @machine_eval_frame echoKind
abbrev echo_eval_budget := @machine_eval_budget echoKind
abbrev echo_eval_holds_sublist := @machine_eval_holds_sublist echoKind

abbrev scribe_eval_wfp := @machine_eval_wfp scribeKind
abbrev scribe_eval_frame := @machine_eval_frame scribeKind
abbrev scribe_eval_budget := @machine_eval_budget scribeKind
abbrev scribe_eval_holds_sublist := @machine_eval_holds_sublist scribeKind

abbrev cursor_eval_wfp := @machine_eval_wfp cursorKind
abbrev cursor_eval_frame := @machine_eval_frame cursorKind
abbrev cursor_eval_budget := @machine_eval_budget cursorKind
abbrev cursor_eval_holds_sublist := @machine_eval_holds_sublist cursorKind

abbrev txn_eval_wfp := @machine_eval_wfp txnKind
abbrev txn_eval_frame := @machine_eval_frame txnKind
abbrev txn_eval_budget := @machine_eval_budget txnKind
abbrev txn_eval_holds_sublist := @machine_eval_holds_sublist txnKind

abbrev ctl_eval_wfp := @machine_eval_wfp ctlKind
abbrev ctl_eval_frame := @machine_eval_frame ctlKind
abbrev ctl_eval_budget := @machine_eval_budget ctlKind
abbrev ctl_eval_holds_sublist := @machine_eval_holds_sublist ctlKind

abbrev cns_eval_wfp := @machine_eval_wfp cnsKind
abbrev cns_eval_frame := @machine_eval_frame cnsKind
abbrev cns_eval_budget := @machine_eval_budget cnsKind
abbrev cns_eval_holds_sublist := @machine_eval_holds_sublist cnsKind

/-! ## 4. Per-Machine PW3 Wrapper Preservation Instantiations & Concrete Witnesses -/

abbrev echo_pw3_wrapper := @project_reconstruct echoKind
abbrev scribe_pw3_wrapper := @project_reconstruct scribeKind
abbrev cursor_pw3_wrapper := @project_reconstruct cursorKind
abbrev txn_pw3_wrapper := @project_reconstruct txnKind
abbrev ctl_pw3_wrapper := @project_reconstruct ctlKind
abbrev cns_pw3_wrapper := @project_reconstruct cnsKind

/-- Positive Witness (`pw3_wrapper_preserve_pos`): Across all 6 child-form machines
    (`echoKind`, `scribeKind`, `cursorKind`, `txnKind`, `ctlKind`, `cnsKind`),
    `project_reconstruct` recovers the normalized narrow output and `reconstruct`
    preserves every unreturned child slot from `entering`. -/
def checkPW3Roundtrip (k : Kind) : Bool :=
  let input := k.tuple.map (fun c => Val.sym ("IN-" ++ c))
  (k.subarms ++ k.arms).all (fun a =>
    let v := Val.ofList ([.int 64, .int 2, .int 0, Val.t] ++
      (returns k a).map (fun c => Val.sym ("OUT-" ++ c)))
    let recon := reconstruct k a false input (normalize k a false v)
    project k a false recon == normalize k a false v) &&
  k.observes.all (fun a =>
    let v := Val.ofList ([Val.t] ++
      (returns k a).map (fun c => Val.sym ("OUT-" ++ c)))
    let recon := reconstruct k a true input (normalize k a true v)
    project k a true recon == normalize k a true v)

theorem pw3_wrapper_roundtrip_all_machines :
    ([echoKind, scribeKind, cursorKind, txnKind, ctlKind, cnsKind].all
      checkPW3Roundtrip) = true := by
  decide +kernel

theorem pw3_wrapper_roundtrip_all_layerAKinds :
    ((Fn2.Instances.LayerAKinds.kinds.filter (·.childForm)).all
      checkPW3Roundtrip) = true := by
  decide +kernel

/-- Negative Witness (`pw3_mutant_dup_returns_neg`): An arm with duplicate entries in `returns`
    is rejected by `ArmWF` (`ArmWF = false`) and fails round-trip `project_reconstruct` on distinct
    returned values for the duplicated child name. -/
def mutantDupReturnArm : Arm :=
  { tag := ":DUP"
    sig := some ⟨["FN2-ECHO", "FN2-MACHINES"], ["FN2-ECHO", "FN2-ECHO"], 4⟩
    decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
    fn := "MUTANT-DUP-RETURN" }

theorem pw3_mutant_dup_returns_neg :
    ArmWF echoKind mutantDupReturnArm false = false ∧
    let input := echoKind.tuple.map Val.sym
    let v := Val.ofList [.int 0, .int 1, .int 0, Val.nil, .sym "V1", .sym "V2"]
    project echoKind mutantDupReturnArm false
      (reconstruct echoKind mutantDupReturnArm false input v) ≠ v := by
  decide +kernel

end Fn2.MachineProofs
