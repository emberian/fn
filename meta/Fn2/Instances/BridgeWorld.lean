-- Generated from the canonical ACL2 export. Checked by the Lean kernel.
module

public import Fn2.ACL2.Translation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace Fn2.Instances.BridgeWorld
open Fn2.ACL2
def «FN2-CORE-CONTROL» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 5) «FN2-CORE»)

def «UPDATE-FN2-CONTROL-STOP» («V» : Val) («FN2-CONTROL» : Val) : Val :=
  (Native.updateNth (Val.int 4) «V» «FN2-CONTROL»)

def «UPDATE-FN2-CONTROL-STOP-REASON» («V» : Val) («FN2-CONTROL» : Val) : Val :=
  (Native.updateNth (Val.int 5) «V» «FN2-CONTROL»)

def «FN2-CONTROL-STOP» («FN2-CONTROL» : Val) : Val :=
  (Native.nth (Val.int 4) «FN2-CONTROL»)

def «=» («X» : Val) («Y» : Val) : Val :=
  (Prim.equal «X» «Y»)

def «FN2-CONTROL-RECORD-STOP» («REASON» : Val) («FN2-CONTROL» : Val) : Val :=
  (if ((«=» («FN2-CONTROL-STOP» «FN2-CONTROL») (Val.int 1))).truthy then «FN2-CONTROL» else ((fun («FN2-CONTROL» : Val) («REASON» : Val) => ((fun («FN2-CONTROL» : Val) => «FN2-CONTROL») («UPDATE-FN2-CONTROL-STOP-REASON» «REASON» «FN2-CONTROL»))) («UPDATE-FN2-CONTROL-STOP» (Val.int 1) «FN2-CONTROL») «REASON»))

def «THROW-NONEXEC-ERROR» («FN» : Val) («ACTUALS» : Val) : Val :=
  Val.nil

def «UPDATE-FN2-CORE-CONTROL» («FN2-CONTROL» : Val) («FN2-CORE» : Val) : Val :=
  (Native.updateNth (Val.int 5) «FN2-CONTROL» «FN2-CORE»)

def «FN2-CORE-STOP» («REASON» : Val) («FN2-CORE» : Val) : Val :=
  ((fun («FN2-CONTROL» : Val) («FN2-CORE» : Val) («REASON» : Val) => ((fun («FN2-CONTROL» : Val) («FN2-CORE» : Val) => ((fun («FN2-CORE» : Val) => «FN2-CORE») («UPDATE-FN2-CORE-CONTROL» «FN2-CONTROL» «FN2-CORE»))) («FN2-CONTROL-RECORD-STOP» «REASON» «FN2-CONTROL») «FN2-CORE»)) («FN2-CORE-CONTROL» «FN2-CORE») «FN2-CORE» «REASON»)

def «FN2-CORE-MACHINES» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 3) «FN2-CORE»)

def «FN2-ECHO-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 7) «FN2-CORE»)

def «FN2-MACHINES-SLOT$AI» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 1) «FN2-MACHINES»))

def «FN2-MACHINES-SLOT» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  («FN2-MACHINES-SLOT$AI» «I» «FN2-MACHINES»)

def «FN2-ECHO-RUN-FREE-CHILDREN» («ID» : Val) («SLOT» : Val) («KIND» : Val) («ORDINAL» : Val) («BUDGET» : Val) («FN2-ECHO» : Val) («FN2-MACHINES» : Val) : Val :=
  (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil Val.nil))))

def «FN2-MACHINES-ROWS» («FN2-MACHINES» : Val) : Val :=
  (Native.nth (Val.int 5) «FN2-MACHINES»)

def «FN2-ECHO-ROWS» («FN2-ECHO» : Val) : Val :=
  (Native.nth (Val.int 16) «FN2-ECHO»)

def «NOT» («P» : Val) : Val :=
  (if («P»).truthy then Val.nil else Val.t)

def «NATP» («X» : Val) : Val :=
  (if ((Prim.integerp «X»)).truthy then («NOT» (Prim.lt «X» (Val.int 0))) else Val.nil)

def «HARD-ERROR» («CTX» : Val) («STR» : Val) («ALIST» : Val) : Val :=
  Val.nil

def «FN2-MACHINE-IDP» («ID» : Val) («FN2-CORE» : Val) : Val :=
  ((fun («FN2-MACHINES» : Val) («ID» : Val) => ((fun («YES» : Val) => «YES») (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» «FN2-MACHINES»)) else Val.nil))) («FN2-CORE-MACHINES» «FN2-CORE») «ID»)

def «FN2-MACHINE-SLOT-READ-CODE» («ID» : Val) («FN2-CORE» : Val) : Val :=
  (if ((«FN2-MACHINE-IDP» «ID» «FN2-CORE»)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))

def «EQ» («X» : Val) («Y» : Val) : Val :=
  (Prim.equal «X» «Y»)

def «FN2-MACHINE-SLOT» («ID» : Val) («FN2-CORE» : Val) : Val :=
  (if ((«EQ» («FN2-MACHINE-SLOT-READ-CODE» «ID» «FN2-CORE») (Val.sym ":OK"))).truthy then ((fun («FN2-MACHINES» : Val) («ID» : Val) => ((fun («ANSWER» : Val) => «ANSWER») («FN2-MACHINES-SLOT» «ID» «FN2-MACHINES»))) («FN2-CORE-MACHINES» «FN2-CORE») «ID») else (Val.int 0))

def «FN2-MACHINES-KIND$AI» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 0) «FN2-MACHINES»))

def «FN2-MACHINES-KIND» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  («FN2-MACHINES-KIND$AI» «I» «FN2-MACHINES»)

def «FN2-MACHINE-KIND-READ-CODE» («ID» : Val) («FN2-CORE» : Val) : Val :=
  (if ((«FN2-MACHINE-IDP» «ID» «FN2-CORE»)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))

def «FN2-MACHINE-KIND» («ID» : Val) («FN2-CORE» : Val) : Val :=
  (if ((«EQ» («FN2-MACHINE-KIND-READ-CODE» «ID» «FN2-CORE») (Val.sym ":OK"))).truthy then ((fun («FN2-MACHINES» : Val) («ID» : Val) => ((fun («ANSWER» : Val) => «ANSWER») («FN2-MACHINES-KIND» «ID» «FN2-MACHINES»))) («FN2-CORE-MACHINES» «FN2-CORE») «ID») else (Val.int 0))

def «FN2-BOOT-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 19) «FN2-CORE»)

def «FN2-BOOT-ROWS» («FN2-BOOT» : Val) : Val :=
  (Native.nth (Val.int 26) «FN2-BOOT»)

def «FN2-AUTH-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 18) «FN2-CORE»)

def «FN2-AUTH-ROWS» («FN2-AUTH» : Val) : Val :=
  (Native.nth (Val.int 46) «FN2-AUTH»)

def «FN2-CNS-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 17) «FN2-CORE»)

def «FN2-CNS-ROWS» («FN2-CNS» : Val) : Val :=
  (Native.nth (Val.int 67) «FN2-CNS»)

def «FN2-CTL-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 16) «FN2-CORE»)

def «FN2-CTL-ROWS» («FN2-CTL» : Val) : Val :=
  (Native.nth (Val.int 34) «FN2-CTL»)

def «FN2-CURSOR-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 15) «FN2-CORE»)

def «FN2-CURSOR-ROWS» («FN2-CURSOR» : Val) : Val :=
  (Native.nth (Val.int 85) «FN2-CURSOR»)

def «FN2-TXN-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 14) «FN2-CORE»)

def «FN2-TXN-ROWS» («FN2-TXN» : Val) : Val :=
  (Native.nth (Val.int 30) «FN2-TXN»)

def «FN2-UPLOAD-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 13) «FN2-CORE»)

def «FN2-UPLOAD-ROWS» («FN2-UPLOAD» : Val) : Val :=
  (Native.nth (Val.int 56) «FN2-UPLOAD»)

def «FN2-CONN-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 12) «FN2-CORE»)

def «FN2-CONN-ROWS» («FN2-CONN» : Val) : Val :=
  (Native.nth (Val.int 50) «FN2-CONN»)

def «FN2-SEALER-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 11) «FN2-CORE»)

def «FN2-SEALER-ROWS» («FN2-SEALER» : Val) : Val :=
  (Native.nth (Val.int 6) «FN2-SEALER»)

def «FN2-RECOVERY-MACHINE-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 10) «FN2-CORE»)

def «FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE» : Val) : Val :=
  (Native.nth (Val.int 42) «FN2-RECOVERY-MACHINE»)

def «FN2-COMMIT-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 9) «FN2-CORE»)

def «FN2-COMMIT-ROWS» («FN2-COMMIT» : Val) : Val :=
  (Native.nth (Val.int 33) «FN2-COMMIT»)

def «FN2-SCRIBE-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 8) «FN2-CORE»)

def «FN2-SCRIBE-ROWS» («FN2-SCRIBE» : Val) : Val :=
  (Native.nth (Val.int 21) «FN2-SCRIBE»)

def «FN2-LISTENER-TABLE» («FN2-CORE» : Val) : Val :=
  (Native.nth (Val.int 6) «FN2-CORE»)

def «FN2-LISTENER-ROWS» («FN2-LISTENER» : Val) : Val :=
  (Native.nth (Val.int 19) «FN2-LISTENER»)

def «EQL» («X» : Val) («Y» : Val) : Val :=
  (Prim.equal «X» «Y»)

def «FN2-MACHINE-PHASE-READ-CODE» («ID» : Val) («FN2-CORE» : Val) : Val :=
  (if ((«NOT» («FN2-MACHINE-IDP» «ID» «FN2-CORE»))).truthy then (Val.sym ":BOUNDS") else ((fun («SLOT» : Val) («FN2-CORE» : Val) («ID» : Val) => ((fun («CASE-DO-NOT-USE-ELSEWHERE» : Val) («SLOT» : Val) («FN2-CORE» : Val) => (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 0))).truthy then ((fun («FN2-LISTENER» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-LISTENER-ROWS» «FN2-LISTENER»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-LISTENER-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 1))).truthy then ((fun («FN2-ECHO» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-ECHO-ROWS» «FN2-ECHO»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-ECHO-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 2))).truthy then ((fun («FN2-SCRIBE» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-SCRIBE-ROWS» «FN2-SCRIBE»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-SCRIBE-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 3))).truthy then ((fun («FN2-COMMIT» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-COMMIT-ROWS» «FN2-COMMIT»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-COMMIT-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 4))).truthy then ((fun («FN2-RECOVERY-MACHINE» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-RECOVERY-MACHINE-ROWS» «FN2-RECOVERY-MACHINE»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 5))).truthy then ((fun («FN2-SEALER» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-SEALER-ROWS» «FN2-SEALER»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-SEALER-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 6))).truthy then ((fun («FN2-CONN» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-CONN-ROWS» «FN2-CONN»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-CONN-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 7))).truthy then ((fun («FN2-UPLOAD» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-UPLOAD-ROWS» «FN2-UPLOAD»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-UPLOAD-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 8))).truthy then ((fun («FN2-TXN» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-TXN-ROWS» «FN2-TXN»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-TXN-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 9))).truthy then ((fun («FN2-CURSOR» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-CURSOR-ROWS» «FN2-CURSOR»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-CURSOR-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 10))).truthy then ((fun («FN2-CTL» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-CTL-ROWS» «FN2-CTL»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-CTL-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 11))).truthy then ((fun («FN2-CNS» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-CNS-ROWS» «FN2-CNS»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-CNS-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 12))).truthy then ((fun («FN2-AUTH» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-AUTH-ROWS» «FN2-AUTH»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-AUTH-TABLE» «FN2-CORE») «SLOT») else (if ((«EQL» «CASE-DO-NOT-USE-ELSEWHERE» (Val.int 13))).truthy then ((fun («FN2-BOOT» : Val) («SLOT» : Val) => ((fun («ANSWER» : Val) => «ANSWER») (if ((if ((«NATP» «SLOT»)).truthy then (Prim.lt «SLOT» («FN2-BOOT-ROWS» «FN2-BOOT»)) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")))) («FN2-BOOT-TABLE» «FN2-CORE») «SLOT») else (Val.sym ":KIND")))))))))))))))) («FN2-MACHINE-KIND» «ID» «FN2-CORE») «SLOT» «FN2-CORE»)) («FN2-MACHINE-SLOT» «ID» «FN2-CORE») «FN2-CORE» «ID»))

def «FN2-ECHO-SNAPSHOT-READ-CODE» («ID» : Val) («FN2-CORE» : Val) : Val :=
  ((fun («CODE» : Val) («FN2-CORE» : Val) («ID» : Val) => (if ((«NOT» («EQ» «CODE» (Val.sym ":OK")))).truthy then «CODE» else (if ((Prim.equal («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 1))).truthy then (Val.sym ":OK") else (Val.sym ":KIND")))) («FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE») «FN2-CORE» «ID»)

def «FN2-ECHO-RUN-FREE» («ID» : Val) («BUDGET» : Val) («FN2-CORE» : Val) : Val :=
  (if ((«EQ» («FN2-ECHO-SNAPSHOT-READ-CODE» «ID» «FN2-CORE») (Val.sym ":OK"))).truthy then ((fun («FN2-ECHO» : Val) («FN2-MACHINES» : Val) («FN2-CONTROL» : Val) («FN2-CORE» : Val) («BUDGET» : Val) («ID» : Val) => ((fun («MV» : Val) («FN2-CORE» : Val) => ((fun («BYTES» : Val) («STEPS» : Val) («DESCRIPTORS» : Val) («RUNNABLE» : Val) («FN2-CONTROL» : Val) («FN2-CORE» : Val) => ((fun («FN2-CORE» : Val) («RUNNABLE» : Val) («DESCRIPTORS» : Val) («STEPS» : Val) («BYTES» : Val) => (Val.cons «BYTES» (Val.cons «STEPS» (Val.cons «DESCRIPTORS» (Val.cons «RUNNABLE» (Val.cons «FN2-CORE» Val.nil)))))) («UPDATE-FN2-CORE-CONTROL» «FN2-CONTROL» «FN2-CORE») «RUNNABLE» «DESCRIPTORS» «STEPS» «BYTES»)) (Native.nth (Val.int 0) «MV») (Native.nth (Val.int 1) «MV») (Native.nth (Val.int 2) «MV») (Native.nth (Val.int 3) «MV») (Native.nth (Val.int 4) «MV») «FN2-CORE»)) ((fun («SLOT» : Val) («FN2-CONTROL» : Val) («BUDGET» : Val) («FN2-MACHINES» : Val) («ID» : Val) («FN2-ECHO» : Val) => (if ((if ((«NATP» «SLOT»)).truthy then (if ((Prim.lt «SLOT» («FN2-ECHO-ROWS» «FN2-ECHO»))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» «FN2-MACHINES»)) else Val.nil) else Val.nil) else Val.nil)).truthy then ((fun («MV» : Val) («FN2-CONTROL» : Val) => ((fun («BYTES» : Val) («STEPS» : Val) («DESCRIPTORS» : Val) («RUNNABLE» : Val) («FN2-CONTROL» : Val) => (Val.cons «BYTES» (Val.cons «STEPS» (Val.cons «DESCRIPTORS» (Val.cons «RUNNABLE» (Val.cons «FN2-CONTROL» Val.nil)))))) (Native.nth (Val.int 0) «MV») (Native.nth (Val.int 1) «MV») (Native.nth (Val.int 2) «MV») (Native.nth (Val.int 3) «MV») «FN2-CONTROL»)) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» «SLOT» (Val.int 1) (Val.int 0) «BUDGET» «FN2-ECHO» «FN2-MACHINES») «FN2-CONTROL») else ((fun («FN2-CONTROL» : Val) => (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons «FN2-CONTROL» Val.nil)))))) («FN2-CONTROL-RECORD-STOP» (Val.int 15) «FN2-CONTROL»)))) (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» «FN2-MACHINES»)) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» «FN2-MACHINES») else (Val.int 4294967295)) «FN2-CONTROL» «BUDGET» «FN2-MACHINES» «ID» «FN2-ECHO») «FN2-CORE»)) («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE») («FN2-CORE-CONTROL» «FN2-CORE») «FN2-CORE» «BUDGET» «ID») else ((fun («FN2-CORE» : Val) => (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons «FN2-CORE» Val.nil)))))) («FN2-CORE-STOP» (Val.int 15) «FN2-CORE»)))

def «FN2-ECHO-PHASE$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 0) «FN2-ECHO»))

def «FN2-ECHO-PHASE» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-PHASE$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-GENERATION$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 1) «FN2-ECHO»))

def «FN2-ECHO-GENERATION» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-GENERATION$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-PRINCIPAL-SLOT$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 2) «FN2-ECHO»))

def «FN2-ECHO-PRINCIPAL-SLOT» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-PRINCIPAL-SLOT$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-ACCOUNT-REF$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 3) «FN2-ECHO»))

def «FN2-ECHO-ACCOUNT-REF» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-ACCOUNT-REF$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-DEADLINE$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 4) «FN2-ECHO»))

def «FN2-ECHO-DEADLINE» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-DEADLINE$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-CAP-INDEX$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 5) «FN2-ECHO»))

def «FN2-ECHO-CAP-INDEX» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-CAP-INDEX$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-CAP-NONCE$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 6) «FN2-ECHO»))

def «FN2-ECHO-CAP-NONCE» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-CAP-NONCE$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-POOL-SLOT$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 7) «FN2-ECHO»))

def «FN2-ECHO-POOL-SLOT» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-POOL-SLOT$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-POOL-GEN$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 8) «FN2-ECHO»))

def «FN2-ECHO-POOL-GEN» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-POOL-GEN$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-OFF$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 9) «FN2-ECHO»))

def «FN2-ECHO-OFF» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-OFF$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-LENGTH$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 10) «FN2-ECHO»))

def «FN2-ECHO-LENGTH» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-LENGTH$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-PENDING$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 11) «FN2-ECHO»))

def «FN2-ECHO-PENDING» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-PENDING$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-BORROWS$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 12) «FN2-ECHO»))

def «FN2-ECHO-BORROWS» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-BORROWS$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-NEXT-FREE$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 13) «FN2-ECHO»))

def «FN2-ECHO-NEXT-FREE» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-NEXT-FREE$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-STOPPED$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 14) «FN2-ECHO»))

def «FN2-ECHO-STOPPED» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-STOPPED$AI» «I» «FN2-ECHO»)

def «FN2-ECHO-MODE$AI» («I» : Val) («FN2-ECHO» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 15) «FN2-ECHO»))

def «FN2-ECHO-MODE» («I» : Val) («FN2-ECHO» : Val) : Val :=
  («FN2-ECHO-MODE$AI» «I» «FN2-ECHO»)

def «FN2-MACHINES-READY-PREV$AI» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 2) «FN2-MACHINES»))

def «FN2-MACHINES-READY-PREV» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  («FN2-MACHINES-READY-PREV$AI» «I» «FN2-MACHINES»)

def «FN2-MACHINES-READY-NEXT$AI» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 3) «FN2-MACHINES»))

def «FN2-MACHINES-READY-NEXT» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  («FN2-MACHINES-READY-NEXT$AI» «I» «FN2-MACHINES»)

def «FN2-MACHINES-WAIT-REASON$AI» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  (Native.nth «I» (Native.nth (Val.int 4) «FN2-MACHINES»))

def «FN2-MACHINES-WAIT-REASON» («I» : Val) («FN2-MACHINES» : Val) : Val :=
  («FN2-MACHINES-WAIT-REASON$AI» «I» «FN2-MACHINES»)

def fns : Fns
  | "FN2-CORE-CONTROL", [«FN2-CORE»] => some («FN2-CORE-CONTROL» «FN2-CORE»)
  | "UPDATE-FN2-CONTROL-STOP", [«V», «FN2-CONTROL»] => some («UPDATE-FN2-CONTROL-STOP» «V» «FN2-CONTROL»)
  | "UPDATE-FN2-CONTROL-STOP-REASON", [«V», «FN2-CONTROL»] => some («UPDATE-FN2-CONTROL-STOP-REASON» «V» «FN2-CONTROL»)
  | "FN2-CONTROL-STOP", [«FN2-CONTROL»] => some («FN2-CONTROL-STOP» «FN2-CONTROL»)
  | "=", [«X», «Y»] => some («=» «X» «Y»)
  | "FN2-CONTROL-RECORD-STOP", [«REASON», «FN2-CONTROL»] => some («FN2-CONTROL-RECORD-STOP» «REASON» «FN2-CONTROL»)
  | "THROW-NONEXEC-ERROR", [«FN», «ACTUALS»] => some («THROW-NONEXEC-ERROR» «FN» «ACTUALS»)
  | "UPDATE-FN2-CORE-CONTROL", [«FN2-CONTROL», «FN2-CORE»] => some («UPDATE-FN2-CORE-CONTROL» «FN2-CONTROL» «FN2-CORE»)
  | "FN2-CORE-STOP", [«REASON», «FN2-CORE»] => some («FN2-CORE-STOP» «REASON» «FN2-CORE»)
  | "FN2-CORE-MACHINES", [«FN2-CORE»] => some («FN2-CORE-MACHINES» «FN2-CORE»)
  | "FN2-ECHO-TABLE", [«FN2-CORE»] => some («FN2-ECHO-TABLE» «FN2-CORE»)
  | "FN2-MACHINES-SLOT$AI", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-SLOT$AI» «I» «FN2-MACHINES»)
  | "FN2-MACHINES-SLOT", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-SLOT» «I» «FN2-MACHINES»)
  | "FN2-ECHO-RUN-FREE-CHILDREN", [«ID», «SLOT», «KIND», «ORDINAL», «BUDGET», «FN2-ECHO», «FN2-MACHINES»] => some («FN2-ECHO-RUN-FREE-CHILDREN» «ID» «SLOT» «KIND» «ORDINAL» «BUDGET» «FN2-ECHO» «FN2-MACHINES»)
  | "FN2-MACHINES-ROWS", [«FN2-MACHINES»] => some («FN2-MACHINES-ROWS» «FN2-MACHINES»)
  | "FN2-ECHO-ROWS", [«FN2-ECHO»] => some («FN2-ECHO-ROWS» «FN2-ECHO»)
  | "NOT", [«P»] => some («NOT» «P»)
  | "NATP", [«X»] => some («NATP» «X»)
  | "HARD-ERROR", [«CTX», «STR», «ALIST»] => some («HARD-ERROR» «CTX» «STR» «ALIST»)
  | "FN2-MACHINE-IDP", [«ID», «FN2-CORE»] => some («FN2-MACHINE-IDP» «ID» «FN2-CORE»)
  | "FN2-MACHINE-SLOT-READ-CODE", [«ID», «FN2-CORE»] => some («FN2-MACHINE-SLOT-READ-CODE» «ID» «FN2-CORE»)
  | "EQ", [«X», «Y»] => some («EQ» «X» «Y»)
  | "FN2-MACHINE-SLOT", [«ID», «FN2-CORE»] => some («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)
  | "FN2-MACHINES-KIND$AI", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-KIND$AI» «I» «FN2-MACHINES»)
  | "FN2-MACHINES-KIND", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-KIND» «I» «FN2-MACHINES»)
  | "FN2-MACHINE-KIND-READ-CODE", [«ID», «FN2-CORE»] => some («FN2-MACHINE-KIND-READ-CODE» «ID» «FN2-CORE»)
  | "FN2-MACHINE-KIND", [«ID», «FN2-CORE»] => some («FN2-MACHINE-KIND» «ID» «FN2-CORE»)
  | "FN2-BOOT-TABLE", [«FN2-CORE»] => some («FN2-BOOT-TABLE» «FN2-CORE»)
  | "FN2-BOOT-ROWS", [«FN2-BOOT»] => some («FN2-BOOT-ROWS» «FN2-BOOT»)
  | "FN2-AUTH-TABLE", [«FN2-CORE»] => some («FN2-AUTH-TABLE» «FN2-CORE»)
  | "FN2-AUTH-ROWS", [«FN2-AUTH»] => some («FN2-AUTH-ROWS» «FN2-AUTH»)
  | "FN2-CNS-TABLE", [«FN2-CORE»] => some («FN2-CNS-TABLE» «FN2-CORE»)
  | "FN2-CNS-ROWS", [«FN2-CNS»] => some («FN2-CNS-ROWS» «FN2-CNS»)
  | "FN2-CTL-TABLE", [«FN2-CORE»] => some («FN2-CTL-TABLE» «FN2-CORE»)
  | "FN2-CTL-ROWS", [«FN2-CTL»] => some («FN2-CTL-ROWS» «FN2-CTL»)
  | "FN2-CURSOR-TABLE", [«FN2-CORE»] => some («FN2-CURSOR-TABLE» «FN2-CORE»)
  | "FN2-CURSOR-ROWS", [«FN2-CURSOR»] => some («FN2-CURSOR-ROWS» «FN2-CURSOR»)
  | "FN2-TXN-TABLE", [«FN2-CORE»] => some («FN2-TXN-TABLE» «FN2-CORE»)
  | "FN2-TXN-ROWS", [«FN2-TXN»] => some («FN2-TXN-ROWS» «FN2-TXN»)
  | "FN2-UPLOAD-TABLE", [«FN2-CORE»] => some («FN2-UPLOAD-TABLE» «FN2-CORE»)
  | "FN2-UPLOAD-ROWS", [«FN2-UPLOAD»] => some («FN2-UPLOAD-ROWS» «FN2-UPLOAD»)
  | "FN2-CONN-TABLE", [«FN2-CORE»] => some («FN2-CONN-TABLE» «FN2-CORE»)
  | "FN2-CONN-ROWS", [«FN2-CONN»] => some («FN2-CONN-ROWS» «FN2-CONN»)
  | "FN2-SEALER-TABLE", [«FN2-CORE»] => some («FN2-SEALER-TABLE» «FN2-CORE»)
  | "FN2-SEALER-ROWS", [«FN2-SEALER»] => some («FN2-SEALER-ROWS» «FN2-SEALER»)
  | "FN2-RECOVERY-MACHINE-TABLE", [«FN2-CORE»] => some («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»)
  | "FN2-RECOVERY-MACHINE-ROWS", [«FN2-RECOVERY-MACHINE»] => some («FN2-RECOVERY-MACHINE-ROWS» «FN2-RECOVERY-MACHINE»)
  | "FN2-COMMIT-TABLE", [«FN2-CORE»] => some («FN2-COMMIT-TABLE» «FN2-CORE»)
  | "FN2-COMMIT-ROWS", [«FN2-COMMIT»] => some («FN2-COMMIT-ROWS» «FN2-COMMIT»)
  | "FN2-SCRIBE-TABLE", [«FN2-CORE»] => some («FN2-SCRIBE-TABLE» «FN2-CORE»)
  | "FN2-SCRIBE-ROWS", [«FN2-SCRIBE»] => some («FN2-SCRIBE-ROWS» «FN2-SCRIBE»)
  | "FN2-LISTENER-TABLE", [«FN2-CORE»] => some («FN2-LISTENER-TABLE» «FN2-CORE»)
  | "FN2-LISTENER-ROWS", [«FN2-LISTENER»] => some («FN2-LISTENER-ROWS» «FN2-LISTENER»)
  | "EQL", [«X», «Y»] => some («EQL» «X» «Y»)
  | "FN2-MACHINE-PHASE-READ-CODE", [«ID», «FN2-CORE»] => some («FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE»)
  | "FN2-ECHO-SNAPSHOT-READ-CODE", [«ID», «FN2-CORE»] => some («FN2-ECHO-SNAPSHOT-READ-CODE» «ID» «FN2-CORE»)
  | "FN2-ECHO-RUN-FREE", [«ID», «BUDGET», «FN2-CORE»] => some («FN2-ECHO-RUN-FREE» «ID» «BUDGET» «FN2-CORE»)
  | "FN2-ECHO-PHASE$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-PHASE$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-PHASE", [«I», «FN2-ECHO»] => some («FN2-ECHO-PHASE» «I» «FN2-ECHO»)
  | "FN2-ECHO-GENERATION$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-GENERATION$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-GENERATION", [«I», «FN2-ECHO»] => some («FN2-ECHO-GENERATION» «I» «FN2-ECHO»)
  | "FN2-ECHO-PRINCIPAL-SLOT$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-PRINCIPAL-SLOT$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-PRINCIPAL-SLOT", [«I», «FN2-ECHO»] => some («FN2-ECHO-PRINCIPAL-SLOT» «I» «FN2-ECHO»)
  | "FN2-ECHO-ACCOUNT-REF$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-ACCOUNT-REF$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-ACCOUNT-REF", [«I», «FN2-ECHO»] => some («FN2-ECHO-ACCOUNT-REF» «I» «FN2-ECHO»)
  | "FN2-ECHO-DEADLINE$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-DEADLINE$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-DEADLINE", [«I», «FN2-ECHO»] => some («FN2-ECHO-DEADLINE» «I» «FN2-ECHO»)
  | "FN2-ECHO-CAP-INDEX$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-CAP-INDEX$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-CAP-INDEX", [«I», «FN2-ECHO»] => some («FN2-ECHO-CAP-INDEX» «I» «FN2-ECHO»)
  | "FN2-ECHO-CAP-NONCE$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-CAP-NONCE$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-CAP-NONCE", [«I», «FN2-ECHO»] => some («FN2-ECHO-CAP-NONCE» «I» «FN2-ECHO»)
  | "FN2-ECHO-POOL-SLOT$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-POOL-SLOT$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-POOL-SLOT", [«I», «FN2-ECHO»] => some («FN2-ECHO-POOL-SLOT» «I» «FN2-ECHO»)
  | "FN2-ECHO-POOL-GEN$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-POOL-GEN$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-POOL-GEN", [«I», «FN2-ECHO»] => some («FN2-ECHO-POOL-GEN» «I» «FN2-ECHO»)
  | "FN2-ECHO-OFF$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-OFF$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-OFF", [«I», «FN2-ECHO»] => some («FN2-ECHO-OFF» «I» «FN2-ECHO»)
  | "FN2-ECHO-LENGTH$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-LENGTH$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-LENGTH", [«I», «FN2-ECHO»] => some («FN2-ECHO-LENGTH» «I» «FN2-ECHO»)
  | "FN2-ECHO-PENDING$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-PENDING$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-PENDING", [«I», «FN2-ECHO»] => some («FN2-ECHO-PENDING» «I» «FN2-ECHO»)
  | "FN2-ECHO-BORROWS$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-BORROWS$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-BORROWS", [«I», «FN2-ECHO»] => some («FN2-ECHO-BORROWS» «I» «FN2-ECHO»)
  | "FN2-ECHO-NEXT-FREE$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-NEXT-FREE$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-NEXT-FREE", [«I», «FN2-ECHO»] => some («FN2-ECHO-NEXT-FREE» «I» «FN2-ECHO»)
  | "FN2-ECHO-STOPPED$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-STOPPED$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-STOPPED", [«I», «FN2-ECHO»] => some («FN2-ECHO-STOPPED» «I» «FN2-ECHO»)
  | "FN2-ECHO-MODE$AI", [«I», «FN2-ECHO»] => some («FN2-ECHO-MODE$AI» «I» «FN2-ECHO»)
  | "FN2-ECHO-MODE", [«I», «FN2-ECHO»] => some («FN2-ECHO-MODE» «I» «FN2-ECHO»)
  | "FN2-MACHINES-READY-PREV$AI", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-READY-PREV$AI» «I» «FN2-MACHINES»)
  | "FN2-MACHINES-READY-PREV", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-READY-PREV» «I» «FN2-MACHINES»)
  | "FN2-MACHINES-READY-NEXT$AI", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-READY-NEXT$AI» «I» «FN2-MACHINES»)
  | "FN2-MACHINES-READY-NEXT", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-READY-NEXT» «I» «FN2-MACHINES»)
  | "FN2-MACHINES-WAIT-REASON$AI", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-WAIT-REASON$AI» «I» «FN2-MACHINES»)
  | "FN2-MACHINES-WAIT-REASON", [«I», «FN2-MACHINES»] => some («FN2-MACHINES-WAIT-REASON» «I» «FN2-MACHINES»)
  | _, _ => none
end Fn2.Instances.BridgeWorld

end
