-- Template for the canonical echo/free certificate; emit_certificate.py instantiates its layout.
import Fn2.Arms.Core
import Fn2.Instances.BridgeKinds
import Fn2.Instances.BridgeTranslation
namespace Fn2.Arms.Validation
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core
open Fn2.Instances.BridgeWorld Fn2.Instances.BridgeKinds
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
theorem snapshot_parts (id core : Val)
    (h : «FN2-ECHO-SNAPSHOT-READ-CODE» id core = .sym ":OK") :
    «FN2-MACHINE-PHASE-READ-CODE» id core = .sym ":OK" ∧
    «FN2-MACHINE-KIND» id core = .int 1 := by
  unfold «FN2-ECHO-SNAPSHOT-READ-CODE» at h
  dsimp only at h
  by_cases hp : «FN2-MACHINE-PHASE-READ-CODE» id core = .sym ":OK"
  · simp [«NOT», «EQ», Prim.equal, hp] at h
    exact ⟨hp, h⟩
  · simp [«NOT», «EQ», Prim.equal, hp] at h

 theorem snapshot_bounds (id core : Val)
    (h : «FN2-ECHO-SNAPSHOT-READ-CODE» id core = .sym ":OK") :
    («NATP» id).truthy = true ∧
    (Prim.lt id («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» core))).truthy = true ∧
    («NATP» («FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core))).truthy = true ∧
    (Prim.lt («FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core))
      («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» core))).truthy = true := by
  obtain ⟨hp, hk⟩ := snapshot_parts id core h
  have hi : («FN2-MACHINE-IDP» id core).truthy = true := by
    by_cases hi : («FN2-MACHINE-IDP» id core).truthy = true
    · exact hi
    · simp [«FN2-MACHINE-PHASE-READ-CODE», «NOT», hi] at hp
  have hid : («NATP» id).truthy = true ∧
      (Prim.lt id («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» core))).truthy = true := by
    simpa [«FN2-MACHINE-IDP», Fn2.Arms.Val.truthy_ite] using hi
  have hs : «FN2-MACHINE-SLOT» id core = «FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core) := by
    simp [«FN2-MACHINE-SLOT», «FN2-MACHINE-SLOT-READ-CODE», hi, «EQ», Prim.equal]
  simp [«FN2-MACHINE-PHASE-READ-CODE», «NOT», hi, hk, «EQL», Prim.equal,
    Val.ofBool, hs] at hp
  exact ⟨hid.1, hid.2, hp⟩

theorem runCore_shape (w : World) (tuple : List String) (k : Kind) (a : Arm)
    (id budget : Val) (kids : List Val) (fuel : Nat) (hlen : kids.length = tuple.length) :
    runCore w tuple k a false [id, budget, Val.ofList kids] fuel =
    (do
      let code ← callFn w (k.name ++ "-SNAPSHOT-READ-CODE") [id, Val.ofList kids]
      if code == Val.sym ":OK" then do
        let slot ← callFn w "FN2-MACHINE-SLOT" [id, Val.ofList kids]
        let kind ← const w ("*" ++ k.name ++ "-KIND*")
        let v ← runArm (coreWorld w tuple) (coreKind k tuple) a false
          ([id, slot, kind, ordOf w k, budget] ++ kids) fuel
        finish false tuple v
      else refusedEntry w tuple false kids) := by
  simp [runCore, nCore, toList_ofList', hlen]

def echoKind : Kind := kinds.head!
def echoFree : Arm := echoKind.arms.head!
theorem callFn_core_plain (w : World) (tuple : List String) (f : String) (args : List Val)
    (h : f.endsWith "@CORE" = false) :
    callFn (coreWorld w tuple) f args = callFn w f args := by
  simp [callFn, coreWorld, coreFns, h]

def echoRead (id slot own dir : Val) : String → Val
  | "PHASE" => «FN2-ECHO-PHASE» slot own
  | "GENERATION" => «FN2-ECHO-GENERATION» slot own
  | "PRINCIPAL-SLOT" => «FN2-ECHO-PRINCIPAL-SLOT» slot own
  | "ACCOUNT-REF" => «FN2-ECHO-ACCOUNT-REF» slot own
  | "READY-PREV" => «FN2-MACHINES-READY-PREV» id dir
  | "READY-NEXT" => «FN2-MACHINES-READY-NEXT» id dir
  | "WAIT-REASON" => «FN2-MACHINES-WAIT-REASON» id dir
  | "DEADLINE" => «FN2-ECHO-DEADLINE» slot own
  | "CAP-INDEX" => «FN2-ECHO-CAP-INDEX» slot own
  | "CAP-NONCE" => «FN2-ECHO-CAP-NONCE» slot own
  | "POOL-SLOT" => «FN2-ECHO-POOL-SLOT» slot own
  | "POOL-GEN" => «FN2-ECHO-POOL-GEN» slot own
  | "OFF" => «FN2-ECHO-OFF» slot own
  | "LENGTH" => «FN2-ECHO-LENGTH» slot own
  | "PENDING" => «FN2-ECHO-PENDING» slot own
  | "BORROWS" => «FN2-ECHO-BORROWS» slot own
  | "NEXT-FREE" => «FN2-ECHO-NEXT-FREE» slot own
  | "STOPPED" => «FN2-ECHO-STOPPED» slot own
  | "MODE" => «FN2-ECHO-MODE» slot own
  | _ => Val.nil


theorem echo_row_reads (id slot : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
  rowReads (coreWorld world coreTuple) (coreKind echoKind coreTuple)
    (coreTuple.zip [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) id slot = .ok [("ROW-PHASE", «FN2-ECHO-PHASE» slot c7), ("ROW-GENERATION", «FN2-ECHO-GENERATION» slot c7), ("ROW-PRINCIPAL-SLOT", «FN2-ECHO-PRINCIPAL-SLOT» slot c7), ("ROW-ACCOUNT-REF", «FN2-ECHO-ACCOUNT-REF» slot c7), ("ROW-READY-PREV", «FN2-MACHINES-READY-PREV» id c3), ("ROW-READY-NEXT", «FN2-MACHINES-READY-NEXT» id c3), ("ROW-WAIT-REASON", «FN2-MACHINES-WAIT-REASON» id c3), ("ROW-DEADLINE", «FN2-ECHO-DEADLINE» slot c7), ("ROW-CAP-INDEX", «FN2-ECHO-CAP-INDEX» slot c7), ("ROW-CAP-NONCE", «FN2-ECHO-CAP-NONCE» slot c7), ("ROW-POOL-SLOT", «FN2-ECHO-POOL-SLOT» slot c7), ("ROW-POOL-GEN", «FN2-ECHO-POOL-GEN» slot c7), ("ROW-OFF", «FN2-ECHO-OFF» slot c7), ("ROW-LENGTH", «FN2-ECHO-LENGTH» slot c7), ("ROW-PENDING", «FN2-ECHO-PENDING» slot c7), ("ROW-BORROWS", «FN2-ECHO-BORROWS» slot c7), ("ROW-NEXT-FREE", «FN2-ECHO-NEXT-FREE» slot c7), ("ROW-STOPPED", «FN2-ECHO-STOPPED» slot c7), ("ROW-MODE", «FN2-ECHO-MODE» slot c7)] := by
  apply rowReads_eq (coreWorld world coreTuple) (coreKind echoKind coreTuple) _ id slot c7 c3
    (by rfl) (by rfl) (echoRead id slot c7 c3)
  intro c hc
  change c ∈ ["PHASE", "GENERATION", "PRINCIPAL-SLOT", "ACCOUNT-REF", "READY-PREV", "READY-NEXT", "WAIT-REASON", "DEADLINE", "CAP-INDEX", "CAP-NONCE", "POOL-SLOT", "POOL-GEN", "OFF", "LENGTH", "PENDING", "BORROWS", "NEXT-FREE", "STOPPED", "MODE"] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [callFn_core_plain _ _ _ _ (by decide +kernel)]
    rfl


theorem echo_idle_run (id slot kind ordinal budget : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
  runArm (coreWorld world coreTuple) (coreKind echoKind coreTuple) echoFree false
    ([id, slot, kind, ordinal, budget] ++ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) 1 =
    .ok (Val.ofList ([.int 0, .int 1, .int 0, Val.nil] ++ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56])) := by
  have hr : echoFree.read = .ok ⟨[], [], [.idle]⟩ := by rfl
  unfold runArm
  simp only [coreKind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_append,
    List.length_cons, List.length_nil]
  have hl : coreTuple.length = 57 := by rfl
  simp only [hl]
  simp only [show (5 + 57 != 5 + 57) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  change (do
    let reads ← rowReads (coreWorld world coreTuple) (coreKind echoKind coreTuple)
      (coreTuple.zip [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) id slot
    let d ← echoFree.read
    let f : Frame := { kind := coreKind echoKind coreTuple, observe := false, refusal := d.onRefusal, base := [("ID",id),("SLOT",slot),("KIND",kind),("ORDINAL",ordinal),("BUDGET",budget)] }
    match ← run (coreWorld world coreTuple) f 1
      { stobjs := coreTuple.zip [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56], vars := reads ++ f.base } d.steps with
    | .done v => pure v
    | .again _ => throw ":repeat-next outside a :repeat") = _
  rw [echo_row_reads]
  simp only [except_ok_bind, hr]
  rfl


theorem echo_free_interpreter (id budget : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
  runCore world coreTuple echoKind echoFree false [id, budget, Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]] 1 =
    (if «FN2-ECHO-SNAPSHOT-READ-CODE» id (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) == .sym ":OK" then
       .ok (Val.ofList [.int 0, .int 1, .int 0, Val.nil, Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]])
     else .ok (Val.ofList [.int 0, .int 1, .int 0, Val.nil, «FN2-CORE-STOP» (.int 15) (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56])])) := by
  rw [runCore_shape _ _ _ _ _ _ _ _ (by rfl)]
  have hcall (i c : Val) : callFn world (echoKind.name ++ "-SNAPSHOT-READ-CODE") [i,c] =
      .ok («FN2-ECHO-SNAPSHOT-READ-CODE» i c) := by rfl
  rw [hcall]
  simp only [except_ok_bind]
  split
  · have hslot (i c : Val) : callFn world "FN2-MACHINE-SLOT" [i,c] =
        .ok («FN2-MACHINE-SLOT» i c) := by rfl
    rw [hslot]
    simp only [except_ok_bind]
    have hk : const world ("*" ++ echoKind.name ++ "-KIND*") = .ok (.int 1) := by rfl
    rw [hk]
    simp only [except_ok_bind]
    rw [echo_idle_run]
    rfl
  · rfl
theorem echo_emitted_success (id budget core : Val)
    (hself : «UPDATE-FN2-CORE-CONTROL» («FN2-CORE-CONTROL» core) core = core)
    (h : «FN2-ECHO-SNAPSHOT-READ-CODE» id core = .sym ":OK") :
    «FN2-ECHO-RUN-FREE» id budget core = Val.ofList [.int 0, .int 1, .int 0, Val.nil, core] := by
  obtain ⟨hi, hr, hs, hb⟩ := snapshot_bounds id core h
  simp [«FN2-ECHO-RUN-FREE», «EQ», Prim.equal, h, hi, hr, hs, hb,
    «FN2-ECHO-RUN-FREE-CHILDREN», Native.nth, Native.nthN, Val.nfix,
    Val.toInt, hself, Val.ofList]

theorem echo_emitted_refused (id budget core : Val)
    (h : «FN2-ECHO-SNAPSHOT-READ-CODE» id core ≠ .sym ":OK") :
    «FN2-ECHO-RUN-FREE» id budget core =
      Val.ofList [.int 0, .int 1, .int 0, Val.nil, «FN2-CORE-STOP» (.int 15) core] := by
  simp [«FN2-ECHO-RUN-FREE», «EQ», Prim.equal, h, Val.ofList]

theorem echo_free_core_eq (id budget : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
    runCore world coreTuple echoKind echoFree false [id, budget, Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]] 1 =
      .ok («FN2-ECHO-RUN-FREE» id budget (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56])) := by
  rw [echo_free_interpreter]
  by_cases h : «FN2-ECHO-SNAPSHOT-READ-CODE» id (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) = .sym ":OK"
  · rw [echo_emitted_success id budget _ (by rfl) h]
    simp only [h, beq_self_eq_true, ↓reduceIte]
  · rw [echo_emitted_refused id budget _ h]
    simp only [beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, ↓reduceIte]

/-- Every child is quantified. No core child is omitted by the narrowed arm
signature, including the children the arm never reads. -/
def CoreImage := Fin 57 → Val

def image (kids : CoreImage) : Val := Val.ofList (List.ofFn kids)

theorem echo_free_whole_core (id budget : Val) (kids : CoreImage) :
    runCore world coreTuple echoKind echoFree false [id, budget, image kids] 1 =
      .ok («FN2-ECHO-RUN-FREE» id budget (image kids)) := by
  simpa only [image, List.ofFn_succ, List.ofFn_zero] using
    (echo_free_core_eq id budget (kids ⟨0, by decide⟩) (kids ⟨1, by decide⟩) (kids ⟨2, by decide⟩) (kids ⟨3, by decide⟩) (kids ⟨4, by decide⟩) (kids ⟨5, by decide⟩) (kids ⟨6, by decide⟩) (kids ⟨7, by decide⟩) (kids ⟨8, by decide⟩) (kids ⟨9, by decide⟩) (kids ⟨10, by decide⟩) (kids ⟨11, by decide⟩) (kids ⟨12, by decide⟩) (kids ⟨13, by decide⟩) (kids ⟨14, by decide⟩) (kids ⟨15, by decide⟩) (kids ⟨16, by decide⟩) (kids ⟨17, by decide⟩) (kids ⟨18, by decide⟩) (kids ⟨19, by decide⟩) (kids ⟨20, by decide⟩) (kids ⟨21, by decide⟩) (kids ⟨22, by decide⟩) (kids ⟨23, by decide⟩) (kids ⟨24, by decide⟩) (kids ⟨25, by decide⟩) (kids ⟨26, by decide⟩) (kids ⟨27, by decide⟩) (kids ⟨28, by decide⟩) (kids ⟨29, by decide⟩) (kids ⟨30, by decide⟩) (kids ⟨31, by decide⟩) (kids ⟨32, by decide⟩) (kids ⟨33, by decide⟩) (kids ⟨34, by decide⟩) (kids ⟨35, by decide⟩) (kids ⟨36, by decide⟩) (kids ⟨37, by decide⟩) (kids ⟨38, by decide⟩) (kids ⟨39, by decide⟩) (kids ⟨40, by decide⟩) (kids ⟨41, by decide⟩) (kids ⟨42, by decide⟩) (kids ⟨43, by decide⟩) (kids ⟨44, by decide⟩) (kids ⟨45, by decide⟩) (kids ⟨46, by decide⟩) (kids ⟨47, by decide⟩) (kids ⟨48, by decide⟩) (kids ⟨49, by decide⟩) (kids ⟨50, by decide⟩) (kids ⟨51, by decide⟩) (kids ⟨52, by decide⟩) (kids ⟨53, by decide⟩) (kids ⟨54, by decide⟩) (kids ⟨55, by decide⟩) (kids ⟨56, by decide⟩))

/-- Successful interpretation exists; this is not a success implication.
The equality includes all four result values and the entire returned core,
for every input and every represented environment, including refused entry. -/
theorem echo_free_certificate (id budget : Val) (kids : CoreImage) :
    ∃ fuel result,
      runCore world coreTuple echoKind echoFree false [id, budget, image kids] fuel = .ok result ∧
      result = «FN2-ECHO-RUN-FREE» id budget (image kids) :=
  ⟨1, _, echo_free_whole_core id budget kids, rfl⟩

/-- The narrowed signature is checked independently of the whole-core result. -/
theorem echo_free_signature : echoFree.sig = some ⟨["FN2-ECHO", "FN2-MACHINES"], [], 4⟩ := by rfl

def expectedManifest : Translation.Manifest := ⟨coreTuple, []⟩

theorem altered_child_layout_rejected :
    Translation.accepts expectedManifest ⟨coreTuple.reverse, []⟩ = false := by decide +kernel

theorem wrong_attachment_rejected :
    Translation.accepts expectedManifest
      ⟨coreTuple, [("FN2-ECHO-RUN-FREE", "FN2-SCRIBE-RUN-FREE")]⟩ = false := by decide +kernel

/-- The changed body is valid canonical syntax and terminates, but gives NIL
instead of the arm's four results. -/
def alteredBody : Translation.Object :=
  .cons (.symbol [67,79,77,77,79,78,45,76,73,83,80] [81,85,79,84,69])
    (.cons (.symbol [67,79,77,77,79,78,45,76,73,83,80] [78,73,76])
           (.symbol [67,79,77,77,79,78,45,76,73,83,80] [78,73,76]))

theorem altered_body_rejected (id slot kind ordinal budget own dir : Val) :
    Translation.evalExport 512 alteredBody fns [] ≠
      .ok («FN2-ECHO-RUN-FREE-CHILDREN» id slot kind ordinal budget own dir) := by
  change (Except.ok Val.nil : Except String Val) ≠ .ok (Val.ofList [.int 0, .int 1, .int 0, Val.nil])
  decide +kernel

/-- All 57 children are present, with a live echo directory entry and row. -/
def witnessKids : CoreImage := fun i =>
  if i.val = 3 then Val.ofList [Val.ofList [.int 1], Val.ofList [.int 0], Val.nil, Val.nil, Val.nil, .int 1]
  else if i.val = 7 then Val.ofList (List.replicate 16 Val.nil ++ [.int 1])
  else .int i.val

theorem echo_free_positive :
    «FN2-ECHO-SNAPSHOT-READ-CODE» (.int 0) (image witnessKids) = .sym ":OK" ∧
    runCore world coreTuple echoKind echoFree false [.int 0, .int 1, image witnessKids] 1 =
      .ok (Val.ofList [.int 0, .int 1, .int 0, Val.nil, image witnessKids]) ∧
    «FN2-ECHO-RUN-FREE» (.int 0) (.int 1) (image witnessKids) =
      Val.ofList [.int 0, .int 1, .int 0, Val.nil, image witnessKids] := by
  have he : «FN2-ECHO-SNAPSHOT-READ-CODE» (.int 0) (image witnessKids) = .sym ":OK" := by decide +kernel
  have hf := echo_emitted_success (.int 0) (.int 1) (image witnessKids) (by decide +kernel) he
  exact ⟨he, by rw [echo_free_whole_core, hf], hf⟩

#print axioms echo_free_certificate
#print axioms altered_body_rejected
#print axioms altered_child_layout_rejected
#print axioms wrong_attachment_rejected
#print axioms echo_free_positive

end Fn2.Arms.Validation
