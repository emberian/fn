-- Generated from core_validation.lean.in and the canonical full child layout.
module

public import Fn2.Arms.Wrapper
public import Fn2.Arms.Validation
public import Fn2.Instances.CoreKinds
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.List.Control
-- BEGIN world bodies (emit_embed.py): scan
import all Fn2.Instances.LayerAWorld.S34_d0to6
import all Fn2.Instances.LayerAWorld.S33_d1to7
import all Fn2.Instances.LayerAWorld.S25_d2to3
import all Fn2.Instances.LayerAWorld.S13_d0to8
import all Fn2.Instances.LayerAWorld.S22_d1to7
import all Fn2.Instances.LayerAWorld.S19_d6to9
import all Fn2.Instances.LayerAWorld.S15xc66772_d1to9
import all Fn2.Instances.LayerAWorld.S20_d5to7
import all Fn2.Instances.LayerAWorld.S21_d6to7
import all Fn2.Instances.LayerAWorld.S16_d5to10
import all Fn2.Instances.LayerAWorld.S12_d0to10
import all Fn2.Instances.LayerAWorld.S12xff6259_d0to4
import all Fn2.Instances.LayerAWorld.S12xff6259_d5to6
import all Fn2.Instances.LayerAWorld.S14_d0to1
import all Fn2.Instances.LayerAWorld.S11x4c060b_d0to1
import all Fn2.Instances.LayerAWorld.S11x4c060b_d3b0
import all Fn2.Instances.LayerAWorld.S11x4c060b_d3b1
import all Fn2.Instances.LayerAWorld.S11x4c060b_d4
import all Fn2.Instances.LayerAWorld.S11x4c060b_d5b0
import all Fn2.Instances.LayerAWorld.S11x4c060b_d5b1
import all Fn2.Instances.LayerAWorld.S11x4c060b_d6to12
import all Fn2.Instances.LayerAWorld.S15_d6to11
import all Fn2.Instances.LayerAWorld.S9_d3to11
import all Fn2.Instances.LayerAWorld.S8_d2to12
import all Fn2.Instances.LayerAWorld.S5_d5to13
import all Fn2.Instances.LayerAWorld.S7_d0to13
import all Fn2.Instances.LayerAWorld.S6_d5to10
import all Fn2.Instances.LayerAWorld.S4_d0to24
import all Fn2.Instances.LayerAWorld.S3_d0to23
import all Fn2.Instances.LayerAWorld.S2_d0to29
import all Fn2.Instances.LayerAWorld.SCnsCtl_d6to14
import all Fn2.Instances.LayerAWorld.KCns_d0to12
import all Fn2.Instances.LayerAWorld.KCns_d13to40
import all Fn2.Instances.LayerAWorld.KCtl_d0to26
import all Fn2.Instances.LayerAWorld.Rest_d6b0
import all Fn2.Instances.LayerAWorld.Rest_d6b1
import all Fn2.Instances.LayerAWorld.Rest_d7b0
import all Fn2.Instances.LayerAWorld.Rest_d7b1
-- END world bodies

@[expose] public section
namespace Fn2.Arms.CoreValidation
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core
open Fn2.Instances.LayerAWorld Fn2.Instances.CoreKinds
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
theorem snapshot_parts (id core : Val)
    (h : «FN2-CNS-SNAPSHOT-READ-CODE» id core = .sym ":OK") :
    «FN2-MACHINE-PHASE-READ-CODE» id core = .sym ":OK" ∧
    «FN2-MACHINE-KIND» id core = .int 11 := by
  unfold «FN2-CNS-SNAPSHOT-READ-CODE» at h
  dsimp only at h
  by_cases hp : «FN2-MACHINE-PHASE-READ-CODE» id core = .sym ":OK"
  · simp [«NOT», «EQ», Prim.equal, hp] at h
    exact ⟨hp, h⟩
  · simp [«NOT», «EQ», Prim.equal, hp] at h

 theorem snapshot_bounds (id core : Val)
    (h : «FN2-CNS-SNAPSHOT-READ-CODE» id core = .sym ":OK") :
    («NATP» id).truthy = true ∧
    (Prim.lt id («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» core))).truthy = true ∧
    («NATP» («FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core))).truthy = true ∧
    (Prim.lt («FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core))
      («FN2-CNS-ROWS» («FN2-CNS-TABLE» core))).truthy = true := by
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

def cnsRead (id slot own dir : Val) : String → Val
  | "PHASE" => «FN2-CNS-PHASE» slot own
  | "GENERATION" => «FN2-CNS-GENERATION» slot own
  | "PRINCIPAL-SLOT" => «FN2-CNS-PRINCIPAL-SLOT» slot own
  | "ACCOUNT-REF" => «FN2-CNS-ACCOUNT-REF» slot own
  | "READY-PREV" => «FN2-MACHINES-READY-PREV» id dir
  | "READY-NEXT" => «FN2-MACHINES-READY-NEXT» id dir
  | "WAIT-REASON" => «FN2-MACHINES-WAIT-REASON» id dir
  | "DEADLINE" => «FN2-CNS-DEADLINE» slot own
  | "CTL" => «FN2-CNS-CTL» slot own
  | "CTL-GEN" => «FN2-CNS-CTL-GEN» slot own
  | "REQUEST" => «FN2-CNS-REQUEST» slot own
  | "FPOS" => «FN2-CNS-FPOS» slot own
  | "FLEN" => «FN2-CNS-FLEN» slot own
  | "FKIND" => «FN2-CNS-FKIND» slot own
  | "VERB" => «FN2-CNS-VERB» slot own
  | "CONSUMER" => «FN2-CNS-CONSUMER» slot own
  | "EPOCH" => «FN2-CNS-EPOCH» slot own
  | "OP" => «FN2-CNS-OP» slot own
  | "TO" => «FN2-CNS-TO» slot own
  | "CSTART" => «FN2-CNS-CSTART» slot own
  | "PAGE-LIMIT" => «FN2-CNS-PAGE-LIMIT» slot own
  | "WAIT-MS" => «FN2-CNS-WAIT-MS» slot own
  | "CPOS" => «FN2-CNS-CPOS» slot own
  | "VERSION" => «FN2-CNS-VERSION» slot own
  | "PUB-FRONTIER" => «FN2-CNS-PUB-FRONTIER» slot own
  | "COUNT" => «FN2-CNS-COUNT» slot own
  | "MORE" => «FN2-CNS-MORE» slot own
  | "OUTCOME" => «FN2-CNS-OUTCOME» slot own
  | "REASON" => «FN2-CNS-REASON» slot own
  | "POSTED" => «FN2-CNS-POSTED» slot own
  | "POSTED-WORD" => «FN2-CNS-POSTED-WORD» slot own
  | "EDGE" => «FN2-CNS-EDGE» slot own
  | "TXN" => «FN2-CNS-TXN» slot own
  | "TXN-GEN" => «FN2-CNS-TXN-GEN» slot own
  | "TX-SLOT" => «FN2-CNS-TX-SLOT» slot own
  | "TX-GEN" => «FN2-CNS-TX-GEN» slot own
  | "UPLOAD" => «FN2-CNS-UPLOAD» slot own
  | "UPLOAD-GEN" => «FN2-CNS-UPLOAD-GEN» slot own
  | "FSTART" => «FN2-CNS-FSTART» slot own
  | "FED" => «FN2-CNS-FED» slot own
  | "FEED-MODE" => «FN2-CNS-FEED-MODE» slot own
  | "FEED-DISCARD" => «FN2-CNS-FEED-DISCARD» slot own
  | "NAME-OFF" => «FN2-CNS-NAME-OFF» slot own
  | "NAME-LEN" => «FN2-CNS-NAME-LEN» slot own
  | "XSTEP" => «FN2-CNS-XSTEP» slot own
  | "XHEAD" => «FN2-CNS-XHEAD» slot own
  | "XGRANT" => «FN2-CNS-XGRANT» slot own
  | "IPOS" => «FN2-CNS-IPOS» slot own
  | "IOFF" => «FN2-CNS-IOFF» slot own
  | "ILEN" => «FN2-CNS-ILEN» slot own
  | "NPOS" => «FN2-CNS-NPOS» slot own
  | "ART" => «FN2-CNS-ART» slot own
  | "ISTREAM" => «FN2-CNS-ISTREAM» slot own
  | "ITYPE" => «FN2-CNS-ITYPE» slot own
  | "ALEN" => «FN2-CNS-ALEN» slot own
  | "LUNIT" => «FN2-CNS-LUNIT» slot own
  | "LEPOCH" => «FN2-CNS-LEPOCH» slot own
  | "LALLOC" => «FN2-CNS-LALLOC» slot own
  | "LSLOT" => «FN2-CNS-LSLOT» slot own
  | "LGEN" => «FN2-CNS-LGEN» slot own
  | "LEASE" => «FN2-CNS-LEASE» slot own
  | "REVENT" => «FN2-CNS-REVENT» slot own
  | "ROUTCOME" => «FN2-CNS-ROUTCOME» slot own
  | "RCOUNT" => «FN2-CNS-RCOUNT» slot own
  | "RREADY" => «FN2-CNS-RREADY» slot own
  | "PENDING" => «FN2-CNS-PENDING» slot own
  | "CURSOR" => «FN2-CNS-CURSOR» slot own
  | "XROW" => «FN2-CNS-XROW» slot own
  | "STOPPED" => «FN2-CNS-STOPPED» slot own
  | "NEXT-FREE" => «FN2-CNS-NEXT-FREE» slot own
  | _ => Val.nil


theorem cns_row_reads (id slot : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
  rowReads (coreWorld world coreTuple) (coreKind cns coreTuple)
    (coreTuple.zip [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) id slot = .ok [("ROW-PHASE", «FN2-CNS-PHASE» slot c17), ("ROW-GENERATION", «FN2-CNS-GENERATION» slot c17), ("ROW-PRINCIPAL-SLOT", «FN2-CNS-PRINCIPAL-SLOT» slot c17), ("ROW-ACCOUNT-REF", «FN2-CNS-ACCOUNT-REF» slot c17), ("ROW-READY-PREV", «FN2-MACHINES-READY-PREV» id c3), ("ROW-READY-NEXT", «FN2-MACHINES-READY-NEXT» id c3), ("ROW-WAIT-REASON", «FN2-MACHINES-WAIT-REASON» id c3), ("ROW-DEADLINE", «FN2-CNS-DEADLINE» slot c17), ("ROW-CTL", «FN2-CNS-CTL» slot c17), ("ROW-CTL-GEN", «FN2-CNS-CTL-GEN» slot c17), ("ROW-REQUEST", «FN2-CNS-REQUEST» slot c17), ("ROW-FPOS", «FN2-CNS-FPOS» slot c17), ("ROW-FLEN", «FN2-CNS-FLEN» slot c17), ("ROW-FKIND", «FN2-CNS-FKIND» slot c17), ("ROW-VERB", «FN2-CNS-VERB» slot c17), ("ROW-CONSUMER", «FN2-CNS-CONSUMER» slot c17), ("ROW-EPOCH", «FN2-CNS-EPOCH» slot c17), ("ROW-OP", «FN2-CNS-OP» slot c17), ("ROW-TO", «FN2-CNS-TO» slot c17), ("ROW-CSTART", «FN2-CNS-CSTART» slot c17), ("ROW-PAGE-LIMIT", «FN2-CNS-PAGE-LIMIT» slot c17), ("ROW-WAIT-MS", «FN2-CNS-WAIT-MS» slot c17), ("ROW-CPOS", «FN2-CNS-CPOS» slot c17), ("ROW-VERSION", «FN2-CNS-VERSION» slot c17), ("ROW-PUB-FRONTIER", «FN2-CNS-PUB-FRONTIER» slot c17), ("ROW-COUNT", «FN2-CNS-COUNT» slot c17), ("ROW-MORE", «FN2-CNS-MORE» slot c17), ("ROW-OUTCOME", «FN2-CNS-OUTCOME» slot c17), ("ROW-REASON", «FN2-CNS-REASON» slot c17), ("ROW-POSTED", «FN2-CNS-POSTED» slot c17), ("ROW-POSTED-WORD", «FN2-CNS-POSTED-WORD» slot c17), ("ROW-EDGE", «FN2-CNS-EDGE» slot c17), ("ROW-TXN", «FN2-CNS-TXN» slot c17), ("ROW-TXN-GEN", «FN2-CNS-TXN-GEN» slot c17), ("ROW-TX-SLOT", «FN2-CNS-TX-SLOT» slot c17), ("ROW-TX-GEN", «FN2-CNS-TX-GEN» slot c17), ("ROW-UPLOAD", «FN2-CNS-UPLOAD» slot c17), ("ROW-UPLOAD-GEN", «FN2-CNS-UPLOAD-GEN» slot c17), ("ROW-FSTART", «FN2-CNS-FSTART» slot c17), ("ROW-FED", «FN2-CNS-FED» slot c17), ("ROW-FEED-MODE", «FN2-CNS-FEED-MODE» slot c17), ("ROW-FEED-DISCARD", «FN2-CNS-FEED-DISCARD» slot c17), ("ROW-NAME-OFF", «FN2-CNS-NAME-OFF» slot c17), ("ROW-NAME-LEN", «FN2-CNS-NAME-LEN» slot c17), ("ROW-XSTEP", «FN2-CNS-XSTEP» slot c17), ("ROW-XHEAD", «FN2-CNS-XHEAD» slot c17), ("ROW-XGRANT", «FN2-CNS-XGRANT» slot c17), ("ROW-IPOS", «FN2-CNS-IPOS» slot c17), ("ROW-IOFF", «FN2-CNS-IOFF» slot c17), ("ROW-ILEN", «FN2-CNS-ILEN» slot c17), ("ROW-NPOS", «FN2-CNS-NPOS» slot c17), ("ROW-ART", «FN2-CNS-ART» slot c17), ("ROW-ISTREAM", «FN2-CNS-ISTREAM» slot c17), ("ROW-ITYPE", «FN2-CNS-ITYPE» slot c17), ("ROW-ALEN", «FN2-CNS-ALEN» slot c17), ("ROW-LUNIT", «FN2-CNS-LUNIT» slot c17), ("ROW-LEPOCH", «FN2-CNS-LEPOCH» slot c17), ("ROW-LALLOC", «FN2-CNS-LALLOC» slot c17), ("ROW-LSLOT", «FN2-CNS-LSLOT» slot c17), ("ROW-LGEN", «FN2-CNS-LGEN» slot c17), ("ROW-LEASE", «FN2-CNS-LEASE» slot c17), ("ROW-REVENT", «FN2-CNS-REVENT» slot c17), ("ROW-ROUTCOME", «FN2-CNS-ROUTCOME» slot c17), ("ROW-RCOUNT", «FN2-CNS-RCOUNT» slot c17), ("ROW-RREADY", «FN2-CNS-RREADY» slot c17), ("ROW-PENDING", «FN2-CNS-PENDING» slot c17), ("ROW-CURSOR", «FN2-CNS-CURSOR» slot c17), ("ROW-XROW", «FN2-CNS-XROW» slot c17), ("ROW-STOPPED", «FN2-CNS-STOPPED» slot c17), ("ROW-NEXT-FREE", «FN2-CNS-NEXT-FREE» slot c17)] := by
  apply rowReads_eq (coreWorld world coreTuple) (coreKind cns coreTuple) _ id slot c17 c3
    (by rfl) (by rfl) (cnsRead id slot c17 c3)
  intro c hc
  change c ∈ ["PHASE", "GENERATION", "PRINCIPAL-SLOT", "ACCOUNT-REF", "READY-PREV", "READY-NEXT", "WAIT-REASON", "DEADLINE", "CTL", "CTL-GEN", "REQUEST", "FPOS", "FLEN", "FKIND", "VERB", "CONSUMER", "EPOCH", "OP", "TO", "CSTART", "PAGE-LIMIT", "WAIT-MS", "CPOS", "VERSION", "PUB-FRONTIER", "COUNT", "MORE", "OUTCOME", "REASON", "POSTED", "POSTED-WORD", "EDGE", "TXN", "TXN-GEN", "TX-SLOT", "TX-GEN", "UPLOAD", "UPLOAD-GEN", "FSTART", "FED", "FEED-MODE", "FEED-DISCARD", "NAME-OFF", "NAME-LEN", "XSTEP", "XHEAD", "XGRANT", "IPOS", "IOFF", "ILEN", "NPOS", "ART", "ISTREAM", "ITYPE", "ALEN", "LUNIT", "LEPOCH", "LALLOC", "LSLOT", "LGEN", "LEASE", "REVENT", "ROUTCOME", "RCOUNT", "RREADY", "PENDING", "CURSOR", "XROW", "STOPPED", "NEXT-FREE"] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-PHASE" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-PHASE».dispatched (err := "no function FN2-CNS-PHASE/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-GENERATION" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-GENERATION».dispatched (err := "no function FN2-CNS-GENERATION/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-PRINCIPAL-SLOT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-PRINCIPAL-SLOT».dispatched (err := "no function FN2-CNS-PRINCIPAL-SLOT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-ACCOUNT-REF" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-ACCOUNT-REF».dispatched (err := "no function FN2-CNS-ACCOUNT-REF/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-MACHINES-READY-PREV" [id, c3] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-MACHINES-READY-PREV».dispatched (err := "no function FN2-MACHINES-READY-PREV/2") id c3)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-MACHINES-READY-NEXT" [id, c3] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-MACHINES-READY-NEXT».dispatched (err := "no function FN2-MACHINES-READY-NEXT/2") id c3)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-MACHINES-WAIT-REASON" [id, c3] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-MACHINES-WAIT-REASON».dispatched (err := "no function FN2-MACHINES-WAIT-REASON/2") id c3)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-DEADLINE" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-DEADLINE».dispatched (err := "no function FN2-CNS-DEADLINE/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-CTL" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-CTL».dispatched (err := "no function FN2-CNS-CTL/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-CTL-GEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-CTL-GEN».dispatched (err := "no function FN2-CNS-CTL-GEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-REQUEST" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-REQUEST».dispatched (err := "no function FN2-CNS-REQUEST/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-FPOS" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-FPOS».dispatched (err := "no function FN2-CNS-FPOS/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-FLEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-FLEN».dispatched (err := "no function FN2-CNS-FLEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-FKIND" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-FKIND».dispatched (err := "no function FN2-CNS-FKIND/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-VERB" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-VERB».dispatched (err := "no function FN2-CNS-VERB/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-CONSUMER" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-CONSUMER».dispatched (err := "no function FN2-CNS-CONSUMER/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-EPOCH" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-EPOCH».dispatched (err := "no function FN2-CNS-EPOCH/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-OP" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-OP».dispatched (err := "no function FN2-CNS-OP/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-TO" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-TO».dispatched (err := "no function FN2-CNS-TO/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-CSTART" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-CSTART».dispatched (err := "no function FN2-CNS-CSTART/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-PAGE-LIMIT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-PAGE-LIMIT».dispatched (err := "no function FN2-CNS-PAGE-LIMIT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-WAIT-MS" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-WAIT-MS».dispatched (err := "no function FN2-CNS-WAIT-MS/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-CPOS" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-CPOS».dispatched (err := "no function FN2-CNS-CPOS/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-VERSION" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-VERSION».dispatched (err := "no function FN2-CNS-VERSION/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-PUB-FRONTIER" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-PUB-FRONTIER».dispatched (err := "no function FN2-CNS-PUB-FRONTIER/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-COUNT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-COUNT».dispatched (err := "no function FN2-CNS-COUNT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-MORE" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-MORE».dispatched (err := "no function FN2-CNS-MORE/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-OUTCOME" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-OUTCOME».dispatched (err := "no function FN2-CNS-OUTCOME/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-REASON" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-REASON».dispatched (err := "no function FN2-CNS-REASON/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-POSTED" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-POSTED».dispatched (err := "no function FN2-CNS-POSTED/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-POSTED-WORD" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-POSTED-WORD».dispatched (err := "no function FN2-CNS-POSTED-WORD/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-EDGE" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-EDGE».dispatched (err := "no function FN2-CNS-EDGE/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-TXN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-TXN».dispatched (err := "no function FN2-CNS-TXN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-TXN-GEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-TXN-GEN».dispatched (err := "no function FN2-CNS-TXN-GEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-TX-SLOT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-TX-SLOT».dispatched (err := "no function FN2-CNS-TX-SLOT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-TX-GEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-TX-GEN».dispatched (err := "no function FN2-CNS-TX-GEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-UPLOAD" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-UPLOAD».dispatched (err := "no function FN2-CNS-UPLOAD/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-UPLOAD-GEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-UPLOAD-GEN».dispatched (err := "no function FN2-CNS-UPLOAD-GEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-FSTART" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-FSTART».dispatched (err := "no function FN2-CNS-FSTART/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-FED" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-FED».dispatched (err := "no function FN2-CNS-FED/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-FEED-MODE" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-FEED-MODE».dispatched (err := "no function FN2-CNS-FEED-MODE/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-FEED-DISCARD" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-FEED-DISCARD».dispatched (err := "no function FN2-CNS-FEED-DISCARD/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-NAME-OFF" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-NAME-OFF».dispatched (err := "no function FN2-CNS-NAME-OFF/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-NAME-LEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-NAME-LEN».dispatched (err := "no function FN2-CNS-NAME-LEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-XSTEP" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-XSTEP».dispatched (err := "no function FN2-CNS-XSTEP/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-XHEAD" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-XHEAD».dispatched (err := "no function FN2-CNS-XHEAD/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-XGRANT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-XGRANT».dispatched (err := "no function FN2-CNS-XGRANT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-IPOS" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-IPOS».dispatched (err := "no function FN2-CNS-IPOS/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-IOFF" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-IOFF».dispatched (err := "no function FN2-CNS-IOFF/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-ILEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-ILEN».dispatched (err := "no function FN2-CNS-ILEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-NPOS" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-NPOS».dispatched (err := "no function FN2-CNS-NPOS/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-ART" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-ART».dispatched (err := "no function FN2-CNS-ART/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-ISTREAM" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-ISTREAM».dispatched (err := "no function FN2-CNS-ISTREAM/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-ITYPE" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-ITYPE».dispatched (err := "no function FN2-CNS-ITYPE/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-ALEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-ALEN».dispatched (err := "no function FN2-CNS-ALEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-LUNIT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-LUNIT».dispatched (err := "no function FN2-CNS-LUNIT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-LEPOCH" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-LEPOCH».dispatched (err := "no function FN2-CNS-LEPOCH/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-LALLOC" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-LALLOC».dispatched (err := "no function FN2-CNS-LALLOC/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-LSLOT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-LSLOT».dispatched (err := "no function FN2-CNS-LSLOT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-LGEN" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-LGEN».dispatched (err := "no function FN2-CNS-LGEN/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-LEASE" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-LEASE».dispatched (err := "no function FN2-CNS-LEASE/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-REVENT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-REVENT».dispatched (err := "no function FN2-CNS-REVENT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-ROUTCOME" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-ROUTCOME».dispatched (err := "no function FN2-CNS-ROUTCOME/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-RCOUNT" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-RCOUNT».dispatched (err := "no function FN2-CNS-RCOUNT/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-RREADY" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-RREADY».dispatched (err := "no function FN2-CNS-RREADY/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-PENDING" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-PENDING».dispatched (err := "no function FN2-CNS-PENDING/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-CURSOR" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-CURSOR».dispatched (err := "no function FN2-CNS-CURSOR/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-XROW" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-XROW».dispatched (err := "no function FN2-CNS-XROW/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-STOPPED" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-STOPPED».dispatched (err := "no function FN2-CNS-STOPPED/2") slot c17)
  · exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-NEXT-FREE" [slot, c17] (by decide +kernel)).trans
      (Fn2.Instances.CoreWorld.«FN2-CNS-NEXT-FREE».dispatched (err := "no function FN2-CNS-NEXT-FREE/2") slot c17)



def handlerBase (id slot event outcome reason count aux0 aux1 : Val) : Env :=
  [("ID",id),("SLOT",slot),("KIND",.int 11),("ORDINAL",.int 6),
   ("EVENT",event),("OUTCOME",outcome),("REASON",reason),("COUNT",count),("AUX0",aux0),("AUX1",aux1)]
def handlerFrame (id slot event outcome reason count aux0 aux1 : Val) : Frame :=
  { kind := coreKind cns coreTuple, observe := true, refusal := [],
    base := handlerBase id slot event outcome reason count aux0 aux1 }
def handlerState (id slot event outcome reason count aux0 aux1 : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) : St :=
  { stobjs := coreTuple.zip [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56],
    vars := [("ROW-PHASE", «FN2-CNS-PHASE» slot c17), ("ROW-GENERATION", «FN2-CNS-GENERATION» slot c17), ("ROW-PRINCIPAL-SLOT", «FN2-CNS-PRINCIPAL-SLOT» slot c17), ("ROW-ACCOUNT-REF", «FN2-CNS-ACCOUNT-REF» slot c17), ("ROW-READY-PREV", «FN2-MACHINES-READY-PREV» id c3), ("ROW-READY-NEXT", «FN2-MACHINES-READY-NEXT» id c3), ("ROW-WAIT-REASON", «FN2-MACHINES-WAIT-REASON» id c3), ("ROW-DEADLINE", «FN2-CNS-DEADLINE» slot c17), ("ROW-CTL", «FN2-CNS-CTL» slot c17), ("ROW-CTL-GEN", «FN2-CNS-CTL-GEN» slot c17), ("ROW-REQUEST", «FN2-CNS-REQUEST» slot c17), ("ROW-FPOS", «FN2-CNS-FPOS» slot c17), ("ROW-FLEN", «FN2-CNS-FLEN» slot c17), ("ROW-FKIND", «FN2-CNS-FKIND» slot c17), ("ROW-VERB", «FN2-CNS-VERB» slot c17), ("ROW-CONSUMER", «FN2-CNS-CONSUMER» slot c17), ("ROW-EPOCH", «FN2-CNS-EPOCH» slot c17), ("ROW-OP", «FN2-CNS-OP» slot c17), ("ROW-TO", «FN2-CNS-TO» slot c17), ("ROW-CSTART", «FN2-CNS-CSTART» slot c17), ("ROW-PAGE-LIMIT", «FN2-CNS-PAGE-LIMIT» slot c17), ("ROW-WAIT-MS", «FN2-CNS-WAIT-MS» slot c17), ("ROW-CPOS", «FN2-CNS-CPOS» slot c17), ("ROW-VERSION", «FN2-CNS-VERSION» slot c17), ("ROW-PUB-FRONTIER", «FN2-CNS-PUB-FRONTIER» slot c17), ("ROW-COUNT", «FN2-CNS-COUNT» slot c17), ("ROW-MORE", «FN2-CNS-MORE» slot c17), ("ROW-OUTCOME", «FN2-CNS-OUTCOME» slot c17), ("ROW-REASON", «FN2-CNS-REASON» slot c17), ("ROW-POSTED", «FN2-CNS-POSTED» slot c17), ("ROW-POSTED-WORD", «FN2-CNS-POSTED-WORD» slot c17), ("ROW-EDGE", «FN2-CNS-EDGE» slot c17), ("ROW-TXN", «FN2-CNS-TXN» slot c17), ("ROW-TXN-GEN", «FN2-CNS-TXN-GEN» slot c17), ("ROW-TX-SLOT", «FN2-CNS-TX-SLOT» slot c17), ("ROW-TX-GEN", «FN2-CNS-TX-GEN» slot c17), ("ROW-UPLOAD", «FN2-CNS-UPLOAD» slot c17), ("ROW-UPLOAD-GEN", «FN2-CNS-UPLOAD-GEN» slot c17), ("ROW-FSTART", «FN2-CNS-FSTART» slot c17), ("ROW-FED", «FN2-CNS-FED» slot c17), ("ROW-FEED-MODE", «FN2-CNS-FEED-MODE» slot c17), ("ROW-FEED-DISCARD", «FN2-CNS-FEED-DISCARD» slot c17), ("ROW-NAME-OFF", «FN2-CNS-NAME-OFF» slot c17), ("ROW-NAME-LEN", «FN2-CNS-NAME-LEN» slot c17), ("ROW-XSTEP", «FN2-CNS-XSTEP» slot c17), ("ROW-XHEAD", «FN2-CNS-XHEAD» slot c17), ("ROW-XGRANT", «FN2-CNS-XGRANT» slot c17), ("ROW-IPOS", «FN2-CNS-IPOS» slot c17), ("ROW-IOFF", «FN2-CNS-IOFF» slot c17), ("ROW-ILEN", «FN2-CNS-ILEN» slot c17), ("ROW-NPOS", «FN2-CNS-NPOS» slot c17), ("ROW-ART", «FN2-CNS-ART» slot c17), ("ROW-ISTREAM", «FN2-CNS-ISTREAM» slot c17), ("ROW-ITYPE", «FN2-CNS-ITYPE» slot c17), ("ROW-ALEN", «FN2-CNS-ALEN» slot c17), ("ROW-LUNIT", «FN2-CNS-LUNIT» slot c17), ("ROW-LEPOCH", «FN2-CNS-LEPOCH» slot c17), ("ROW-LALLOC", «FN2-CNS-LALLOC» slot c17), ("ROW-LSLOT", «FN2-CNS-LSLOT» slot c17), ("ROW-LGEN", «FN2-CNS-LGEN» slot c17), ("ROW-LEASE", «FN2-CNS-LEASE» slot c17), ("ROW-REVENT", «FN2-CNS-REVENT» slot c17), ("ROW-ROUTCOME", «FN2-CNS-ROUTCOME» slot c17), ("ROW-RCOUNT", «FN2-CNS-RCOUNT» slot c17), ("ROW-RREADY", «FN2-CNS-RREADY» slot c17), ("ROW-PENDING", «FN2-CNS-PENDING» slot c17), ("ROW-CURSOR", «FN2-CNS-CURSOR» slot c17), ("ROW-XROW", «FN2-CNS-XROW» slot c17), ("ROW-STOPPED", «FN2-CNS-STOPPED» slot c17), ("ROW-NEXT-FREE", «FN2-CNS-NEXT-FREE» slot c17)] ++ handlerBase id slot event outcome reason count aux0 aux1 }

theorem unsigned_fits (n : Nat) (v : Val) :
    («UNSIGNED-BYTE-P» (.int n) v).truthy = ColType.fits (.uw n) v := by
  rw [fits_uw_eq_acl2]
  simp [«UNSIGNED-BYTE-P», «INTEGER-RANGE-P», «NOT», Prim.integerp, Prim.lt,
    Val.toInt, Val.isInt, Val.ofBool, Val.truthy_ite, Bool.and_assoc, not_decide_lt_zero]

theorem natp_lt (i rows : Val) :
    ((«NATP» i).truthy && (Prim.lt i rows).truthy) = natLt i rows := by
  rw [natLt_eq_acl2]
  simp [«NATP», «NOT», Val.truthy_ite, Bool.and_assoc]

def handlerPending : List (String × Expr) :=
  [("REVENT",.sym "EVENT"),("ROUTCOME",.sym "OUTCOME"),("RCOUNT",.sym "COUNT"),("RREADY",.int 1)]

def handlerPairs (event outcome count : Val) : List (String × Val) :=
  [("REVENT",event),("ROUTCOME",outcome),("RCOUNT",count),("RREADY",.int 1)]
def handlerFits (slot event outcome count own : Val) : Bool :=
  natLt slot («FN2-CNS-ROWS» own) &&
    (ColType.fits (.uw 8) event && (ColType.fits (.uw 8) outcome && ColType.fits (.uw 32) count))
def handlerOwn (slot event outcome count own : Val) : Val :=
  «FN2-CNS-SET-RREADY» slot (.int 1)
    («FN2-CNS-SET-RCOUNT» slot count
      («FN2-CNS-SET-ROUTCOME» slot outcome («FN2-CNS-SET-REVENT» slot event own)))

theorem «FN2-CNS-ROWS».core_call («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) "FN2-CNS-ROWS" [«FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ROWS» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-ROWS" [«FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-ROWS».dispatched (err := "no function FN2-CNS-ROWS/1") «FN2-CNS»)

theorem «FN2-MACHINES-ROWS».core_call («FN2-MACHINES» : Val) :
    callFn (coreWorld world coreTuple) "FN2-MACHINES-ROWS" [«FN2-MACHINES»] = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-ROWS» «FN2-MACHINES») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-MACHINES-ROWS" [«FN2-MACHINES»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-MACHINES-ROWS».dispatched (err := "no function FN2-MACHINES-ROWS/1") «FN2-MACHINES»)

theorem «FN2-CONTROL-RECORD-STOP».core_call («REASON» : Val) («FN2-CONTROL» : Val) :
    callFn (coreWorld world coreTuple) "FN2-CONTROL-RECORD-STOP" [«REASON», «FN2-CONTROL»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CONTROL-RECORD-STOP» «REASON» «FN2-CONTROL») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CONTROL-RECORD-STOP" [«REASON», «FN2-CONTROL»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CONTROL-RECORD-STOP».dispatched (err := "no function FN2-CONTROL-RECORD-STOP/2") «REASON» «FN2-CONTROL»)

theorem «FN2-CNS-SET-REVENT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "REVENT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REVENT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-REVENT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-REVENT».dispatched (err := "no function FN2-CNS-SET-REVENT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-ROUTCOME».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "ROUTCOME") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ROUTCOME» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-ROUTCOME" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-ROUTCOME».dispatched (err := "no function FN2-CNS-SET-ROUTCOME/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-RCOUNT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "RCOUNT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-RCOUNT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-RCOUNT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-RCOUNT».dispatched (err := "no function FN2-CNS-SET-RCOUNT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-RREADY».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "RREADY") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-RREADY» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-RREADY" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-RREADY».dispatched (err := "no function FN2-CNS-SET-RREADY/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-PHASE».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "PHASE") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PHASE» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-PHASE" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-PHASE».dispatched (err := "no function FN2-CNS-SET-PHASE/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-GENERATION».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "GENERATION") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-GENERATION» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-GENERATION" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-GENERATION».dispatched (err := "no function FN2-CNS-SET-GENERATION/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-PRINCIPAL-SLOT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "PRINCIPAL-SLOT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PRINCIPAL-SLOT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-PRINCIPAL-SLOT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-PRINCIPAL-SLOT».dispatched (err := "no function FN2-CNS-SET-PRINCIPAL-SLOT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-ACCOUNT-REF».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "ACCOUNT-REF") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ACCOUNT-REF» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-ACCOUNT-REF" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-ACCOUNT-REF».dispatched (err := "no function FN2-CNS-SET-ACCOUNT-REF/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-DEADLINE».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "DEADLINE") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-DEADLINE» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-DEADLINE" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-DEADLINE».dispatched (err := "no function FN2-CNS-SET-DEADLINE/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-CTL».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "CTL") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CTL» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-CTL" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-CTL».dispatched (err := "no function FN2-CNS-SET-CTL/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-CTL-GEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "CTL-GEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CTL-GEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-CTL-GEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-CTL-GEN».dispatched (err := "no function FN2-CNS-SET-CTL-GEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-REQUEST».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "REQUEST") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REQUEST» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-REQUEST" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-REQUEST».dispatched (err := "no function FN2-CNS-SET-REQUEST/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-FPOS».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "FPOS") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FPOS» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-FPOS" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-FPOS».dispatched (err := "no function FN2-CNS-SET-FPOS/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-FLEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "FLEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FLEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-FLEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-FLEN».dispatched (err := "no function FN2-CNS-SET-FLEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-FKIND».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "FKIND") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FKIND» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-FKIND" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-FKIND».dispatched (err := "no function FN2-CNS-SET-FKIND/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-VERB».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "VERB") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-VERB» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-VERB" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-VERB».dispatched (err := "no function FN2-CNS-SET-VERB/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-CONSUMER».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "CONSUMER") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CONSUMER» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-CONSUMER" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-CONSUMER».dispatched (err := "no function FN2-CNS-SET-CONSUMER/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-EPOCH».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "EPOCH") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-EPOCH» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-EPOCH" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-EPOCH».dispatched (err := "no function FN2-CNS-SET-EPOCH/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-OP».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "OP") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-OP» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-OP" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-OP».dispatched (err := "no function FN2-CNS-SET-OP/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-TO».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "TO") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TO» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-TO" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-TO».dispatched (err := "no function FN2-CNS-SET-TO/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-CSTART».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "CSTART") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CSTART» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-CSTART" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-CSTART».dispatched (err := "no function FN2-CNS-SET-CSTART/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-PAGE-LIMIT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "PAGE-LIMIT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PAGE-LIMIT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-PAGE-LIMIT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-PAGE-LIMIT».dispatched (err := "no function FN2-CNS-SET-PAGE-LIMIT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-WAIT-MS».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "WAIT-MS") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-WAIT-MS» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-WAIT-MS" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-WAIT-MS».dispatched (err := "no function FN2-CNS-SET-WAIT-MS/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-CPOS».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "CPOS") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CPOS» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-CPOS" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-CPOS».dispatched (err := "no function FN2-CNS-SET-CPOS/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-VERSION».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "VERSION") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-VERSION» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-VERSION" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-VERSION».dispatched (err := "no function FN2-CNS-SET-VERSION/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-PUB-FRONTIER».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "PUB-FRONTIER") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PUB-FRONTIER» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-PUB-FRONTIER" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-PUB-FRONTIER».dispatched (err := "no function FN2-CNS-SET-PUB-FRONTIER/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-COUNT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "COUNT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-COUNT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-COUNT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-COUNT».dispatched (err := "no function FN2-CNS-SET-COUNT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-MORE».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "MORE") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-MORE» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-MORE" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-MORE».dispatched (err := "no function FN2-CNS-SET-MORE/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-OUTCOME».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "OUTCOME") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-OUTCOME» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-OUTCOME" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-OUTCOME».dispatched (err := "no function FN2-CNS-SET-OUTCOME/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-REASON».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "REASON") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REASON» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-REASON" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-REASON».dispatched (err := "no function FN2-CNS-SET-REASON/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-POSTED».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "POSTED") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-POSTED» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-POSTED" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-POSTED».dispatched (err := "no function FN2-CNS-SET-POSTED/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-POSTED-WORD».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "POSTED-WORD") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-POSTED-WORD» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-POSTED-WORD" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-POSTED-WORD».dispatched (err := "no function FN2-CNS-SET-POSTED-WORD/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-EDGE».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "EDGE") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-EDGE» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-EDGE" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-EDGE».dispatched (err := "no function FN2-CNS-SET-EDGE/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-TXN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "TXN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TXN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-TXN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-TXN».dispatched (err := "no function FN2-CNS-SET-TXN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-TXN-GEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "TXN-GEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TXN-GEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-TXN-GEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-TXN-GEN».dispatched (err := "no function FN2-CNS-SET-TXN-GEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-TX-SLOT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "TX-SLOT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TX-SLOT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-TX-SLOT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-TX-SLOT».dispatched (err := "no function FN2-CNS-SET-TX-SLOT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-TX-GEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "TX-GEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TX-GEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-TX-GEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-TX-GEN».dispatched (err := "no function FN2-CNS-SET-TX-GEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-UPLOAD».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "UPLOAD") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-UPLOAD» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-UPLOAD" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-UPLOAD».dispatched (err := "no function FN2-CNS-SET-UPLOAD/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-UPLOAD-GEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "UPLOAD-GEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-UPLOAD-GEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-UPLOAD-GEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-UPLOAD-GEN».dispatched (err := "no function FN2-CNS-SET-UPLOAD-GEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-FSTART».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "FSTART") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FSTART» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-FSTART" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-FSTART».dispatched (err := "no function FN2-CNS-SET-FSTART/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-FED».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "FED") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FED» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-FED" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-FED».dispatched (err := "no function FN2-CNS-SET-FED/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-FEED-MODE».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "FEED-MODE") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FEED-MODE» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-FEED-MODE" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-FEED-MODE».dispatched (err := "no function FN2-CNS-SET-FEED-MODE/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-FEED-DISCARD».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "FEED-DISCARD") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FEED-DISCARD» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-FEED-DISCARD" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-FEED-DISCARD».dispatched (err := "no function FN2-CNS-SET-FEED-DISCARD/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-NAME-OFF».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "NAME-OFF") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NAME-OFF» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-NAME-OFF" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-NAME-OFF».dispatched (err := "no function FN2-CNS-SET-NAME-OFF/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-NAME-LEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "NAME-LEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NAME-LEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-NAME-LEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-NAME-LEN».dispatched (err := "no function FN2-CNS-SET-NAME-LEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-XSTEP».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "XSTEP") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XSTEP» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-XSTEP" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-XSTEP».dispatched (err := "no function FN2-CNS-SET-XSTEP/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-XHEAD».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "XHEAD") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XHEAD» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-XHEAD" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-XHEAD».dispatched (err := "no function FN2-CNS-SET-XHEAD/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-XGRANT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "XGRANT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XGRANT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-XGRANT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-XGRANT».dispatched (err := "no function FN2-CNS-SET-XGRANT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-IPOS».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "IPOS") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-IPOS» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-IPOS" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-IPOS».dispatched (err := "no function FN2-CNS-SET-IPOS/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-IOFF».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "IOFF") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-IOFF» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-IOFF" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-IOFF».dispatched (err := "no function FN2-CNS-SET-IOFF/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-ILEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "ILEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ILEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-ILEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-ILEN».dispatched (err := "no function FN2-CNS-SET-ILEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-NPOS».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "NPOS") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NPOS» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-NPOS" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-NPOS».dispatched (err := "no function FN2-CNS-SET-NPOS/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-ART».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "ART") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ART» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-ART" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-ART».dispatched (err := "no function FN2-CNS-SET-ART/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-ISTREAM».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "ISTREAM") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ISTREAM» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-ISTREAM" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-ISTREAM».dispatched (err := "no function FN2-CNS-SET-ISTREAM/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-ITYPE».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "ITYPE") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ITYPE» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-ITYPE" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-ITYPE».dispatched (err := "no function FN2-CNS-SET-ITYPE/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-ALEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "ALEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ALEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-ALEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-ALEN».dispatched (err := "no function FN2-CNS-SET-ALEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-LUNIT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "LUNIT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LUNIT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-LUNIT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-LUNIT».dispatched (err := "no function FN2-CNS-SET-LUNIT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-LEPOCH».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "LEPOCH") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LEPOCH» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-LEPOCH" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-LEPOCH».dispatched (err := "no function FN2-CNS-SET-LEPOCH/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-LALLOC».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "LALLOC") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LALLOC» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-LALLOC" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-LALLOC».dispatched (err := "no function FN2-CNS-SET-LALLOC/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-LSLOT».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "LSLOT") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LSLOT» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-LSLOT" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-LSLOT».dispatched (err := "no function FN2-CNS-SET-LSLOT/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-LGEN».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "LGEN") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LGEN» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-LGEN" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-LGEN».dispatched (err := "no function FN2-CNS-SET-LGEN/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-LEASE».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "LEASE") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LEASE» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-LEASE" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-LEASE».dispatched (err := "no function FN2-CNS-SET-LEASE/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-PENDING».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "PENDING") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PENDING» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-PENDING" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-PENDING».dispatched (err := "no function FN2-CNS-SET-PENDING/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-CURSOR».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "CURSOR") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CURSOR» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-CURSOR" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-CURSOR».dispatched (err := "no function FN2-CNS-SET-CURSOR/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-XROW».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "XROW") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XROW» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-XROW" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-XROW».dispatched (err := "no function FN2-CNS-SET-XROW/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-STOPPED».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "STOPPED") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-STOPPED» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-STOPPED" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-STOPPED».dispatched (err := "no function FN2-CNS-SET-STOPPED/3") «I» «V» «FN2-CNS»)

theorem «FN2-CNS-SET-NEXT-FREE».core_call («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-CNS" ++ "-SET-" ++ "NEXT-FREE") [«I», «V», «FN2-CNS»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NEXT-FREE» «I» «V» «FN2-CNS») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CNS-SET-NEXT-FREE" [«I», «V», «FN2-CNS»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CNS-SET-NEXT-FREE».dispatched (err := "no function FN2-CNS-SET-NEXT-FREE/3") «I» «V» «FN2-CNS»)

theorem «FN2-MACHINES-SET-WAIT-REASON».core_call («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    callFn (coreWorld world coreTuple) ("FN2-MACHINES-SET-" ++ "WAIT-REASON") [«I», «V», «FN2-MACHINES»] = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-SET-WAIT-REASON» «I» «V» «FN2-MACHINES») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-MACHINES-SET-WAIT-REASON" [«I», «V», «FN2-MACHINES»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-MACHINES-SET-WAIT-REASON».dispatched (err := "no function FN2-MACHINES-SET-WAIT-REASON/3") «I» «V» «FN2-MACHINES»)

theorem «FN2-CORE-RELEASE-CHILDREN».core_call («SLOT» : Val) («GEN» : Val) («OKIND» : Val) («OSLOT» : Val) («OGEN» : Val) («FN2-POOL» : Val) («FN2-CONTROL» : Val) :
    callFn (coreWorld world coreTuple) "FN2-CORE-RELEASE-CHILDREN" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL», «FN2-CONTROL»] = .ok (Fn2.Instances.LayerAWorld.«FN2-CORE-RELEASE-CHILDREN» «SLOT» «GEN» «OKIND» «OSLOT» «OGEN» «FN2-POOL» «FN2-CONTROL») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-CORE-RELEASE-CHILDREN" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL», «FN2-CONTROL»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-CORE-RELEASE-CHILDREN».dispatched (err := "no function FN2-CORE-RELEASE-CHILDREN/7") «SLOT» «GEN» «OKIND» «OSLOT» «OGEN» «FN2-POOL» «FN2-CONTROL»)

theorem «FN2-MACHINES-RECLAIM».core_call («ID» : Val) («ORD» : Val) («RETIRE» : Val) («FN2-MACHINES» : Val) («FN2-CONTROL» : Val) :
    callFn (coreWorld world coreTuple) "FN2-MACHINES-RECLAIM" [«ID», «ORD», «RETIRE», «FN2-MACHINES», «FN2-CONTROL»] = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-RECLAIM» «ID» «ORD» «RETIRE» «FN2-MACHINES» «FN2-CONTROL») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-MACHINES-RECLAIM" [«ID», «ORD», «RETIRE», «FN2-MACHINES», «FN2-CONTROL»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-MACHINES-RECLAIM».dispatched (err := "no function FN2-MACHINES-RECLAIM/5") «ID» «ORD» «RETIRE» «FN2-MACHINES» «FN2-CONTROL»)

theorem «FN2-MACHINES-FREE-HEAD-OF».core_call («ORD» : Val) («FN2-MACHINES» : Val) :
    callFn (coreWorld world coreTuple) "FN2-MACHINES-FREE-HEAD-OF" [«ORD», «FN2-MACHINES»] = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-FREE-HEAD-OF» «ORD» «FN2-MACHINES») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-MACHINES-FREE-HEAD-OF" [«ORD», «FN2-MACHINES»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-MACHINES-FREE-HEAD-OF».dispatched (err := "no function FN2-MACHINES-FREE-HEAD-OF/2") «ORD» «FN2-MACHINES»)

theorem «FN2-MACHINES-GEN-LIMIT».core_call («FN2-MACHINES» : Val) :
    callFn (coreWorld world coreTuple) "FN2-MACHINES-GEN-LIMIT" [«FN2-MACHINES»] = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-GEN-LIMIT» «FN2-MACHINES») := by
  exact (Fn2.Arms.Validation.callFn_core_plain world coreTuple "FN2-MACHINES-GEN-LIMIT" [«FN2-MACHINES»] (by decide +kernel)).trans
    (Fn2.Instances.CoreWorld.«FN2-MACHINES-GEN-LIMIT».dispatched (err := "no function FN2-MACHINES-GEN-LIMIT/1") «FN2-MACHINES»)


theorem handler_put (id slot event outcome reason count aux0 aux1 : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
  let st : St := { (handlerState id slot event outcome reason count aux0 aux1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56)
    with pending := handlerPending }
  put (coreWorld world coreTuple) (handlerFrame id slot event outcome reason count aux0 aux1)
    st (handlerPairs event outcome count) =
  if handlerFits slot event outcome count c17 then
    .ok (setStobj (setStobj st "FN2-CNS" (handlerOwn slot event outcome count c17)) "FN2-MACHINES" c3)
  else .ok (setStobj st "FN2-CONTROL" («FN2-CONTROL-RECORD-STOP» (.int 13) c5)) := by
  dsimp only
  let f := handlerFrame id slot event outcome reason count aux0 aux1
  let st : St := { (handlerState id slot event outcome reason count aux0 aux1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56)
    with pending := handlerPending }
  let pairs := handlerPairs event outcome count
  change put (coreWorld world coreTuple) f st pairs = _
  have hp : (natLt slot («FN2-CNS-ROWS» c17) &&
      ((pairs.filter fun p => directoryFields.contains p.1).isEmpty || natLt id («FN2-MACHINES-ROWS» c3)) &&
      pairs.all (fun (n,v) => match f.kind.columns.find? (·.1 == n) with
        | some (_,ty) => ty.fits v | none => false)) = handlerFits slot event outcome count c17 := by
    change ((natLt slot («FN2-CNS-ROWS» c17) && true) &&
      (ColType.fits (.uw 8) event && (ColType.fits (.uw 8) outcome &&
        (ColType.fits (.uw 32) count && true)))) = _
    simp only [Bool.and_true, handlerFits]
  by_cases h : handlerFits slot event outcome count c17 = true
  · rw [if_pos h]
    rw [put_pass (coreWorld world coreTuple) f st pairs slot id c17 c3 c5
      («FN2-CNS-ROWS» c17) («FN2-MACHINES-ROWS» c3)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      («FN2-CNS-ROWS».core_call _) («FN2-MACHINES-ROWS».core_call _) (hp.trans h)]
    have hf : f.kind.name = "FN2-CNS" := by rfl
    have ho : pairs.filter (fun p => !directoryFields.contains p.1) = pairs := by rfl
    have hd : pairs.filter (fun p => directoryFields.contains p.1) = [] := by rfl
    rw [ho, hd, hf]
    simp only [pairs, handlerPairs, List.foldlM_cons, List.foldlM_nil,
      «FN2-CNS-SET-REVENT».core_call, «FN2-CNS-SET-ROUTCOME».core_call,
      «FN2-CNS-SET-RCOUNT».core_call, «FN2-CNS-SET-RREADY».core_call, except_ok_bind]
    rfl
  · rw [if_neg h]
    have hn : handlerFits slot event outcome count c17 = false := Bool.eq_false_iff.mpr h
    rw [put_fail (coreWorld world coreTuple) f st pairs slot id c17 c3 c5
      («FN2-CNS-ROWS» c17) («FN2-MACHINES-ROWS» c3)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      («FN2-CNS-ROWS».core_call _) («FN2-MACHINES-ROWS».core_call _) (hp.trans hn)]
    have hc : const (coreWorld world coreTuple) "*FN2-STOP-REASON-MACHINE-WRITE*" = .ok (.int 13) := by rfl
    simp only [hc, except_ok_bind, «FN2-CONTROL-RECORD-STOP».core_call]
    rfl

theorem handler_run (id slot event outcome reason count aux0 aux1 : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
  runArm (coreWorld world coreTuple) (coreKind cns coreTuple) readResult true
    ([id,slot,.int 11,.int 6,event,outcome,reason,count,aux0,aux1] ++ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) 2 =
  (do
    let st ← flush (coreWorld world coreTuple) (handlerFrame id slot event outcome reason count aux0 aux1)
      { (handlerState id slot event outcome reason count aux0 aux1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56) with pending := handlerPending }
    let result ← wakeResult (handlerFrame id slot event outcome reason count aux0 aux1) st (← var st "ID")
    match result with
    | .done v => pure v
    | .again _ => throw ":repeat-next outside a :repeat") := by
  unfold runArm
  simp only [coreKind, Bool.not_true, Bool.true_eq_false, ↓reduceIte, List.length_append,
    List.length_cons, List.length_nil]
  have hl : coreTuple.length = 57 := by rfl
  simp only [hl]
  change (do
    let reads ← rowReads (coreWorld world coreTuple) (coreKind cns coreTuple)
      (coreTuple.zip [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) id slot
    let d ← readResult.read
    let f : Frame := { kind := coreKind cns coreTuple, observe := true, refusal := d.onRefusal, base := handlerBase id slot event outcome reason count aux0 aux1 }
    match ← run (coreWorld world coreTuple) f 2
      { stobjs := coreTuple.zip [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56], vars := reads ++ f.base } d.steps with
    | .done v => pure v
    | .again _ => throw ":repeat-next outside a :repeat") = _
  rw [cns_row_reads]
  have hr : readResult.read = .ok ⟨[], [], [.set handlerPending, .wake]⟩ := by rfl
  simp only [hr, except_ok_bind]
  dsimp only [run, pend, handlerPending]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, except_ok_bind, bind_assoc]
  rfl

theorem handler_flush (id slot event outcome reason count aux0 aux1 : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
  let f := handlerFrame id slot event outcome reason count aux0 aux1
  let st : St := { (handlerState id slot event outcome reason count aux0 aux1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56) with pending := handlerPending }
  flush (coreWorld world coreTuple) f st =
    (do let st' ← put (coreWorld world coreTuple) f st (handlerPairs event outcome count)
        pure { st' with pending := [], next := none, nextDone := false }) := by
  dsimp only
  let f := handlerFrame id slot event outcome reason count aux0 aux1
  let st : St := { (handlerState id slot event outcome reason count aux0 aux1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56) with pending := handlerPending }
  change flush (coreWorld world coreTuple) f st = _
  have e1 : ev (coreWorld world coreTuple) f.kind st (.sym "EVENT") = .ok event := by
    have hr : readExpr (coreWorld world coreTuple) f.kind (.sym "EVENT") = .ok (.var "EVENT") := by
      change readExprF (coreWorld world coreTuple) f.kind (fun _ => .error "unused") (.sym "EVENT") = _
      simp [readExprF, show f.kind.name = "FN2-CNS" from rfl]
      rfl
    simp only [ev, hr, except_ok_bind, Term.eval]
    try rfl
  have e2 : ev (coreWorld world coreTuple) f.kind st (.sym "OUTCOME") = .ok outcome := by
    have hr : readExpr (coreWorld world coreTuple) f.kind (.sym "OUTCOME") = .ok (.var "OUTCOME") := by
      change readExprF (coreWorld world coreTuple) f.kind (fun _ => .error "unused") (.sym "OUTCOME") = _
      simp [readExprF, show f.kind.name = "FN2-CNS" from rfl]
      rfl
    simp only [ev, hr, except_ok_bind, Term.eval]
    try rfl
  have e3 : ev (coreWorld world coreTuple) f.kind st (.sym "COUNT") = .ok count := by
    have hr : readExpr (coreWorld world coreTuple) f.kind (.sym "COUNT") = .ok (.var "COUNT") := by
      change readExprF (coreWorld world coreTuple) f.kind (fun _ => .error "unused") (.sym "COUNT") = _
      simp [readExprF, show f.kind.name = "FN2-CNS" from rfl]
      rfl
    simp only [ev, hr, except_ok_bind, Term.eval]
    try rfl
  have e4 : ev (coreWorld world coreTuple) f.kind st (.int 1) = .ok (.int 1) := by
    have hr : readExpr (coreWorld world coreTuple) f.kind (.int 1) = .ok (.quote (.int 1)) := by rfl
    simp only [ev, hr, except_ok_bind, Term.eval]
    try rfl
  have he : st.pending.mapM (fun (n,e) => do pure (n, ← ev (coreWorld world coreTuple) f.kind st e)) = .ok (handlerPairs event outcome count) := by
    change handlerPending.mapM _ = _
    simp only [handlerPending, List.mapM_cons, List.mapM_nil, e1, e2, e3, e4, except_ok_bind]
    try rfl
  simp only [flush, he, except_ok_bind]
  rfl

theorem handler_reduced (id slot event outcome reason count aux0 aux1 : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
  runArm (coreWorld world coreTuple) (coreKind cns coreTuple) readResult true
    ([id,slot,.int 11,.int 6,event,outcome,reason,count,aux0,aux1] ++ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) 2 =
  if handlerFits slot event outcome count c17 then
    .ok (Val.ofList (id :: [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, (handlerOwn slot event outcome count c17), c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]))
  else .ok (Val.ofList (id :: [c0, c1, c2, c3, c4, («FN2-CONTROL-RECORD-STOP» (.int 13) c5), c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56])) := by
  rw [handler_run, handler_flush, handler_put]
  split <;> rfl

theorem handler_write (id event outcome count core : Val)
    (h : «FN2-CNS-SNAPSHOT-READ-CODE» id core = .sym ":OK")
    (hself : «UPDATE-FN2-CNS-TABLE» («FN2-CNS-TABLE» core) core = core) :
    «FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY» id event outcome count (.int 1) core =
    if handlerFits («FN2-MACHINE-SLOT» id core) event outcome count («FN2-CNS-TABLE» core) then
      «UPDATE-FN2-CNS-TABLE»
        (handlerOwn («FN2-MACHINE-SLOT» id core) event outcome count («FN2-CNS-TABLE» core)) core
    else «FN2-CORE-STOP» (.int 13) core := by
  obtain ⟨hi, hr, hs, hb⟩ := snapshot_bounds id core h
  obtain ⟨_, hk⟩ := snapshot_parts id core h
  have hid : («FN2-MACHINE-IDP» id core).truthy = true := by
    simp [«FN2-MACHINE-IDP», hi, hr]
  have hslot : «FN2-MACHINE-SLOT» id core = «FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core) := by
    simp [«FN2-MACHINE-SLOT», «FN2-MACHINE-SLOT-READ-CODE», hid, «EQ», Prim.equal]
  have hn : natLt («FN2-MACHINE-SLOT» id core) («FN2-CNS-ROWS» («FN2-CNS-TABLE» core)) = true := by
    rw [← natp_lt, hslot, hs, hb]
    rfl
  generalize he : ColType.fits (.uw 8) event = e
  generalize ho : ColType.fits (.uw 8) outcome = o
  generalize hc : ColType.fits (.uw 32) count = c
  have he' : («UNSIGNED-BYTE-P» (.int 8) event).truthy = e := (unsigned_fits 8 event).trans he
  have ho' : («UNSIGNED-BYTE-P» (.int 8) outcome).truthy = o := (unsigned_fits 8 outcome).trans ho
  have hc' : («UNSIGNED-BYTE-P» (.int 32) count).truthy = c := (unsigned_fits 32 count).trans hc
  have h1 : («UNSIGNED-BYTE-P» (.int 1) (.int 1)).truthy = true := by rfl
  rw [hslot] at hn
  cases e <;> cases o <;> cases c <;>
    simp [«FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY», «NOT», Prim.equal,
      hid, hk, hslot, hs, hb, he', ho', hc', h1, he, ho, hc, handlerFits, hn,
      handlerOwn, Native.nth, Native.nthN, Val.nfix, Val.toInt, hself,
      «FN2-MACHINE-REFUSE-WRITE»]

theorem handler_certificate (id event outcome reason count aux0 aux1 : Val) (c0 : Val) (c1 : Val) (c2 : Val) (c3 : Val) (c4 : Val) (c5 : Val) (c6 : Val) (c7 : Val) (c8 : Val) (c9 : Val) (c10 : Val) (c11 : Val) (c12 : Val) (c13 : Val) (c14 : Val) (c15 : Val) (c16 : Val) (c17 : Val) (c18 : Val) (c19 : Val) (c20 : Val) (c21 : Val) (c22 : Val) (c23 : Val) (c24 : Val) (c25 : Val) (c26 : Val) (c27 : Val) (c28 : Val) (c29 : Val) (c30 : Val) (c31 : Val) (c32 : Val) (c33 : Val) (c34 : Val) (c35 : Val) (c36 : Val) (c37 : Val) (c38 : Val) (c39 : Val) (c40 : Val) (c41 : Val) (c42 : Val) (c43 : Val) (c44 : Val) (c45 : Val) (c46 : Val) (c47 : Val) (c48 : Val) (c49 : Val) (c50 : Val) (c51 : Val) (c52 : Val) (c53 : Val) (c54 : Val) (c55 : Val) (c56 : Val) :
    ∃ fuel result,
      runCore world coreTuple cns readResult true
        [id,event,outcome,reason,count,aux0,aux1,Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]] fuel = .ok result ∧
      result = «FN2-CNS-ON-READ-RESULT» id event outcome reason count aux0 aux1 (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) := by
  apply Wrapper.certificate world coreTuple cns readResult true
    [id,event,outcome,reason,count,aux0,aux1,Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]]
    («FN2-CNS-ON-READ-RESULT» id event outcome reason count aux0 aux1 (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]))
    («FN2-CNS-SNAPSHOT-READ-CODE» id (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56])) (by rfl) (by rfl)
  · exact Fn2.Instances.CoreWorld.«FN2-CNS-SNAPSHOT-READ-CODE».dispatched (err := "no function FN2-CNS-SNAPSHOT-READ-CODE/2") _ _
  · intro h
    let slot := «FN2-MACHINE-SLOT» id (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56])
    let afterKids := if handlerFits slot event outcome count c17
      then [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, (handlerOwn slot event outcome count c17), c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56] else [c0, c1, c2, c3, c4, («FN2-CONTROL-RECORD-STOP» (.int 13) c5), c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]
    refine ⟨slot, .int 11, 2, Val.ofList (id :: afterKids), ?_, ?_, ?_, ?_⟩
    · exact Fn2.Instances.CoreWorld.«FN2-MACHINE-SLOT».dispatched (err := "no function FN2-MACHINE-SLOT/2") _ _
    · rfl
    · change runArm (coreWorld world coreTuple) (coreKind cns coreTuple) readResult true
        ([id,slot,.int 11,.int 6,event,outcome,reason,count,aux0,aux1] ++ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) 2 = _
      rw [handler_reduced]
      unfold afterKids
      split <;> rfl
    · have hw := handler_write id event outcome count (Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]) h (by rfl)
      unfold «FN2-CNS-ON-READ-RESULT»
      simp only [«EQ», Prim.equal, h, beq_self_eq_true, Val.ofBool, Val.t, Val.truthy, ↓reduceIte]
      rw [hw]
      change finish true coreTuple (Val.ofList (id :: afterKids)) =
        .ok (Val.ofList [id, if handlerFits slot event outcome count c17 then
          Val.ofList [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, (handlerOwn slot event outcome count c17), c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56] else Val.ofList [c0, c1, c2, c3, c4, («FN2-CONTROL-RECORD-STOP» (.int 13) c5), c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56]])
      unfold afterKids
      by_cases hf : handlerFits slot event outcome count c17 = true
      · simp only [hf, ↓reduceIte]
        change finish true coreTuple (Val.ofList (id :: [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, (handlerOwn slot event outcome count c17), c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56])) = _
        rfl
      · simp only [hf, ↓reduceIte]
        change finish true coreTuple (Val.ofList (id :: [c0, c1, c2, c3, c4, («FN2-CONTROL-RECORD-STOP» (.int 13) c5), c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56])) = _
        rfl
  · intro h
    unfold «FN2-CNS-ON-READ-RESULT»
    simp only [«EQ», Prim.equal, beq_eq_false_iff_ne.mpr h, Val.ofBool, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Every child of the canonical core layout, with arbitrary ACL2 values. -/
def coreImage (kids : Fin 57 → Val) : Val := Val.ofList [(kids ⟨0, by decide⟩), (kids ⟨1, by decide⟩), (kids ⟨2, by decide⟩), (kids ⟨3, by decide⟩), (kids ⟨4, by decide⟩), (kids ⟨5, by decide⟩), (kids ⟨6, by decide⟩), (kids ⟨7, by decide⟩), (kids ⟨8, by decide⟩), (kids ⟨9, by decide⟩), (kids ⟨10, by decide⟩), (kids ⟨11, by decide⟩), (kids ⟨12, by decide⟩), (kids ⟨13, by decide⟩), (kids ⟨14, by decide⟩), (kids ⟨15, by decide⟩), (kids ⟨16, by decide⟩), (kids ⟨17, by decide⟩), (kids ⟨18, by decide⟩), (kids ⟨19, by decide⟩), (kids ⟨20, by decide⟩), (kids ⟨21, by decide⟩), (kids ⟨22, by decide⟩), (kids ⟨23, by decide⟩), (kids ⟨24, by decide⟩), (kids ⟨25, by decide⟩), (kids ⟨26, by decide⟩), (kids ⟨27, by decide⟩), (kids ⟨28, by decide⟩), (kids ⟨29, by decide⟩), (kids ⟨30, by decide⟩), (kids ⟨31, by decide⟩), (kids ⟨32, by decide⟩), (kids ⟨33, by decide⟩), (kids ⟨34, by decide⟩), (kids ⟨35, by decide⟩), (kids ⟨36, by decide⟩), (kids ⟨37, by decide⟩), (kids ⟨38, by decide⟩), (kids ⟨39, by decide⟩), (kids ⟨40, by decide⟩), (kids ⟨41, by decide⟩), (kids ⟨42, by decide⟩), (kids ⟨43, by decide⟩), (kids ⟨44, by decide⟩), (kids ⟨45, by decide⟩), (kids ⟨46, by decide⟩), (kids ⟨47, by decide⟩), (kids ⟨48, by decide⟩), (kids ⟨49, by decide⟩), (kids ⟨50, by decide⟩), (kids ⟨51, by decide⟩), (kids ⟨52, by decide⟩), (kids ⟨53, by decide⟩), (kids ⟨54, by decide⟩), (kids ⟨55, by decide⟩), (kids ⟨56, by decide⟩)]

theorem cns_read_result_certificate (id event outcome reason count aux0 aux1 : Val)
    (kids : Fin 57 → Val) :
    ∃ fuel result,
      runCore world coreTuple cns readResult true
        [id,event,outcome,reason,count,aux0,aux1,coreImage kids] fuel = .ok result ∧
      result = «FN2-CNS-ON-READ-RESULT» id event outcome reason count aux0 aux1 (coreImage kids) := by
  exact handler_certificate id event outcome reason count aux0 aux1 (kids ⟨0, by decide⟩) (kids ⟨1, by decide⟩) (kids ⟨2, by decide⟩) (kids ⟨3, by decide⟩) (kids ⟨4, by decide⟩) (kids ⟨5, by decide⟩) (kids ⟨6, by decide⟩) (kids ⟨7, by decide⟩) (kids ⟨8, by decide⟩) (kids ⟨9, by decide⟩) (kids ⟨10, by decide⟩) (kids ⟨11, by decide⟩) (kids ⟨12, by decide⟩) (kids ⟨13, by decide⟩) (kids ⟨14, by decide⟩) (kids ⟨15, by decide⟩) (kids ⟨16, by decide⟩) (kids ⟨17, by decide⟩) (kids ⟨18, by decide⟩) (kids ⟨19, by decide⟩) (kids ⟨20, by decide⟩) (kids ⟨21, by decide⟩) (kids ⟨22, by decide⟩) (kids ⟨23, by decide⟩) (kids ⟨24, by decide⟩) (kids ⟨25, by decide⟩) (kids ⟨26, by decide⟩) (kids ⟨27, by decide⟩) (kids ⟨28, by decide⟩) (kids ⟨29, by decide⟩) (kids ⟨30, by decide⟩) (kids ⟨31, by decide⟩) (kids ⟨32, by decide⟩) (kids ⟨33, by decide⟩) (kids ⟨34, by decide⟩) (kids ⟨35, by decide⟩) (kids ⟨36, by decide⟩) (kids ⟨37, by decide⟩) (kids ⟨38, by decide⟩) (kids ⟨39, by decide⟩) (kids ⟨40, by decide⟩) (kids ⟨41, by decide⟩) (kids ⟨42, by decide⟩) (kids ⟨43, by decide⟩) (kids ⟨44, by decide⟩) (kids ⟨45, by decide⟩) (kids ⟨46, by decide⟩) (kids ⟨47, by decide⟩) (kids ⟨48, by decide⟩) (kids ⟨49, by decide⟩) (kids ⟨50, by decide⟩) (kids ⟨51, by decide⟩) (kids ⟨52, by decide⟩) (kids ⟨53, by decide⟩) (kids ⟨54, by decide⟩) (kids ⟨55, by decide⟩) (kids ⟨56, by decide⟩)

def witnessKids : Fin 57 → Val := fun i =>
  if i.val = 3 then Val.ofList [Val.ofList [.int 11],Val.ofList [.int 0],Val.nil,Val.nil,Val.nil,.int 1]
  else if i.val = 17 then Val.ofList (List.replicate 67 Val.nil ++ [.int 1])
  else .int i.val

def witnessCore : Val := Val.ofList (List.ofFn witnessKids)
def witnessResult : Val := «FN2-CNS-ON-READ-RESULT» (.int 0) (.int 13) (.int 0) (.int 0) (.int 7) (.int 0) (.int 0) witnessCore

theorem handler_write_positive :
    witnessCore.toList.length = coreTuple.length ∧
    «FN2-CNS-SNAPSHOT-READ-CODE» (.int 0) witnessCore = .sym ":OK" ∧
    witnessResult.car = .int 0 ∧
    «FN2-CNS-REVENT» (.int 0) («FN2-CNS-TABLE» witnessResult.cdr.car) = .int 13 ∧
    «FN2-CNS-ROUTCOME» (.int 0) («FN2-CNS-TABLE» witnessResult.cdr.car) = .int 0 ∧
    «FN2-CNS-RCOUNT» (.int 0) («FN2-CNS-TABLE» witnessResult.cdr.car) = .int 7 ∧
    «FN2-CNS-RREADY» (.int 0) («FN2-CNS-TABLE» witnessResult.cdr.car) = .int 1 ∧
    witnessResult ≠ Val.ofList [.int 0,witnessCore] := by decide +kernel

def wakeBeforeWrite : Arm := { readResult with
  decl := Val.ofList [Val.ofList [.sym ":WAKE"], readResult.decl.car] }

theorem pending_write_order_rejected :
    runCore world coreTuple cns wakeBeforeWrite true
      [.int 0,.int 13,.int 0,.int 0,.int 7,.int 0,.int 0,witnessCore] 1 ≠ .ok witnessResult := by
  decide +kernel

theorem omitted_child_rejected (fuel : Nat) (result : Val) :
    runCore world coreTuple cns readResult true
      [.int 0,.int 13,.int 0,.int 0,.int 7,.int 0,.int 0,Val.ofList witnessCore.toList.tail] fuel ≠ .ok result := by
  apply Wrapper.omitted_child_rejected
  decide +kernel

end Fn2.Arms.CoreValidation
namespace Fn2.Arms.CoreValidation
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core
open Fn2.Instances.LayerAWorld Fn2.Instances.CoreKinds

/-- Logical column writes retain their independence even for malformed arrays. -/
def fieldWrite (field : Nat) (slot value own : Val) : Val :=
  Native.updateNth (.int field) (Native.updateNth slot value (Native.nth (.int field) own)) own

theorem fieldWrite_order (i j : Nat) (slot v w own : Val) (h : i < j) :
    fieldWrite i slot v (fieldWrite j slot w own) =
      fieldWrite j slot w (fieldWrite i slot v own) := by
  exact updateNth_array_commute i j slot v w own (by omega)


theorem «FN2-CNS-SET-PHASE».field_write (slot value own : Val) :
    «FN2-CNS-SET-PHASE» slot value own = fieldWrite 0 slot value own := by rfl

theorem «FN2-CNS-SET-GENERATION».field_write (slot value own : Val) :
    «FN2-CNS-SET-GENERATION» slot value own = fieldWrite 1 slot value own := by rfl

theorem «FN2-CNS-SET-CTL».field_write (slot value own : Val) :
    «FN2-CNS-SET-CTL» slot value own = fieldWrite 5 slot value own := by rfl

theorem «FN2-CNS-SET-CTL-GEN».field_write (slot value own : Val) :
    «FN2-CNS-SET-CTL-GEN» slot value own = fieldWrite 6 slot value own := by rfl

theorem «FN2-CNS-SET-EDGE».field_write (slot value own : Val) :
    «FN2-CNS-SET-EDGE» slot value own = fieldWrite 28 slot value own := by rfl

theorem «FN2-CNS-SET-TXN».field_write (slot value own : Val) :
    «FN2-CNS-SET-TXN» slot value own = fieldWrite 29 slot value own := by rfl

theorem «FN2-CNS-SET-TXN-GEN».field_write (slot value own : Val) :
    «FN2-CNS-SET-TXN-GEN» slot value own = fieldWrite 30 slot value own := by rfl

theorem «FN2-CNS-SET-TX-SLOT».field_write (slot value own : Val) :
    «FN2-CNS-SET-TX-SLOT» slot value own = fieldWrite 31 slot value own := by rfl

theorem «FN2-CNS-SET-TX-GEN».field_write (slot value own : Val) :
    «FN2-CNS-SET-TX-GEN» slot value own = fieldWrite 32 slot value own := by rfl

theorem «FN2-CNS-SET-UPLOAD».field_write (slot value own : Val) :
    «FN2-CNS-SET-UPLOAD» slot value own = fieldWrite 33 slot value own := by rfl

theorem «FN2-CNS-SET-UPLOAD-GEN».field_write (slot value own : Val) :
    «FN2-CNS-SET-UPLOAD-GEN» slot value own = fieldWrite 34 slot value own := by rfl

theorem «FN2-CNS-SET-NEXT-FREE».field_write (slot value own : Val) :
    «FN2-CNS-SET-NEXT-FREE» slot value own = fieldWrite 66 slot value own := by rfl

theorem «FN2-CNS-SET-LEASE».field_write (slot value own : Val) :
    «FN2-CNS-SET-LEASE» slot value own = fieldWrite 57 slot value own := by rfl

theorem «FN2-CNS-SET-LSLOT».field_write (slot value own : Val) :
    «FN2-CNS-SET-LSLOT» slot value own = fieldWrite 55 slot value own := by rfl

theorem «FN2-CNS-SET-LGEN».field_write (slot value own : Val) :
    «FN2-CNS-SET-LGEN» slot value own = fieldWrite 56 slot value own := by rfl

def cleanupOwn (slot : Val) (phase : Val) (gen : Val) (next : Val) (own : Val) : Val := («FN2-CNS-SET-PHASE» slot (phase) («FN2-CNS-SET-NEXT-FREE» slot (next) («FN2-CNS-SET-TX-GEN» slot (.int 0) («FN2-CNS-SET-TX-SLOT» slot (.int 4294967295) («FN2-CNS-SET-UPLOAD-GEN» slot (.int 0) («FN2-CNS-SET-UPLOAD» slot (.int 4294967295) («FN2-CNS-SET-TXN-GEN» slot (.int 0) («FN2-CNS-SET-TXN» slot (.int 4294967295) («FN2-CNS-SET-EDGE» slot (.int 4294967295) («FN2-CNS-SET-CTL-GEN» slot (.int 0) («FN2-CNS-SET-CTL» slot (.int 4294967295) («FN2-CNS-SET-GENERATION» slot (gen) own))))))))))))

theorem cleanup_write_order (slot : Val) (phase : Val) (gen : Val) (next : Val) (own : Val) :
    («FN2-CNS-SET-NEXT-FREE» slot (next) («FN2-CNS-SET-UPLOAD-GEN» slot (.int 0) («FN2-CNS-SET-UPLOAD» slot (.int 4294967295) («FN2-CNS-SET-TX-GEN» slot (.int 0) («FN2-CNS-SET-TX-SLOT» slot (.int 4294967295) («FN2-CNS-SET-TXN-GEN» slot (.int 0) («FN2-CNS-SET-TXN» slot (.int 4294967295) («FN2-CNS-SET-EDGE» slot (.int 4294967295) («FN2-CNS-SET-CTL-GEN» slot (.int 0) («FN2-CNS-SET-CTL» slot (.int 4294967295) («FN2-CNS-SET-GENERATION» slot (gen) («FN2-CNS-SET-PHASE» slot (phase) own)))))))))))) = cleanupOwn slot phase gen next own := by

  simp (disch := decide) only [cleanupOwn, «FN2-CNS-SET-GENERATION».field_write, «FN2-CNS-SET-CTL».field_write, «FN2-CNS-SET-CTL-GEN».field_write, «FN2-CNS-SET-EDGE».field_write, «FN2-CNS-SET-TXN».field_write, «FN2-CNS-SET-TXN-GEN».field_write, «FN2-CNS-SET-UPLOAD».field_write, «FN2-CNS-SET-UPLOAD-GEN».field_write, «FN2-CNS-SET-TX-SLOT».field_write, «FN2-CNS-SET-TX-GEN».field_write, «FN2-CNS-SET-NEXT-FREE».field_write, «FN2-CNS-SET-PHASE».field_write, fieldWrite_order 0 66, fieldWrite_order 0 32, fieldWrite_order 0 31, fieldWrite_order 0 34, fieldWrite_order 0 33, fieldWrite_order 0 30, fieldWrite_order 0 29, fieldWrite_order 0 28, fieldWrite_order 0 6, fieldWrite_order 0 5, fieldWrite_order 0 1, fieldWrite_order 32 34, fieldWrite_order 32 33, fieldWrite_order 31 34, fieldWrite_order 31 33]

def leaseOwn (slot : Val) (own : Val) : Val := («FN2-CNS-SET-LGEN» slot (.int 0) («FN2-CNS-SET-LSLOT» slot (.int 4294967295) («FN2-CNS-SET-LEASE» slot (.int 0) own)))

theorem lease_write_order (slot : Val) (own : Val) :
    («FN2-CNS-SET-LEASE» slot (.int 0) («FN2-CNS-SET-LGEN» slot (.int 0) («FN2-CNS-SET-LSLOT» slot (.int 4294967295) own))) = leaseOwn slot  own := by

  simp (disch := decide) only [leaseOwn, «FN2-CNS-SET-LEASE».field_write, «FN2-CNS-SET-LSLOT».field_write, «FN2-CNS-SET-LGEN».field_write, fieldWrite_order 55 57, fieldWrite_order 56 57]

theorem lease_write (id core : Val)
    (h : «FN2-CNS-SNAPSHOT-READ-CODE» id core = .sym ":OK") :
    «FN2-CNS-WRITE+LSLOT+LGEN+LEASE» id (.int 4294967295) (.int 0) (.int 0) core =
      «UPDATE-FN2-CNS-TABLE» (leaseOwn («FN2-MACHINE-SLOT» id core) («FN2-CNS-TABLE» core)) core := by
  obtain ⟨hi, hr, hs, hb⟩ := snapshot_bounds id core h
  obtain ⟨_, hk⟩ := snapshot_parts id core h
  have hid : («FN2-MACHINE-IDP» id core).truthy = true := by
    simp [«FN2-MACHINE-IDP», hi, hr]
  have hslot : «FN2-MACHINE-SLOT» id core = «FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core) := by
    simp [«FN2-MACHINE-SLOT», «FN2-MACHINE-SLOT-READ-CODE», hid, «EQ», Prim.equal]
  have hn0 : («UNSIGNED-BYTE-P» (.int 32) (.int 4294967295)).truthy = true := by rfl
  have hz60 : («UNSIGNED-BYTE-P» (.int 60) (.int 0)).truthy = true := by rfl
  have hz1 : («UNSIGNED-BYTE-P» (.int 1) (.int 0)).truthy = true := by rfl
  have hconst0 : («NATP» (.int 0)).truthy = true := by rfl
  have hconst1 : (Prim.lt (.int 0) (.int 2)).truthy = true := by rfl
  have hconst2 : (Prim.lt (.int 0) (.int 26)).truthy = true := by rfl
  have hconst3 : («NATP» (.int 11)).truthy = true := by rfl
  have hconst4 : (Prim.lt (.int 11) (.int 12)).truthy = true := by rfl
  have hconst5 : (Prim.lt (.int 0) (.int 12)).truthy = true := by rfl
  simp [«FN2-CNS-WRITE+LSLOT+LGEN+LEASE», «NOT», Prim.equal,
    hid, hk, hslot, hs, hb, hn0, hz60, hz1, hconst0, hconst1, hconst2, hconst3, hconst4, hconst5,
    Native.nth, Native.nthN, Val.nfix, Val.toInt, lease_write_order]

def cleanupFits (gen next : Val) : Bool := ColType.fits (.uw 60) gen && ColType.fits (.uw 32) next

theorem cleanup_write (id gen next retire core : Val)
    (h : «FN2-CNS-SNAPSHOT-READ-CODE» id core = .sym ":OK")
    (hself : «UPDATE-FN2-CNS-TABLE» («FN2-CNS-TABLE» core) core = core) :
    «FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE»
      id (if retire.truthy then .int 11 else .int 0) gen (.int 0) (.int 4294967295) (.int 0)
      (.int 4294967295) (.int 4294967295) (.int 0) (.int 4294967295) (.int 0)
      (.int 4294967295) (.int 0) next core =
    if cleanupFits gen next then
      «UPDATE-FN2-CORE-MACHINES»
        («FN2-MACHINES-SET-WAIT-REASON» id (.int 0) («FN2-CORE-MACHINES» core))
        («UPDATE-FN2-CNS-TABLE»
          (cleanupOwn («FN2-MACHINE-SLOT» id core) (if retire.truthy then .int 11 else .int 0) gen next («FN2-CNS-TABLE» core)) core)
    else «FN2-CORE-STOP» (.int 13) core := by
  obtain ⟨hi, hr, hs, hb⟩ := snapshot_bounds id core h
  obtain ⟨_, hk⟩ := snapshot_parts id core h
  have hid : («FN2-MACHINE-IDP» id core).truthy = true := by
    simp [«FN2-MACHINE-IDP», hi, hr]
  have hslot : «FN2-MACHINE-SLOT» id core = «FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» core) := by
    simp [«FN2-MACHINE-SLOT», «FN2-MACHINE-SLOT-READ-CODE», hid, «EQ», Prim.equal]
  have hn0 : («UNSIGNED-BYTE-P» (.int 32) (.int 4294967295)).truthy = true := by rfl
  have hz60 : («UNSIGNED-BYTE-P» (.int 60) (.int 0)).truthy = true := by rfl
  have hz1 : («UNSIGNED-BYTE-P» (.int 1) (.int 0)).truthy = true := by rfl
  have hconst0 : («NATP» (.int 0)).truthy = true := by rfl
  have hconst1 : (Prim.lt (.int 0) (.int 2)).truthy = true := by rfl
  have hconst2 : (Prim.lt (.int 0) (.int 26)).truthy = true := by rfl
  have hconst3 : («NATP» (.int 11)).truthy = true := by rfl
  have hconst4 : (Prim.lt (.int 11) (.int 12)).truthy = true := by rfl
  have hconst5 : (Prim.lt (.int 0) (.int 12)).truthy = true := by rfl
  have hm (v : Val) : «FN2-CORE-MACHINES» («UPDATE-FN2-CNS-TABLE» v core) = «FN2-CORE-MACHINES» core := by
    exact nth_updateNth_ne 3 17 v core (by decide)
  generalize hg : ColType.fits (.uw 60) gen = g
  generalize hn : ColType.fits (.uw 32) next = n
  have hg' : («UNSIGNED-BYTE-P» (.int 60) gen).truthy = g := (unsigned_fits 60 gen).trans hg
  have hn' : («UNSIGNED-BYTE-P» (.int 32) next).truthy = n := (unsigned_fits 32 next).trans hn
  cases hh : retire.truthy <;> cases g <;> cases n <;>
    simp [«FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE»,
      «NOT», «EQL», Prim.equal,
      hid, hk, hslot, hs, hb, hi, hr, hm, hconst0, hconst1, hconst2, hconst3, hconst4, hconst5, hn0, hz60, hg', hn', hg, hn, hh, cleanupFits,
      Native.nth, Native.nthN, Val.nfix, Val.toInt, cleanup_write_order,
      «FN2-MACHINE-REFUSE-WRITE», hself]

def drainBase (id slot budget : Val) : Env :=
  [("ID",id),("SLOT",slot),("KIND",.int 11),("ORDINAL",.int 6),("BUDGET",budget)]
def drainFrame (id slot budget : Val) : Frame :=
  { kind := coreKind cns coreTuple, observe := false, refusal := [.stop "MACHINE-PHASE" none],
    base := drainBase id slot budget }

def leasePairs  : List (String × Val) := [("LEASE",.int 0), ("LSLOT",.int 4294967295), ("LGEN",.int 0)]

theorem lease_put (id slot budget own dir control : Val)  (st : St)
    (hi : var st "ID" = .ok id) (hs : var st "SLOT" = .ok slot)
    (ho : stobj st "FN2-CNS" = .ok own) (hd : stobj st "FN2-MACHINES" = .ok dir)
    (hc : stobj st "FN2-CONTROL" = .ok control)
    (hb : natLt slot («FN2-CNS-ROWS» own) = true)
    : put (coreWorld world coreTuple) (drainFrame id slot budget) st (leasePairs ) =
      .ok (setStobj (setStobj st "FN2-CNS" (leaseOwn slot  own)) "FN2-MACHINES" dir) := by
  let f := drainFrame id slot budget
  let pairs := leasePairs
  have hp : (natLt slot («FN2-CNS-ROWS» own) &&
      ((pairs.filter fun p => directoryFields.contains p.1).isEmpty || natLt id («FN2-MACHINES-ROWS» dir)) &&
      pairs.all (fun (n,v) => match f.kind.columns.find? (·.1 == n) with
        | some (_,ty) => ty.fits v | none => false)) = true := by
    change ((natLt slot («FN2-CNS-ROWS» own) && (true || natLt id («FN2-MACHINES-ROWS» dir))) && (true && (true && (true && true)))) = _
    simp only [hb, Bool.and_true, Bool.true_and, Bool.or_true, Bool.true_or, Bool.false_or]
  rw [put_pass (coreWorld world coreTuple) f st pairs slot id own dir control
    («FN2-CNS-ROWS» own) («FN2-MACHINES-ROWS» dir)
    hs hi ho hd hc («FN2-CNS-ROWS».core_call _) («FN2-MACHINES-ROWS».core_call _) hp]
  have hf : f.kind.name = "FN2-CNS" := by rfl
  have hop : pairs.filter (fun p => !directoryFields.contains p.1) = [("LEASE",.int 0), ("LSLOT",.int 4294967295), ("LGEN",.int 0)] := by rfl
  have hdp : pairs.filter (fun p => directoryFields.contains p.1) = [] := by rfl
  rw [hop, hdp, hf]
  simp only [List.foldlM_cons, List.foldlM_nil, except_ok_bind, «FN2-CNS-SET-LEASE».core_call, «FN2-CNS-SET-LSLOT».core_call, «FN2-CNS-SET-LGEN».core_call]
  rfl

def cleanupPairs (phase : Val) (gen : Val) (next : Val) : List (String × Val) := [("GENERATION",gen), ("CTL",.int 4294967295), ("CTL-GEN",.int 0), ("EDGE",.int 4294967295), ("TXN",.int 4294967295), ("TXN-GEN",.int 0), ("UPLOAD",.int 4294967295), ("UPLOAD-GEN",.int 0), ("TX-SLOT",.int 4294967295), ("TX-GEN",.int 0), ("NEXT-FREE",next), ("WAIT-REASON",.int 0), ("PHASE",phase)]

theorem cleanup_put (id slot budget own dir control : Val) (phase : Val) (gen : Val) (next : Val) (st : St)
    (hi : var st "ID" = .ok id) (hs : var st "SLOT" = .ok slot)
    (ho : stobj st "FN2-CNS" = .ok own) (hd : stobj st "FN2-MACHINES" = .ok dir)
    (hc : stobj st "FN2-CONTROL" = .ok control)
    (hb : natLt slot («FN2-CNS-ROWS» own) = true)
    (hdb : natLt id («FN2-MACHINES-ROWS» dir) = true)
    (hphase : ColType.fits (.enum 12) phase = true)
    : put (coreWorld world coreTuple) (drainFrame id slot budget) st (cleanupPairs phase gen next) =
      if cleanupFits gen next then .ok (setStobj (setStobj st "FN2-CNS" (cleanupOwn slot phase gen next own)) "FN2-MACHINES" («FN2-MACHINES-SET-WAIT-REASON» id (.int 0) dir))
      else .ok (setStobj st "FN2-CONTROL" («FN2-CONTROL-RECORD-STOP» (.int 13) control)) := by
  let f := drainFrame id slot budget
  let pairs := cleanupPairs phase gen next
  have hp : (natLt slot («FN2-CNS-ROWS» own) &&
      ((pairs.filter fun p => directoryFields.contains p.1).isEmpty || natLt id («FN2-MACHINES-ROWS» dir)) &&
      pairs.all (fun (n,v) => match f.kind.columns.find? (·.1 == n) with
        | some (_,ty) => ty.fits v | none => false)) = cleanupFits gen next := by
    change ((natLt slot («FN2-CNS-ROWS» own) && (false || natLt id («FN2-MACHINES-ROWS» dir))) && (ColType.fits (.uw 60) gen && (true && (true && (true && (true && (true && (true && (true && (true && (true && (ColType.fits (.uw 32) next && (true && (ColType.fits (.enum 12) phase && true)))))))))))))) = _
    simp only [hb, hdb, hphase, cleanupFits, Bool.and_true, Bool.true_and, Bool.or_true, Bool.true_or, Bool.false_or]
  by_cases hfit : cleanupFits gen next = true
  · rw [if_pos hfit]
    rw [put_pass (coreWorld world coreTuple) f st pairs slot id own dir control
      («FN2-CNS-ROWS» own) («FN2-MACHINES-ROWS» dir)
      hs hi ho hd hc («FN2-CNS-ROWS».core_call _) («FN2-MACHINES-ROWS».core_call _) (hp.trans hfit)]
    have hf : f.kind.name = "FN2-CNS" := by rfl
    have hop : pairs.filter (fun p => !directoryFields.contains p.1) = [("GENERATION",gen), ("CTL",.int 4294967295), ("CTL-GEN",.int 0), ("EDGE",.int 4294967295), ("TXN",.int 4294967295), ("TXN-GEN",.int 0), ("UPLOAD",.int 4294967295), ("UPLOAD-GEN",.int 0), ("TX-SLOT",.int 4294967295), ("TX-GEN",.int 0), ("NEXT-FREE",next), ("PHASE",phase)] := by rfl
    have hdp : pairs.filter (fun p => directoryFields.contains p.1) = [("WAIT-REASON",.int 0)] := by rfl
    rw [hop, hdp, hf]
    simp only [List.foldlM_cons, List.foldlM_nil, except_ok_bind, «FN2-CNS-SET-GENERATION».core_call, «FN2-CNS-SET-CTL».core_call, «FN2-CNS-SET-CTL-GEN».core_call, «FN2-CNS-SET-EDGE».core_call, «FN2-CNS-SET-TXN».core_call, «FN2-CNS-SET-TXN-GEN».core_call, «FN2-CNS-SET-UPLOAD».core_call, «FN2-CNS-SET-UPLOAD-GEN».core_call, «FN2-CNS-SET-TX-SLOT».core_call, «FN2-CNS-SET-TX-GEN».core_call, «FN2-CNS-SET-NEXT-FREE».core_call, «FN2-MACHINES-SET-WAIT-REASON».core_call, «FN2-CNS-SET-PHASE».core_call]
    rfl
  · rw [if_neg hfit]
    have hn : cleanupFits gen next = false := Bool.eq_false_iff.mpr hfit
    rw [put_fail (coreWorld world coreTuple) f st pairs slot id own dir control
      («FN2-CNS-ROWS» own) («FN2-MACHINES-ROWS» dir)
      hs hi ho hd hc («FN2-CNS-ROWS».core_call _) («FN2-MACHINES-ROWS».core_call _) (hp.trans hn)]
    have hr : const (coreWorld world coreTuple) "*FN2-STOP-REASON-MACHINE-WRITE*" = .ok (.int 13) := by rfl
    simp only [hr, except_ok_bind, «FN2-CONTROL-RECORD-STOP».core_call]
    rfl

def form (name : String) (args : List Expr) : Expr := Val.ofList (.sym name :: args)
def leasePending : List (String × Expr) :=
  [("LEASE",.sym "*FN2-CNS-LEASE-NONE*"),("LSLOT",.sym "*FN2-NONE*"),("LGEN",.int 0)]
def cleanupPending : List (String × Expr) :=
  [("GENERATION",form "IF" [.sym "RETIRE",.sym "ROW-GENERATION",form "+" [.int 1,.sym "ROW-GENERATION"]]),
   ("CTL",.sym "*FN2-NONE*"),("CTL-GEN",.int 0),("EDGE",.sym "*FN2-NONE*"),
   ("TXN",.sym "*FN2-NONE*"),("TXN-GEN",.int 0),("UPLOAD",.sym "*FN2-NONE*"),("UPLOAD-GEN",.int 0),
   ("TX-SLOT",.sym "*FN2-NONE*"),("TX-GEN",.int 0),("NEXT-FREE",.sym "NEXT"),("WAIT-REASON",.sym "*FN2-WAIT-NONE*")]
def cleanupNext : Expr := form ":IF" [.sym "RETIRE",.sym ":RETIRED",.sym ":FREE"]
def releaseCall : Call := ⟨"FN2-CNS-LEASE-RELEASE",[.sym "ROW-LSLOT",.sym "ROW-LGEN"],[]⟩
def reclaimCall : Call := ⟨"FN2-CNS-RECLAIM",[.sym "ID",.sym "*FN2-CNS-ADMISSION-ORDINAL*",.sym "RETIRE"],[]⟩
def leaseSteps : List Step :=
  [.do_ ["LC"] releaseCall true [.sym ":OK",.sym ":RETIRED"] none [] [],
   .set leasePending,.charge none (some (.sym "*FN2-WORK-TRANSITION*")) none (some Val.t)]
def cleanupSteps : List Step :=
  [.let_ "NEXT" (form "FN2-MACHINE-FREE-HEAD" [.sym "*FN2-CNS-ADMISSION-ORDINAL*"]),
   .let_ "RETIRE" (form ">=" [.sym "ROW-GENERATION",form "FN2-MACHINE-GEN-LIMIT" []]),
   .set cleanupPending,.next cleanupNext,
   .do_ [] reclaimCall false [] none [] [],
   .charge none (some (.sym "*FN2-WORK-RELEASE*")) none none]
def drainingSteps : List Step :=
  [.cond [(form "EQUAL" [.sym "ROW-LEASE",.sym "*FN2-CNS-LEASE-HELD*"],leaseSteps),(Val.t,cleanupSteps)]]

theorem draining_read_by_definition :
    draining.read = .ok ⟨[],[.stop "MACHINE-PHASE" none],drainingSteps⟩ := by
  with_unfolding_all rfl

def drainState (id slot budget : Val) (kids : Fin 57 → Val) : St :=
  { stobjs := coreTuple.zip [(kids ⟨0, by decide⟩), (kids ⟨1, by decide⟩), (kids ⟨2, by decide⟩), (kids ⟨3, by decide⟩), (kids ⟨4, by decide⟩), (kids ⟨5, by decide⟩), (kids ⟨6, by decide⟩), (kids ⟨7, by decide⟩), (kids ⟨8, by decide⟩), (kids ⟨9, by decide⟩), (kids ⟨10, by decide⟩), (kids ⟨11, by decide⟩), (kids ⟨12, by decide⟩), (kids ⟨13, by decide⟩), (kids ⟨14, by decide⟩), (kids ⟨15, by decide⟩), (kids ⟨16, by decide⟩), (kids ⟨17, by decide⟩), (kids ⟨18, by decide⟩), (kids ⟨19, by decide⟩), (kids ⟨20, by decide⟩), (kids ⟨21, by decide⟩), (kids ⟨22, by decide⟩), (kids ⟨23, by decide⟩), (kids ⟨24, by decide⟩), (kids ⟨25, by decide⟩), (kids ⟨26, by decide⟩), (kids ⟨27, by decide⟩), (kids ⟨28, by decide⟩), (kids ⟨29, by decide⟩), (kids ⟨30, by decide⟩), (kids ⟨31, by decide⟩), (kids ⟨32, by decide⟩), (kids ⟨33, by decide⟩), (kids ⟨34, by decide⟩), (kids ⟨35, by decide⟩), (kids ⟨36, by decide⟩), (kids ⟨37, by decide⟩), (kids ⟨38, by decide⟩), (kids ⟨39, by decide⟩), (kids ⟨40, by decide⟩), (kids ⟨41, by decide⟩), (kids ⟨42, by decide⟩), (kids ⟨43, by decide⟩), (kids ⟨44, by decide⟩), (kids ⟨45, by decide⟩), (kids ⟨46, by decide⟩), (kids ⟨47, by decide⟩), (kids ⟨48, by decide⟩), (kids ⟨49, by decide⟩), (kids ⟨50, by decide⟩), (kids ⟨51, by decide⟩), (kids ⟨52, by decide⟩), (kids ⟨53, by decide⟩), (kids ⟨54, by decide⟩), (kids ⟨55, by decide⟩), (kids ⟨56, by decide⟩)],
    vars := [("ROW-PHASE", «FN2-CNS-PHASE» slot (kids ⟨17, by decide⟩)), ("ROW-GENERATION", «FN2-CNS-GENERATION» slot (kids ⟨17, by decide⟩)), ("ROW-PRINCIPAL-SLOT", «FN2-CNS-PRINCIPAL-SLOT» slot (kids ⟨17, by decide⟩)), ("ROW-ACCOUNT-REF", «FN2-CNS-ACCOUNT-REF» slot (kids ⟨17, by decide⟩)), ("ROW-READY-PREV", «FN2-MACHINES-READY-PREV» id (kids ⟨3, by decide⟩)), ("ROW-READY-NEXT", «FN2-MACHINES-READY-NEXT» id (kids ⟨3, by decide⟩)), ("ROW-WAIT-REASON", «FN2-MACHINES-WAIT-REASON» id (kids ⟨3, by decide⟩)), ("ROW-DEADLINE", «FN2-CNS-DEADLINE» slot (kids ⟨17, by decide⟩)), ("ROW-CTL", «FN2-CNS-CTL» slot (kids ⟨17, by decide⟩)), ("ROW-CTL-GEN", «FN2-CNS-CTL-GEN» slot (kids ⟨17, by decide⟩)), ("ROW-REQUEST", «FN2-CNS-REQUEST» slot (kids ⟨17, by decide⟩)), ("ROW-FPOS", «FN2-CNS-FPOS» slot (kids ⟨17, by decide⟩)), ("ROW-FLEN", «FN2-CNS-FLEN» slot (kids ⟨17, by decide⟩)), ("ROW-FKIND", «FN2-CNS-FKIND» slot (kids ⟨17, by decide⟩)), ("ROW-VERB", «FN2-CNS-VERB» slot (kids ⟨17, by decide⟩)), ("ROW-CONSUMER", «FN2-CNS-CONSUMER» slot (kids ⟨17, by decide⟩)), ("ROW-EPOCH", «FN2-CNS-EPOCH» slot (kids ⟨17, by decide⟩)), ("ROW-OP", «FN2-CNS-OP» slot (kids ⟨17, by decide⟩)), ("ROW-TO", «FN2-CNS-TO» slot (kids ⟨17, by decide⟩)), ("ROW-CSTART", «FN2-CNS-CSTART» slot (kids ⟨17, by decide⟩)), ("ROW-PAGE-LIMIT", «FN2-CNS-PAGE-LIMIT» slot (kids ⟨17, by decide⟩)), ("ROW-WAIT-MS", «FN2-CNS-WAIT-MS» slot (kids ⟨17, by decide⟩)), ("ROW-CPOS", «FN2-CNS-CPOS» slot (kids ⟨17, by decide⟩)), ("ROW-VERSION", «FN2-CNS-VERSION» slot (kids ⟨17, by decide⟩)), ("ROW-PUB-FRONTIER", «FN2-CNS-PUB-FRONTIER» slot (kids ⟨17, by decide⟩)), ("ROW-COUNT", «FN2-CNS-COUNT» slot (kids ⟨17, by decide⟩)), ("ROW-MORE", «FN2-CNS-MORE» slot (kids ⟨17, by decide⟩)), ("ROW-OUTCOME", «FN2-CNS-OUTCOME» slot (kids ⟨17, by decide⟩)), ("ROW-REASON", «FN2-CNS-REASON» slot (kids ⟨17, by decide⟩)), ("ROW-POSTED", «FN2-CNS-POSTED» slot (kids ⟨17, by decide⟩)), ("ROW-POSTED-WORD", «FN2-CNS-POSTED-WORD» slot (kids ⟨17, by decide⟩)), ("ROW-EDGE", «FN2-CNS-EDGE» slot (kids ⟨17, by decide⟩)), ("ROW-TXN", «FN2-CNS-TXN» slot (kids ⟨17, by decide⟩)), ("ROW-TXN-GEN", «FN2-CNS-TXN-GEN» slot (kids ⟨17, by decide⟩)), ("ROW-TX-SLOT", «FN2-CNS-TX-SLOT» slot (kids ⟨17, by decide⟩)), ("ROW-TX-GEN", «FN2-CNS-TX-GEN» slot (kids ⟨17, by decide⟩)), ("ROW-UPLOAD", «FN2-CNS-UPLOAD» slot (kids ⟨17, by decide⟩)), ("ROW-UPLOAD-GEN", «FN2-CNS-UPLOAD-GEN» slot (kids ⟨17, by decide⟩)), ("ROW-FSTART", «FN2-CNS-FSTART» slot (kids ⟨17, by decide⟩)), ("ROW-FED", «FN2-CNS-FED» slot (kids ⟨17, by decide⟩)), ("ROW-FEED-MODE", «FN2-CNS-FEED-MODE» slot (kids ⟨17, by decide⟩)), ("ROW-FEED-DISCARD", «FN2-CNS-FEED-DISCARD» slot (kids ⟨17, by decide⟩)), ("ROW-NAME-OFF", «FN2-CNS-NAME-OFF» slot (kids ⟨17, by decide⟩)), ("ROW-NAME-LEN", «FN2-CNS-NAME-LEN» slot (kids ⟨17, by decide⟩)), ("ROW-XSTEP", «FN2-CNS-XSTEP» slot (kids ⟨17, by decide⟩)), ("ROW-XHEAD", «FN2-CNS-XHEAD» slot (kids ⟨17, by decide⟩)), ("ROW-XGRANT", «FN2-CNS-XGRANT» slot (kids ⟨17, by decide⟩)), ("ROW-IPOS", «FN2-CNS-IPOS» slot (kids ⟨17, by decide⟩)), ("ROW-IOFF", «FN2-CNS-IOFF» slot (kids ⟨17, by decide⟩)), ("ROW-ILEN", «FN2-CNS-ILEN» slot (kids ⟨17, by decide⟩)), ("ROW-NPOS", «FN2-CNS-NPOS» slot (kids ⟨17, by decide⟩)), ("ROW-ART", «FN2-CNS-ART» slot (kids ⟨17, by decide⟩)), ("ROW-ISTREAM", «FN2-CNS-ISTREAM» slot (kids ⟨17, by decide⟩)), ("ROW-ITYPE", «FN2-CNS-ITYPE» slot (kids ⟨17, by decide⟩)), ("ROW-ALEN", «FN2-CNS-ALEN» slot (kids ⟨17, by decide⟩)), ("ROW-LUNIT", «FN2-CNS-LUNIT» slot (kids ⟨17, by decide⟩)), ("ROW-LEPOCH", «FN2-CNS-LEPOCH» slot (kids ⟨17, by decide⟩)), ("ROW-LALLOC", «FN2-CNS-LALLOC» slot (kids ⟨17, by decide⟩)), ("ROW-LSLOT", «FN2-CNS-LSLOT» slot (kids ⟨17, by decide⟩)), ("ROW-LGEN", «FN2-CNS-LGEN» slot (kids ⟨17, by decide⟩)), ("ROW-LEASE", «FN2-CNS-LEASE» slot (kids ⟨17, by decide⟩)), ("ROW-REVENT", «FN2-CNS-REVENT» slot (kids ⟨17, by decide⟩)), ("ROW-ROUTCOME", «FN2-CNS-ROUTCOME» slot (kids ⟨17, by decide⟩)), ("ROW-RCOUNT", «FN2-CNS-RCOUNT» slot (kids ⟨17, by decide⟩)), ("ROW-RREADY", «FN2-CNS-RREADY» slot (kids ⟨17, by decide⟩)), ("ROW-PENDING", «FN2-CNS-PENDING» slot (kids ⟨17, by decide⟩)), ("ROW-CURSOR", «FN2-CNS-CURSOR» slot (kids ⟨17, by decide⟩)), ("ROW-XROW", «FN2-CNS-XROW» slot (kids ⟨17, by decide⟩)), ("ROW-STOPPED", «FN2-CNS-STOPPED» slot (kids ⟨17, by decide⟩)), ("ROW-NEXT-FREE", «FN2-CNS-NEXT-FREE» slot (kids ⟨17, by decide⟩))] ++ drainBase id slot budget }

theorem drain_entry (fuel : Nat) (id slot budget : Val) (kids : Fin 57 → Val) :
    runArm (coreWorld world coreTuple) (coreKind cns coreTuple) draining false
      ([id,slot,.int 11,.int 6,budget] ++ [(kids ⟨0, by decide⟩), (kids ⟨1, by decide⟩), (kids ⟨2, by decide⟩), (kids ⟨3, by decide⟩), (kids ⟨4, by decide⟩), (kids ⟨5, by decide⟩), (kids ⟨6, by decide⟩), (kids ⟨7, by decide⟩), (kids ⟨8, by decide⟩), (kids ⟨9, by decide⟩), (kids ⟨10, by decide⟩), (kids ⟨11, by decide⟩), (kids ⟨12, by decide⟩), (kids ⟨13, by decide⟩), (kids ⟨14, by decide⟩), (kids ⟨15, by decide⟩), (kids ⟨16, by decide⟩), (kids ⟨17, by decide⟩), (kids ⟨18, by decide⟩), (kids ⟨19, by decide⟩), (kids ⟨20, by decide⟩), (kids ⟨21, by decide⟩), (kids ⟨22, by decide⟩), (kids ⟨23, by decide⟩), (kids ⟨24, by decide⟩), (kids ⟨25, by decide⟩), (kids ⟨26, by decide⟩), (kids ⟨27, by decide⟩), (kids ⟨28, by decide⟩), (kids ⟨29, by decide⟩), (kids ⟨30, by decide⟩), (kids ⟨31, by decide⟩), (kids ⟨32, by decide⟩), (kids ⟨33, by decide⟩), (kids ⟨34, by decide⟩), (kids ⟨35, by decide⟩), (kids ⟨36, by decide⟩), (kids ⟨37, by decide⟩), (kids ⟨38, by decide⟩), (kids ⟨39, by decide⟩), (kids ⟨40, by decide⟩), (kids ⟨41, by decide⟩), (kids ⟨42, by decide⟩), (kids ⟨43, by decide⟩), (kids ⟨44, by decide⟩), (kids ⟨45, by decide⟩), (kids ⟨46, by decide⟩), (kids ⟨47, by decide⟩), (kids ⟨48, by decide⟩), (kids ⟨49, by decide⟩), (kids ⟨50, by decide⟩), (kids ⟨51, by decide⟩), (kids ⟨52, by decide⟩), (kids ⟨53, by decide⟩), (kids ⟨54, by decide⟩), (kids ⟨55, by decide⟩), (kids ⟨56, by decide⟩)]) fuel =
    (do match ← run (coreWorld world coreTuple) (drainFrame id slot budget) fuel
          (drainState id slot budget kids) drainingSteps with
        | .done v => pure v
        | .again _ => throw ":repeat-next outside a :repeat") := by
  unfold runArm
  simp only [coreKind, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_append,
    List.length_cons, List.length_nil]
  have hl : coreTuple.length = 57 := by rfl
  simp only [hl]
  change (do
    let reads ← rowReads (coreWorld world coreTuple) (coreKind cns coreTuple)
      (coreTuple.zip [(kids ⟨0, by decide⟩), (kids ⟨1, by decide⟩), (kids ⟨2, by decide⟩), (kids ⟨3, by decide⟩), (kids ⟨4, by decide⟩), (kids ⟨5, by decide⟩), (kids ⟨6, by decide⟩), (kids ⟨7, by decide⟩), (kids ⟨8, by decide⟩), (kids ⟨9, by decide⟩), (kids ⟨10, by decide⟩), (kids ⟨11, by decide⟩), (kids ⟨12, by decide⟩), (kids ⟨13, by decide⟩), (kids ⟨14, by decide⟩), (kids ⟨15, by decide⟩), (kids ⟨16, by decide⟩), (kids ⟨17, by decide⟩), (kids ⟨18, by decide⟩), (kids ⟨19, by decide⟩), (kids ⟨20, by decide⟩), (kids ⟨21, by decide⟩), (kids ⟨22, by decide⟩), (kids ⟨23, by decide⟩), (kids ⟨24, by decide⟩), (kids ⟨25, by decide⟩), (kids ⟨26, by decide⟩), (kids ⟨27, by decide⟩), (kids ⟨28, by decide⟩), (kids ⟨29, by decide⟩), (kids ⟨30, by decide⟩), (kids ⟨31, by decide⟩), (kids ⟨32, by decide⟩), (kids ⟨33, by decide⟩), (kids ⟨34, by decide⟩), (kids ⟨35, by decide⟩), (kids ⟨36, by decide⟩), (kids ⟨37, by decide⟩), (kids ⟨38, by decide⟩), (kids ⟨39, by decide⟩), (kids ⟨40, by decide⟩), (kids ⟨41, by decide⟩), (kids ⟨42, by decide⟩), (kids ⟨43, by decide⟩), (kids ⟨44, by decide⟩), (kids ⟨45, by decide⟩), (kids ⟨46, by decide⟩), (kids ⟨47, by decide⟩), (kids ⟨48, by decide⟩), (kids ⟨49, by decide⟩), (kids ⟨50, by decide⟩), (kids ⟨51, by decide⟩), (kids ⟨52, by decide⟩), (kids ⟨53, by decide⟩), (kids ⟨54, by decide⟩), (kids ⟨55, by decide⟩), (kids ⟨56, by decide⟩)]) id slot
    let d ← draining.read
    let f : Frame := { kind := coreKind cns coreTuple, observe := false, refusal := d.onRefusal, base := drainBase id slot budget }
    match ← run (coreWorld world coreTuple) f fuel
      { stobjs := coreTuple.zip [(kids ⟨0, by decide⟩), (kids ⟨1, by decide⟩), (kids ⟨2, by decide⟩), (kids ⟨3, by decide⟩), (kids ⟨4, by decide⟩), (kids ⟨5, by decide⟩), (kids ⟨6, by decide⟩), (kids ⟨7, by decide⟩), (kids ⟨8, by decide⟩), (kids ⟨9, by decide⟩), (kids ⟨10, by decide⟩), (kids ⟨11, by decide⟩), (kids ⟨12, by decide⟩), (kids ⟨13, by decide⟩), (kids ⟨14, by decide⟩), (kids ⟨15, by decide⟩), (kids ⟨16, by decide⟩), (kids ⟨17, by decide⟩), (kids ⟨18, by decide⟩), (kids ⟨19, by decide⟩), (kids ⟨20, by decide⟩), (kids ⟨21, by decide⟩), (kids ⟨22, by decide⟩), (kids ⟨23, by decide⟩), (kids ⟨24, by decide⟩), (kids ⟨25, by decide⟩), (kids ⟨26, by decide⟩), (kids ⟨27, by decide⟩), (kids ⟨28, by decide⟩), (kids ⟨29, by decide⟩), (kids ⟨30, by decide⟩), (kids ⟨31, by decide⟩), (kids ⟨32, by decide⟩), (kids ⟨33, by decide⟩), (kids ⟨34, by decide⟩), (kids ⟨35, by decide⟩), (kids ⟨36, by decide⟩), (kids ⟨37, by decide⟩), (kids ⟨38, by decide⟩), (kids ⟨39, by decide⟩), (kids ⟨40, by decide⟩), (kids ⟨41, by decide⟩), (kids ⟨42, by decide⟩), (kids ⟨43, by decide⟩), (kids ⟨44, by decide⟩), (kids ⟨45, by decide⟩), (kids ⟨46, by decide⟩), (kids ⟨47, by decide⟩), (kids ⟨48, by decide⟩), (kids ⟨49, by decide⟩), (kids ⟨50, by decide⟩), (kids ⟨51, by decide⟩), (kids ⟨52, by decide⟩), (kids ⟨53, by decide⟩), (kids ⟨54, by decide⟩), (kids ⟨55, by decide⟩), (kids ⟨56, by decide⟩)], vars := reads ++ f.base } d.steps with
    | .done v => pure v
    | .again _ => throw ":repeat-next outside a :repeat") = _
  rw [cns_row_reads, draining_read_by_definition]
  rfl

theorem ev_var_of_read (st : St) (name : String) (value : Val)
    (hr : readExpr (coreWorld world coreTuple) (coreKind cns coreTuple) (.sym name) = .ok (.var name))
    (hv : (st.vars ++ st.stobjs).get? name = some value) :
    ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.sym name) = .ok value := by
  simp only [ev, hr, except_ok_bind, Term.eval, hv]

theorem ev_quote_of_read (st : St) (e : Expr) (value : Val)
    (hr : readExpr (coreWorld world coreTuple) (coreKind cns coreTuple) e = .ok (.quote value)) :
    ev (coreWorld world coreTuple) (coreKind cns coreTuple) st e = .ok value := by
  simp only [ev, hr, except_ok_bind, Term.eval]

theorem ev_lease_test (st : St) (lease : Val)
    (hv : (st.vars ++ st.stobjs).get? "ROW-LEASE" = some lease) :
    ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (form "EQUAL" [.sym "ROW-LEASE",.sym "*FN2-CNS-LEASE-HELD*"]) =
      .ok (Prim.equal lease (.int 1)) := by
  have hr : readExpr (coreWorld world coreTuple) (coreKind cns coreTuple)
      (form "EQUAL" [.sym "ROW-LEASE",.sym "*FN2-CNS-LEASE-HELD*"]) =
      .ok (.app "EQUAL" [.var "ROW-LEASE",.quote (.int 1)]) := by with_unfolding_all rfl
  simp only [ev, hr, except_ok_bind]
  rw [Term.eval.eq_5 _ _ "EQUAL" _ (by simp) (by simp)]
  simp only [Term.eval, List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, hv, except_ok_bind]
  rfl

theorem eval_gen_limit (env : Env) (dir : Val) (hd : env.get? "FN2-MACHINES" = some dir) :
    Term.eval (coreWorld world coreTuple).fns env (.app "FN2-MACHINES-GEN-LIMIT" [.var "FN2-MACHINES"]) =
      .ok («FN2-MACHINES-GEN-LIMIT» dir) := by
  rw [Term.eval.eq_5 _ _ "FN2-MACHINES-GEN-LIMIT" _ (by simp) (by simp)]
  simp only [Term.eval, List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
    hd, except_ok_bind]
  have hf : "FN2-MACHINES-GEN-LIMIT".endsWith "@CORE" = false := by decide +kernel
  simpa only [coreWorld, coreFns, hf, Bool.false_eq_true, if_false] using
    (Fn2.Instances.CoreWorld.«FN2-MACHINES-GEN-LIMIT».dispatched
      (err := "no function FN2-MACHINES-GEN-LIMIT of arity 1") dir)

theorem ev_free_head (st : St) (dir : Val)
    (ho : (st.vars ++ st.stobjs).get? "ORDINAL" = some (.int 6))
    (hd : (st.vars ++ st.stobjs).get? "FN2-MACHINES" = some dir) :
    ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (form "FN2-MACHINE-FREE-HEAD" [.sym "*FN2-CNS-ADMISSION-ORDINAL*"]) =
      .ok («FN2-MACHINES-FREE-HEAD-OF» (.int 6) dir) := by
  have hr : readExpr (coreWorld world coreTuple) (coreKind cns coreTuple)
      (form "FN2-MACHINE-FREE-HEAD" [.sym "*FN2-CNS-ADMISSION-ORDINAL*"]) =
      .ok (.app "FN2-MACHINES-FREE-HEAD-OF" [.var "ORDINAL",.var "FN2-MACHINES"]) := by with_unfolding_all rfl
  simp only [ev, hr, except_ok_bind]
  rw [Term.eval.eq_5 _ _ "FN2-MACHINES-FREE-HEAD-OF" _ (by simp) (by simp)]
  simp only [Term.eval, List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, ho, hd, except_ok_bind]
  have hf : "FN2-MACHINES-FREE-HEAD-OF".endsWith "@CORE" = false := by decide +kernel
  simpa only [coreWorld, coreFns, hf, Bool.false_eq_true, if_false] using
    (Fn2.Instances.CoreWorld.«FN2-MACHINES-FREE-HEAD-OF».dispatched
      (err := "no function FN2-MACHINES-FREE-HEAD-OF of arity 2") (.int 6) dir)

/-- Reconstruct the full parent while replacing exactly the operation's children. -/
def patchKids (kids : Fin 57 → Val) (pool dir control own : Val) : Fin 57 → Val := fun i =>
  if i.val = 0 then pool else if i.val = 3 then dir else if i.val = 5 then control
  else if i.val = 17 then own else kids i

theorem release_result_shape (slot gen kind id generation pool control : Val) :
    let r := «FN2-CORE-RELEASE-CHILDREN» slot gen kind id generation pool control
    r = Val.ofList [r.car,r.cdr.car,r.cdr.cdr.car] := by rfl

theorem reclaim_result_shape (id ord retire dir control : Val) :
    let r := «FN2-MACHINES-RECLAIM» id ord retire dir control
    r = Val.ofList [r.car,r.cdr.car] := by
  dsimp only
  unfold «FN2-MACHINES-RECLAIM»
  simp only [«FN2-MACHINES-STOP-WRITE»]
  repeat' first | rfl | split

theorem release_adapter (slot gen id generation : Val) (kids : Fin 57 → Val) :
    let r := «FN2-CORE-RELEASE-CHILDREN» slot gen (.int 11) id generation (kids ⟨0,by decide⟩) (kids ⟨5,by decide⟩)
    «FN2-CNS-LEASE-RELEASE» slot gen (.int 11) id generation (coreImage kids) =
      Val.ofList [r.car, coreImage (patchKids kids r.cdr.car (kids ⟨3,by decide⟩) r.cdr.cdr.car (kids ⟨17,by decide⟩))] := by rfl

theorem reclaim_adapter (id retire : Val) (kids : Fin 57 → Val) :
    let r := «FN2-MACHINES-RECLAIM» id (.int 6) retire (kids ⟨3,by decide⟩) (kids ⟨5,by decide⟩)
    «FN2-CNS-RECLAIM» id (.int 6) retire (coreImage kids) =
      coreImage (patchKids kids (kids ⟨0,by decide⟩) r.car r.cdr.car (kids ⟨17,by decide⟩)) := by
  have h0 (r : Val) : Native.nth (.int 0) r = r.car := by cases r <;> rfl
  have h1 (r : Val) : Native.nth (.int 1) r = r.cdr.car := by
    cases r <;> first | rfl | exact h0 _
  dsimp only
  unfold «FN2-CNS-RECLAIM»
  simp only [h0, h1]
  rfl

theorem snapshot_pool_control_frame (id pool control : Val) (kids : Fin 57 → Val) :
    «FN2-CNS-SNAPSHOT-READ-CODE» id
      (coreImage (patchKids kids pool (kids ⟨3,by decide⟩) control (kids ⟨17,by decide⟩))) =
    «FN2-CNS-SNAPSHOT-READ-CODE» id (coreImage kids) := by rfl

theorem slot_pool_control_frame (id pool control : Val) (kids : Fin 57 → Val) :
    «FN2-MACHINE-SLOT» id
      (coreImage (patchKids kids pool (kids ⟨3,by decide⟩) control (kids ⟨17,by decide⟩))) =
    «FN2-MACHINE-SLOT» id (coreImage kids) := by rfl

theorem flush_lease (id slot budget own dir control : Val) (st : St)
    (hp : st.pending = leasePending) (hn : st.next = none)
    (hi : var st "ID" = .ok id) (hs : var st "SLOT" = .ok slot)
    (ho : stobj st "FN2-CNS" = .ok own) (hd : stobj st "FN2-MACHINES" = .ok dir)
    (hc : stobj st "FN2-CONTROL" = .ok control)
    (hb : natLt slot («FN2-CNS-ROWS» own) = true) :
    flush (coreWorld world coreTuple) (drainFrame id slot budget) st =
    .ok { (setStobj (setStobj st "FN2-CNS" (leaseOwn slot own)) "FN2-MACHINES" dir)
      with pending := [], next := none, nextDone := st.nextDone } := by
  have e0 : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (.sym "*FN2-CNS-LEASE-NONE*") = .ok (.int 0) :=
    ev_quote_of_read st _ _ (by with_unfolding_all rfl)
  have en : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (.sym "*FN2-NONE*") = .ok (.int 4294967295) :=
    ev_quote_of_read st _ _ (by with_unfolding_all rfl)
  have ez : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.int 0) = .ok (.int 0) :=
    ev_quote_of_read st _ _ (by rfl)
  have hk : (drainFrame id slot budget).kind = coreKind cns coreTuple := by rfl
  simp only [flush, hp, hn, hk, leasePending, List.mapM_cons, List.mapM_nil,
    e0, en, ez, except_ok_bind]
  change (do
    let st' ← put (coreWorld world coreTuple) (drainFrame id slot budget) st leasePairs
    pure { st' with pending := [], next := none, nextDone := st.nextDone || false }) = _
  rw [lease_put id slot budget own dir control st hi hs ho hd hc hb]
  simp only [except_ok_bind, Bool.or_false]
  rfl

def releaseOp : Op := world.ops[1]!
def reclaimOp : Op := world.ops[0]!

theorem ev_var_expression (st : St) (expr : Expr) (name : String) (value : Val)
    (hr : readExpr (coreWorld world coreTuple) (coreKind cns coreTuple) expr = .ok (.var name))
    (hv : var st name = .ok value) :
    ev (coreWorld world coreTuple) (coreKind cns coreTuple) st expr = .ok value := by
  simp only [ev, hr, except_ok_bind, Term.eval, var_env_bound st name value hv]

theorem release_call (lslot : Val) (lgen : Val) (id : Val) (generation : Val) (pool : Val) (control : Val) (st : St)
    (h_lslot : var st "ROW-LSLOT" = .ok lslot)
    (h_lgen : var st "ROW-LGEN" = .ok lgen)
    (h_id : var st "ID" = .ok id)
    (h_generation : var st "ROW-GENERATION" = .ok generation)
    (h_kind : var st "KIND" = .ok (.int 11))
    (h_pool : stobj st "FN2-POOL" = .ok pool)
    (h_control : stobj st "FN2-CONTROL" = .ok control)
    : callOp (coreWorld world coreTuple) (coreKind cns coreTuple) st releaseCall =
      .ok (releaseOp, «FN2-CORE-RELEASE-CHILDREN» lslot lgen (.int 11) id generation pool control) := by
  have hop : findOp (coreWorld world coreTuple) releaseCall.op = .ok releaseOp := by rfl
  have hkeys : expandOwner (coreWorld world coreTuple) (coreKind cns coreTuple) [] = .ok [] := by rfl
  have e0 : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.sym "ROW-LSLOT") = .ok lslot :=
    ev_var_expression st _ _ _ (by with_unfolding_all rfl) h_lslot
  have e1 : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.sym "ROW-LGEN") = .ok lgen :=
    ev_var_expression st _ _ _ (by with_unfolding_all rfl) h_lgen
  have ha : actuals (coreWorld world coreTuple) (coreKind cns coreTuple) st
      releaseOp.formals releaseOp.stobjsIn releaseCall.args [] = .ok [lslot, lgen, (.int 11), id, generation, pool, control] := by
    change actuals (coreWorld world coreTuple) (coreKind cns coreTuple) st
      ["SLOT", "GEN", "OKIND", "OSLOT", "OGEN", "FN2-POOL", "FN2-CONTROL"]
      [none, none, none, none, none, (some "FN2-POOL"), (some "FN2-CONTROL")]
      [(.sym "ROW-LSLOT"), (.sym "ROW-LGEN")] [] = _
    dsimp only [actuals]
    simp only [e0, e1, h_lslot, h_lgen, h_id, h_generation, h_kind, h_pool, h_control, except_ok_bind]
    rfl
  unfold callOp
  rw [hop]
  simp only [except_ok_bind]
  change (do
    let keys ← expandOwner (coreWorld world coreTuple) (coreKind cns coreTuple) []
    let args ← actuals (coreWorld world coreTuple) (coreKind cns coreTuple) st releaseOp.formals releaseOp.stobjsIn releaseCall.args keys
    let r ← callFn (coreWorld world coreTuple) "FN2-CORE-RELEASE-CHILDREN" args
    pure (releaseOp,r)) = _
  simp only [hkeys, except_ok_bind, ha, «FN2-CORE-RELEASE-CHILDREN».core_call]
  rfl

theorem reclaim_call (id : Val) (retire : Val) (dir : Val) (control : Val) (st : St)
    (h_id : var st "ID" = .ok id)
    (h_retire : var st "RETIRE" = .ok retire)
    (h_ord : var st "ORDINAL" = .ok (.int 6))
    (h_dir : stobj st "FN2-MACHINES" = .ok dir)
    (h_control : stobj st "FN2-CONTROL" = .ok control)
    : callOp (coreWorld world coreTuple) (coreKind cns coreTuple) st reclaimCall =
      .ok (reclaimOp, «FN2-MACHINES-RECLAIM» id (.int 6) retire dir control) := by
  have hop : findOp (coreWorld world coreTuple) reclaimCall.op = .ok reclaimOp := by rfl
  have hkeys : expandOwner (coreWorld world coreTuple) (coreKind cns coreTuple) [] = .ok [] := by rfl
  have e0 : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.sym "ID") = .ok id :=
    ev_var_expression st _ _ _ (by with_unfolding_all rfl) h_id
  have e1 : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.sym "*FN2-CNS-ADMISSION-ORDINAL*") = .ok (.int 6) :=
    ev_var_expression st _ _ _ (by with_unfolding_all rfl) h_ord
  have e2 : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.sym "RETIRE") = .ok retire :=
    ev_var_expression st _ _ _ (by with_unfolding_all rfl) h_retire
  have ha : actuals (coreWorld world coreTuple) (coreKind cns coreTuple) st
      reclaimOp.formals reclaimOp.stobjsIn reclaimCall.args [] = .ok [id, (.int 6), retire, dir, control] := by
    change actuals (coreWorld world coreTuple) (coreKind cns coreTuple) st
      ["ID", "ORD", "RETIRE", "FN2-MACHINES", "FN2-CONTROL"]
      [none, none, none, (some "FN2-MACHINES"), (some "FN2-CONTROL")]
      [(.sym "ID"), (.sym "*FN2-CNS-ADMISSION-ORDINAL*"), (.sym "RETIRE")] [] = _
    dsimp only [actuals]
    simp only [e0, e1, e2, h_id, h_retire, h_ord, h_dir, h_control, except_ok_bind]
    rfl
  unfold callOp
  rw [hop]
  simp only [except_ok_bind]
  change (do
    let keys ← expandOwner (coreWorld world coreTuple) (coreKind cns coreTuple) []
    let args ← actuals (coreWorld world coreTuple) (coreKind cns coreTuple) st reclaimOp.formals reclaimOp.stobjsIn reclaimCall.args keys
    let r ← callFn (coreWorld world coreTuple) "FN2-MACHINES-RECLAIM" args
    pure (reclaimOp,r)) = _
  simp only [hkeys, except_ok_bind, ha, «FN2-MACHINES-RECLAIM».core_call]
  rfl

theorem ev_retire (st : St) (gen dir : Val)
    (hg : var st "ROW-GENERATION" = .ok gen)
    (hd : (st.vars ++ st.stobjs).get? "FN2-MACHINES" = some dir) :
    ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (form ">=" [.sym "ROW-GENERATION",form "FN2-MACHINE-GEN-LIMIT" []]) =
      .ok («NOT» (Prim.lt gen («FN2-MACHINES-GEN-LIMIT» dir))) := by
  let env := st.vars ++ st.stobjs
  have hr : readExpr (coreWorld world coreTuple) (coreKind cns coreTuple)
      (form ">=" [.sym "ROW-GENERATION",form "FN2-MACHINE-GEN-LIMIT" []]) =
      .ok (.app "IF" [.app "<" [.var "ROW-GENERATION",.app "FN2-MACHINES-GEN-LIMIT" [.var "FN2-MACHINES"]],
        .quote Val.nil,.quote Val.t]) := by with_unfolding_all rfl
  have eg : Term.eval (coreWorld world coreTuple).fns env (.var "ROW-GENERATION") = .ok gen := by
    simp only [env, Term.eval, var_env_bound st _ _ hg]
  have el := eval_gen_limit env dir hd
  have elt : Term.eval (coreWorld world coreTuple).fns env
      (.app "<" [.var "ROW-GENERATION",.app "FN2-MACHINES-GEN-LIMIT" [.var "FN2-MACHINES"]]) =
      .ok (Prim.lt gen («FN2-MACHINES-GEN-LIMIT» dir)) := by
    rw [Term.eval.eq_5 _ _ "<" _ (by simp) (by simp)]
    simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil,
      List.mapM_cons, List.mapM_nil, eg, el, except_ok_bind]
    rfl
  simp only [ev, hr, except_ok_bind]
  change Term.eval (coreWorld world coreTuple).fns env _ = _
  rw [Term.eval.eq_3]
  rw [elt]
  simp only [except_ok_bind]
  cases hh : (Prim.lt gen («FN2-MACHINES-GEN-LIMIT» dir)).truthy <;>
    simp [hh, Term.eval, «NOT»]

theorem ev_cleanup_generation (st : St) (retire gen : Val)
    (hrv : var st "RETIRE" = .ok retire) (hgv : var st "ROW-GENERATION" = .ok gen) :
    ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (form "IF" [.sym "RETIRE",.sym "ROW-GENERATION",form "+" [.int 1,.sym "ROW-GENERATION"]]) =
      .ok (if retire.truthy then gen else Prim.plus (.int 1) gen) := by
  let env := st.vars ++ st.stobjs
  have hr : readExpr (coreWorld world coreTuple) (coreKind cns coreTuple)
      (form "IF" [.sym "RETIRE",.sym "ROW-GENERATION",form "+" [.int 1,.sym "ROW-GENERATION"]]) =
      .ok (.app "IF" [.var "RETIRE",.var "ROW-GENERATION",.app "BINARY-+" [.quote (.int 1),.var "ROW-GENERATION"]]) := by
    with_unfolding_all rfl
  have er : Term.eval (coreWorld world coreTuple).fns env (.var "RETIRE") = .ok retire := by
    simp only [env, Term.eval, var_env_bound st _ _ hrv]
  have eg : Term.eval (coreWorld world coreTuple).fns env (.var "ROW-GENERATION") = .ok gen := by
    simp only [env, Term.eval, var_env_bound st _ _ hgv]
  have ep : Term.eval (coreWorld world coreTuple).fns env (.app "BINARY-+" [.quote (.int 1),.var "ROW-GENERATION"]) =
      .ok (Prim.plus (.int 1) gen) := by
    rw [Term.eval.eq_5 _ _ "BINARY-+" _ (by simp) (by simp)]
    simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil,
      List.mapM_cons, List.mapM_nil, eg, Term.eval.eq_2, except_ok_bind]
    rfl
  simp only [ev, hr, except_ok_bind]
  change Term.eval (coreWorld world coreTuple).fns env _ = _
  rw [Term.eval.eq_3, er]
  simp only [except_ok_bind]
  cases hh : retire.truthy <;> simp only [hh, Bool.false_eq_true, ↓reduceIte, eg, ep]

theorem eval_cleanup_next (st : St) (retire : Val) (hv : var st "RETIRE" = .ok retire) :
    (do let term ← readNext (coreWorld world coreTuple) (coreKind cns coreTuple) cleanupNext
        term.eval (coreWorld world coreTuple).fns (st.vars ++ st.stobjs)) =
      .ok (if retire.truthy then .int 11 else .int 0) := by
  have hr : readNext (coreWorld world coreTuple) (coreKind cns coreTuple) cleanupNext =
      .ok (.app "IF" [.var "RETIRE",.quote (.int 11),.quote (.int 0)]) := by with_unfolding_all rfl
  simp only [hr, except_ok_bind, Term.eval.eq_3, Term.eval.eq_1, var_env_bound st _ _ hv]
  cases hh : retire.truthy <;> simp only [hh, Bool.false_eq_true, ↓reduceIte, except_ok_bind, Term.eval.eq_2]

def cleanupPhase (retire : Val) : Val := if retire.truthy then .int 11 else .int 0
def cleanupGeneration (retire gen : Val) : Val := if retire.truthy then gen else Prim.plus (.int 1) gen

theorem flush_cleanup (id slot budget own dir control retire gen next : Val) (st : St)
    (hp : st.pending = cleanupPending) (hn : st.next = some cleanupNext)
    (hi : var st "ID" = .ok id) (hs : var st "SLOT" = .ok slot)
    (ho : stobj st "FN2-CNS" = .ok own) (hd : stobj st "FN2-MACHINES" = .ok dir)
    (hc : stobj st "FN2-CONTROL" = .ok control)
    (hr : var st "RETIRE" = .ok retire) (hg : var st "ROW-GENERATION" = .ok gen)
    (hnext : var st "NEXT" = .ok next)
    (hb : natLt slot («FN2-CNS-ROWS» own) = true)
    (hdb : natLt id («FN2-MACHINES-ROWS» dir) = true) :
    flush (coreWorld world coreTuple) (drainFrame id slot budget) st =
    if cleanupFits (cleanupGeneration retire gen) next then
      .ok { (setStobj
        (setStobj st "FN2-CNS" (cleanupOwn slot (cleanupPhase retire) (cleanupGeneration retire gen) next own))
        "FN2-MACHINES" («FN2-MACHINES-SET-WAIT-REASON» id (.int 0) dir))
        with pending := [], next := none, nextDone := true }
    else .ok { (setStobj st "FN2-CONTROL" («FN2-CONTROL-RECORD-STOP» (.int 13) control))
        with pending := [], next := none, nextDone := true } := by
  have eg := ev_cleanup_generation st retire gen hr hg
  have en : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (.sym "*FN2-NONE*") = .ok (.int 4294967295) :=
    ev_quote_of_read st _ _ (by with_unfolding_all rfl)
  have ew : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (.sym "*FN2-WAIT-NONE*") = .ok (.int 0) :=
    ev_quote_of_read st _ _ (by with_unfolding_all rfl)
  have ez : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.int 0) = .ok (.int 0) :=
    ev_quote_of_read st _ _ (by rfl)
  have ex : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st (.sym "NEXT") = .ok next :=
    ev_var_expression st _ _ _ (by with_unfolding_all rfl) hnext
  have hread : readNext (coreWorld world coreTuple) (coreKind cns coreTuple) cleanupNext =
      .ok (.app "IF" [.var "RETIRE",.quote (.int 11),.quote (.int 0)]) := by with_unfolding_all rfl
  have ep : Term.eval (coreWorld world coreTuple).fns (st.vars ++ st.stobjs)
      (.app "IF" [.var "RETIRE",.quote (.int 11),.quote (.int 0)]) = .ok (cleanupPhase retire) := by
    simpa only [hread, except_ok_bind] using eval_cleanup_next st retire hr
  have hf : ColType.fits (.enum 12) (cleanupPhase retire) = true := by
    cases hh : retire.truthy <;> simp [cleanupPhase, hh, ColType.fits]
  have hk : (drainFrame id slot budget).kind = coreKind cns coreTuple := by rfl
  simp only [flush, hp, hn, hk, cleanupPending, List.mapM_cons, List.mapM_nil,
    eg, en, ew, ez, ex, hread, ep, except_ok_bind]
  change (do
    let st' ← put (coreWorld world coreTuple) (drainFrame id slot budget) st
      (cleanupPairs (cleanupPhase retire) (cleanupGeneration retire gen) next)
    pure { st' with pending := [], next := none, nextDone := st.nextDone || true }) = _
  rw [cleanup_put id slot budget own dir control (cleanupPhase retire) (cleanupGeneration retire gen) next st hi hs ho hd hc hb hdb hf]
  split <;> simp only [except_ok_bind, Bool.or_true] <;> rfl

theorem find_release : findOp (coreWorld world coreTuple) "FN2-CNS-LEASE-RELEASE" = .ok releaseOp := by rfl
theorem find_reclaim : findOp (coreWorld world coreTuple) "FN2-CNS-RECLAIM" = .ok reclaimOp := by rfl

theorem bind_release (st : St) (r : Val) (hs : r = Val.ofList [r.car,r.cdr.car,r.cdr.cdr.car]) :
    bindOuts st releaseOp.stobjsOut ["LC"] r =
      .ok { (setStobj (setStobj st "FN2-POOL" r.cdr.car) "FN2-CONTROL" r.cdr.cdr.car)
        with vars := ("LC",r.car) :: st.vars } := by
  calc
    _ = bindOuts st releaseOp.stobjsOut ["LC"] (Val.ofList [r.car,r.cdr.car,r.cdr.cdr.car]) :=
      congrArg (bindOuts st releaseOp.stobjsOut ["LC"]) hs
    _ = _ := by rfl

theorem bind_reclaim (st : St) (r : Val) (hs : r = Val.ofList [r.car,r.cdr.car]) :
    bindOuts st reclaimOp.stobjsOut [] r =
      .ok (setStobj (setStobj st "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car) := by
  calc
    _ = bindOuts st reclaimOp.stobjsOut [] (Val.ofList [r.car,r.cdr.car]) :=
      congrArg (bindOuts st reclaimOp.stobjsOut []) hs
    _ = _ := by rfl

theorem accepted_code (code : Val) :
    codeIn code [.sym ":OK",.sym ":RETIRED"] =
      (Native.memberEqual code (Val.ofList [.sym ":OK",.sym ":RETIRED"])).truthy := by
  by_cases ho : code = .sym ":OK" <;> by_cases hr : code = .sym ":RETIRED" <;>
    simp [codeIn, Native.memberEqual, Val.ofList, ho, hr, Val.truthy, Val.nil]

theorem run_draining_cases (fuel : Nat) (id slot budget : Val) (kids : Fin 57 → Val) :
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel + 1)
      (drainState id slot budget kids) drainingSteps =
    if (Prim.equal («FN2-CNS-LEASE» slot (kids ⟨17,by decide⟩)) (.int 1)).truthy then
      run (coreWorld world coreTuple) (drainFrame id slot budget) fuel (drainState id slot budget kids) leaseSteps
    else run (coreWorld world coreTuple) (drainFrame id slot budget) fuel (drainState id slot budget kids) cleanupSteps := by
  let st := drainState id slot budget kids
  have el : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st
      (form "EQUAL" [.sym "ROW-LEASE",.sym "*FN2-CNS-LEASE-HELD*"]) =
      .ok (Prim.equal («FN2-CNS-LEASE» slot (kids ⟨17,by decide⟩)) (.int 1)) :=
    ev_lease_test st _ (by rfl)
  have et : ev (coreWorld world coreTuple) (coreKind cns coreTuple) st Val.t = .ok Val.t :=
    ev_quote_of_read st _ _ (by rfl)
  have hk : (drainFrame id slot budget).kind = coreKind cns coreTuple := by rfl
  change run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel + 1) st drainingSteps = _
  by_cases hh : (Prim.equal («FN2-CNS-LEASE» slot (kids ⟨17,by decide⟩)) (.int 1)).truthy = true
  · simp only [run, drainingSteps, hk, List.findM?, el, et, except_ok_bind, hh]
    rfl
  · simp only [run, drainingSteps, hk, List.findM?, el, et, except_ok_bind, hh]
    rfl

theorem charge_cleanup (fuel : Nat) (id slot budget : Val) (st : St)
    (hp : st.pending = []) (hn : st.next = none) :
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+1) st
      [.charge none (some (.sym "*FN2-WORK-RELEASE*")) none none] =
    chargeResult (drainFrame id slot budget) st (.int 0) (.int 20) (.int 0) Val.nil := by
  have he := ev_quote_of_read st (.sym "*FN2-WORK-RELEASE*") (.int 20) (by with_unfolding_all rfl)
  have hk : (drainFrame id slot budget).kind = coreKind cns coreTuple := by rfl
  simp only [run, flush_empty _ _ st hp hn, except_ok_bind, evOpt, hk, he]

theorem charge_lease (fuel : Nat) (id slot budget : Val) (st sf : St)
    (hf : flush (coreWorld world coreTuple) (drainFrame id slot budget) st = .ok sf) :
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+1) st
      [.charge none (some (.sym "*FN2-WORK-TRANSITION*")) none (some Val.t)] =
    chargeResult (drainFrame id slot budget) sf (.int 0) (.int 24) (.int 0) Val.t := by
  have he := ev_quote_of_read sf (.sym "*FN2-WORK-TRANSITION*") (.int 24) (by with_unfolding_all rfl)
  have ht := ev_quote_of_read sf Val.t Val.t (by rfl)
  have hk : (drainFrame id slot budget).kind = coreKind cns coreTuple := by rfl
  simp only [run, hf, except_ok_bind, evOpt, hk, he, ht]

theorem stop_phase (fuel : Nat) (id slot budget control : Val) (st : St)
    (hp : st.pending = []) (hn : st.next = none)
    (hc : stobj st "FN2-CONTROL" = .ok control) :
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+1) st
      [.stop "MACHINE-PHASE" none] =
    chargeResult (drainFrame id slot budget)
      (setStobj st "FN2-CONTROL" («FN2-CONTROL-RECORD-STOP» (.int 15) control))
      (.int 0) (.int 1) (.int 0) Val.nil := by
  exact run_stop_global (coreWorld world coreTuple) (drainFrame id slot budget) st fuel
    "MACHINE-PHASE" control (.int 15) (.int 1) («FN2-CONTROL-RECORD-STOP» (.int 15) control)
    hp hn hc (by rfl) (by rfl) (by rfl) (by rfl)
    («FN2-CONTROL-RECORD-STOP».core_call _ _)


def cleanupState (id slot budget retire next : Val) (kids : Fin 57 → Val) : St :=
  { (drainState id slot budget kids) with
    vars := ("RETIRE",retire) :: ("NEXT",next) :: (drainState id slot budget kids).vars,
    pending := cleanupPending, next := some cleanupNext }

def cleanupRetire (slot : Val) (kids : Fin 57 → Val) : Val :=
  «NOT» (Prim.lt («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))
    («FN2-MACHINES-GEN-LIMIT» (kids ⟨3,by decide⟩)))
def cleanupHead (kids : Fin 57 → Val) : Val :=
  «FN2-MACHINES-FREE-HEAD-OF» (.int 6) (kids ⟨3,by decide⟩)

theorem cleanup_prefix (fuel : Nat) (id slot budget : Val) (kids : Fin 57 → Val) :
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+6)
      (drainState id slot budget kids) cleanupSteps =
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+2)
      (cleanupState id slot budget (cleanupRetire slot kids) (cleanupHead kids) kids)
      [.do_ [] reclaimCall false [] none [] [],
       .charge none (some (.sym "*FN2-WORK-RELEASE*")) none none] := by
  let st := drainState id slot budget kids
  have en := ev_free_head st (kids ⟨3,by decide⟩) (by rfl) (by rfl)
  let st1 : St := { st with vars := ("NEXT",cleanupHead kids) :: st.vars }
  have er := ev_retire st1 («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))
    (kids ⟨3,by decide⟩) (by rfl) (by rfl)
  have hk : (drainFrame id slot budget).kind = coreKind cns coreTuple := by rfl
  change run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+6) st cleanupSteps = _
  unfold cleanupSteps
  rw [run]
  simp only [hk, en, except_ok_bind]
  change run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+5) st1 _ = _
  rw [run]
  simp only [hk, er, except_ok_bind]
  rfl

def cleanupAfter (id slot budget : Val) (kids : Fin 57 → Val) : St :=
  let retire := cleanupRetire slot kids
  let gen := cleanupGeneration retire («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))
  let next := cleanupHead kids
  let st := cleanupState id slot budget retire next kids
  if cleanupFits gen next then
    { (setStobj (setStobj st "FN2-CNS" (cleanupOwn slot (cleanupPhase retire) gen next (kids ⟨17,by decide⟩)))
      "FN2-MACHINES" («FN2-MACHINES-SET-WAIT-REASON» id (.int 0) (kids ⟨3,by decide⟩)))
      with pending := [], next := none, nextDone := true }
  else { (setStobj st "FN2-CONTROL" («FN2-CONTROL-RECORD-STOP» (.int 13) (kids ⟨5,by decide⟩)))
      with pending := [], next := none, nextDone := true }

theorem cleanup_flush_state (id slot budget : Val) (kids : Fin 57 → Val)
    (hb : natLt slot («FN2-CNS-ROWS» (kids ⟨17,by decide⟩)) = true)
    (hd : natLt id («FN2-MACHINES-ROWS» (kids ⟨3,by decide⟩)) = true) :
    flush (coreWorld world coreTuple) (drainFrame id slot budget)
      (cleanupState id slot budget (cleanupRetire slot kids) (cleanupHead kids) kids) =
      .ok (cleanupAfter id slot budget kids) := by
  rw [flush_cleanup id slot budget (kids ⟨17,by decide⟩) (kids ⟨3,by decide⟩)
    (kids ⟨5,by decide⟩) (cleanupRetire slot kids)
    («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩)) (cleanupHead kids)
    _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) hb hd]
  by_cases hf : cleanupFits (cleanupGeneration (cleanupRetire slot kids)
    («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))) (cleanupHead kids) = true <;>
    simp only [cleanupAfter, hf, Bool.false_eq_true, ↓reduceIte]

theorem run_reclaim (fuel : Nat) (id slot budget retire dir control : Val) (st : St)
    (hp : st.pending = []) (hn : st.next = none)
    (hi : var st "ID" = .ok id) (hr : var st "RETIRE" = .ok retire)
    (hord : var st "ORDINAL" = .ok (.int 6))
    (hd : stobj st "FN2-MACHINES" = .ok dir) (hc : stobj st "FN2-CONTROL" = .ok control) :
    let r := «FN2-MACHINES-RECLAIM» id (.int 6) retire dir control
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+2) st
      [.do_ [] reclaimCall false [] none [] [],
       .charge none (some (.sym "*FN2-WORK-RELEASE*")) none none] =
    chargeResult (drainFrame id slot budget)
      (setStobj (setStobj st "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car)
      (.int 0) (.int 20) (.int 0) Val.nil := by
  dsimp only
  have hcall := reclaim_call id retire dir control st hi hr hord hd hc
  rw [run]
  simp only [flush_empty _ _ st hp hn, except_ok_bind, reclaimCall, find_reclaim]
  change (do
    let (_,r) ← callOp (coreWorld world coreTuple) (coreKind cns coreTuple) st reclaimCall
    let st' ← bindOuts st reclaimOp.stobjsOut [] r
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+1) st'
      [.charge none (some (.sym "*FN2-WORK-RELEASE*")) none none]) = _
  rw [hcall]
  simp only [except_ok_bind, bind_reclaim _ _ (reclaim_result_shape _ _ _ _ _)]
  exact charge_cleanup fuel id slot budget _ hp hn

def cleanupKids (id slot : Val) (kids : Fin 57 → Val) : Fin 57 → Val :=
  let retire := cleanupRetire slot kids
  let gen := cleanupGeneration retire («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))
  let next := cleanupHead kids
  if cleanupFits gen next then
    patchKids kids (kids ⟨0,by decide⟩) («FN2-MACHINES-SET-WAIT-REASON» id (.int 0) (kids ⟨3,by decide⟩))
      (kids ⟨5,by decide⟩) (cleanupOwn slot (cleanupPhase retire) gen next (kids ⟨17,by decide⟩))
  else patchKids kids (kids ⟨0,by decide⟩) (kids ⟨3,by decide⟩)
    («FN2-CONTROL-RECORD-STOP» (.int 13) (kids ⟨5,by decide⟩)) (kids ⟨17,by decide⟩)

def reclaimedKids (id retire : Val) (kids : Fin 57 → Val) : Fin 57 → Val :=
  let r := «FN2-MACHINES-RECLAIM» id (.int 6) retire (kids ⟨3,by decide⟩) (kids ⟨5,by decide⟩)
  patchKids kids (kids ⟨0,by decide⟩) r.car r.cdr.car (kids ⟨17,by decide⟩)

def armResult (steps retry : Val) (kids : Fin 57 → Val) : Val :=
  Val.ofList ([.int 0,steps,.int 0,retry] ++ [(kids ⟨0, by decide⟩), (kids ⟨1, by decide⟩), (kids ⟨2, by decide⟩), (kids ⟨3, by decide⟩), (kids ⟨4, by decide⟩), (kids ⟨5, by decide⟩), (kids ⟨6, by decide⟩), (kids ⟨7, by decide⟩), (kids ⟨8, by decide⟩), (kids ⟨9, by decide⟩), (kids ⟨10, by decide⟩), (kids ⟨11, by decide⟩), (kids ⟨12, by decide⟩), (kids ⟨13, by decide⟩), (kids ⟨14, by decide⟩), (kids ⟨15, by decide⟩), (kids ⟨16, by decide⟩), (kids ⟨17, by decide⟩), (kids ⟨18, by decide⟩), (kids ⟨19, by decide⟩), (kids ⟨20, by decide⟩), (kids ⟨21, by decide⟩), (kids ⟨22, by decide⟩), (kids ⟨23, by decide⟩), (kids ⟨24, by decide⟩), (kids ⟨25, by decide⟩), (kids ⟨26, by decide⟩), (kids ⟨27, by decide⟩), (kids ⟨28, by decide⟩), (kids ⟨29, by decide⟩), (kids ⟨30, by decide⟩), (kids ⟨31, by decide⟩), (kids ⟨32, by decide⟩), (kids ⟨33, by decide⟩), (kids ⟨34, by decide⟩), (kids ⟨35, by decide⟩), (kids ⟨36, by decide⟩), (kids ⟨37, by decide⟩), (kids ⟨38, by decide⟩), (kids ⟨39, by decide⟩), (kids ⟨40, by decide⟩), (kids ⟨41, by decide⟩), (kids ⟨42, by decide⟩), (kids ⟨43, by decide⟩), (kids ⟨44, by decide⟩), (kids ⟨45, by decide⟩), (kids ⟨46, by decide⟩), (kids ⟨47, by decide⟩), (kids ⟨48, by decide⟩), (kids ⟨49, by decide⟩), (kids ⟨50, by decide⟩), (kids ⟨51, by decide⟩), (kids ⟨52, by decide⟩), (kids ⟨53, by decide⟩), (kids ⟨54, by decide⟩), (kids ⟨55, by decide⟩), (kids ⟨56, by decide⟩)])

theorem cleanup_run (fuel : Nat) (id slot budget : Val) (kids : Fin 57 → Val)
    (hb : natLt slot («FN2-CNS-ROWS» (kids ⟨17,by decide⟩)) = true)
    (hd : natLt id («FN2-MACHINES-ROWS» (kids ⟨3,by decide⟩)) = true) :
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+6)
      (drainState id slot budget kids) cleanupSteps =
    .ok (.done (armResult (.int 20) Val.nil
      (reclaimedKids id (cleanupRetire slot kids) (cleanupKids id slot kids)))) := by
  rw [cleanup_prefix, run]
  simp only [cleanup_flush_state id slot budget kids hb hd, except_ok_bind, reclaimCall, find_reclaim]
  change (do
    let (_,r) ← callOp (coreWorld world coreTuple) (coreKind cns coreTuple)
      (cleanupAfter id slot budget kids) reclaimCall
    let st' ← bindOuts (cleanupAfter id slot budget kids) reclaimOp.stobjsOut [] r
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+1) st'
      [.charge none (some (.sym "*FN2-WORK-RELEASE*")) none none]) = _
  by_cases hf : cleanupFits (cleanupGeneration (cleanupRetire slot kids)
    («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))) (cleanupHead kids) = true <;>
    simp only [cleanupAfter, cleanupKids, hf, ↓reduceIte] <;> rw [reclaim_call _ _ _ _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)] <;>
    simp only [except_ok_bind, bind_reclaim _ _ (reclaim_result_shape _ _ _ _ _)] <;>
    rw [charge_cleanup fuel id slot budget _ (by rfl) (by rfl)] <;> rfl

def releaseRaw (id slot : Val) (kids : Fin 57 → Val) : Val :=
  «FN2-CORE-RELEASE-CHILDREN» («FN2-CNS-LSLOT» slot (kids ⟨17,by decide⟩))
    («FN2-CNS-LGEN» slot (kids ⟨17,by decide⟩)) (.int 11) id
    («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩)) (kids ⟨0,by decide⟩) (kids ⟨5,by decide⟩)

def releaseState (id slot budget : Val) (kids : Fin 57 → Val) : St :=
  let st := drainState id slot budget kids
  let r := releaseRaw id slot kids
  { (setStobj (setStobj st "FN2-POOL" r.cdr.car) "FN2-CONTROL" r.cdr.cdr.car)
    with vars := ("LC",r.car) :: st.vars }

def leaseKids (id slot : Val) (kids : Fin 57 → Val) : Fin 57 → Val :=
  let r := releaseRaw id slot kids
  if codeIn r.car [.sym ":OK",.sym ":RETIRED"] then
    patchKids kids r.cdr.car (kids ⟨3,by decide⟩) r.cdr.cdr.car (leaseOwn slot (kids ⟨17,by decide⟩))
  else patchKids kids r.cdr.car (kids ⟨3,by decide⟩)
    («FN2-CONTROL-RECORD-STOP» (.int 15) r.cdr.cdr.car) (kids ⟨17,by decide⟩)

theorem lease_prefix (fuel : Nat) (id slot budget : Val) (kids : Fin 57 → Val) :
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+3)
      (drainState id slot budget kids) leaseSteps =
    if codeIn (releaseRaw id slot kids).car [.sym ":OK",.sym ":RETIRED"] then
      run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+2)
        (releaseState id slot budget kids)
        [.set leasePending,.charge none (some (.sym "*FN2-WORK-TRANSITION*")) none (some Val.t)]
    else run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+2)
        (releaseState id slot budget kids) [.stop "MACHINE-PHASE" none] := by
  let st := drainState id slot budget kids
  have hc := release_call («FN2-CNS-LSLOT» slot (kids ⟨17,by decide⟩))
    («FN2-CNS-LGEN» slot (kids ⟨17,by decide⟩)) id («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))
    (kids ⟨0,by decide⟩) (kids ⟨5,by decide⟩) st
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  change run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+3) st leaseSteps = _
  unfold leaseSteps
  rw [run_do_accept_stop (coreWorld world coreTuple) (drainFrame id slot budget) st
    (releaseState id slot budget kids) (fuel+2) "LC" "MACHINE-PHASE" releaseCall
    [.sym ":OK",.sym ":RETIRED"] _ releaseOp (releaseRaw id slot kids) (releaseRaw id slot kids).car
    (by rfl) (by rfl) find_release hc
    (bind_release _ _ (release_result_shape _ _ _ _ _ _ _)) (by rfl) (by rfl) (by rfl)]


theorem lease_run (fuel : Nat) (id slot budget : Val) (kids : Fin 57 → Val)
    (hb : natLt slot («FN2-CNS-ROWS» (kids ⟨17,by decide⟩)) = true) :
    run (coreWorld world coreTuple) (drainFrame id slot budget) (fuel+3)
      (drainState id slot budget kids) leaseSteps =
    .ok (.done (armResult
      (if codeIn (releaseRaw id slot kids).car [.sym ":OK",.sym ":RETIRED"] then .int 24 else .int 1)
      (if codeIn (releaseRaw id slot kids).car [.sym ":OK",.sym ":RETIRED"] then Val.t else Val.nil)
      (leaseKids id slot kids))) := by
  rw [lease_prefix]
  unfold leaseKids
  by_cases ha : codeIn (releaseRaw id slot kids).car [.sym ":OK",.sym ":RETIRED"] = true
  · simp only [ha, ↓reduceIte]
    rw [run]
    have hp : pend (releaseState id slot budget kids) leasePending =
        .ok { (releaseState id slot budget kids) with pending := leasePending } := by rfl
    rw [hp]
    simp only [except_ok_bind]
    rw [charge_lease fuel id slot budget _ _
      (flush_lease id slot budget (kids ⟨17,by decide⟩) (kids ⟨3,by decide⟩)
        (releaseRaw id slot kids).cdr.cdr.car _
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hb)]
    rfl
  · simp only [ha, ↓reduceIte]
    rw [stop_phase (fuel+1) id slot budget (releaseRaw id slot kids).cdr.cdr.car _ (by rfl) (by rfl) (by rfl)]
    rfl

def drainingLease (slot : Val) (kids : Fin 57 → Val) : Bool :=
  (Prim.equal («FN2-CNS-LEASE» slot (kids ⟨17,by decide⟩)) (.int 1)).truthy

def drainingCharge (id slot : Val) (kids : Fin 57 → Val) : Val :=
  if drainingLease slot kids then
    if codeIn (releaseRaw id slot kids).car [.sym ":OK",.sym ":RETIRED"] then .int 24 else .int 1
  else .int 20

def drainingRetry (id slot : Val) (kids : Fin 57 → Val) : Val :=
  if drainingLease slot kids then
    if codeIn (releaseRaw id slot kids).car [.sym ":OK",.sym ":RETIRED"] then Val.t else Val.nil
  else Val.nil

def drainingKids (id slot : Val) (kids : Fin 57 → Val) : Fin 57 → Val :=
  if drainingLease slot kids then leaseKids id slot kids
  else reclaimedKids id (cleanupRetire slot kids) (cleanupKids id slot kids)

theorem draining_run (id slot budget : Val) (kids : Fin 57 → Val)
    (hb : natLt slot («FN2-CNS-ROWS» (kids ⟨17,by decide⟩)) = true)
    (hd : natLt id («FN2-MACHINES-ROWS» (kids ⟨3,by decide⟩)) = true) :
    runArm (coreWorld world coreTuple) (coreKind cns coreTuple) draining false
      ([id,slot,.int 11,.int 6,budget] ++ [(kids ⟨0, by decide⟩), (kids ⟨1, by decide⟩), (kids ⟨2, by decide⟩), (kids ⟨3, by decide⟩), (kids ⟨4, by decide⟩), (kids ⟨5, by decide⟩), (kids ⟨6, by decide⟩), (kids ⟨7, by decide⟩), (kids ⟨8, by decide⟩), (kids ⟨9, by decide⟩), (kids ⟨10, by decide⟩), (kids ⟨11, by decide⟩), (kids ⟨12, by decide⟩), (kids ⟨13, by decide⟩), (kids ⟨14, by decide⟩), (kids ⟨15, by decide⟩), (kids ⟨16, by decide⟩), (kids ⟨17, by decide⟩), (kids ⟨18, by decide⟩), (kids ⟨19, by decide⟩), (kids ⟨20, by decide⟩), (kids ⟨21, by decide⟩), (kids ⟨22, by decide⟩), (kids ⟨23, by decide⟩), (kids ⟨24, by decide⟩), (kids ⟨25, by decide⟩), (kids ⟨26, by decide⟩), (kids ⟨27, by decide⟩), (kids ⟨28, by decide⟩), (kids ⟨29, by decide⟩), (kids ⟨30, by decide⟩), (kids ⟨31, by decide⟩), (kids ⟨32, by decide⟩), (kids ⟨33, by decide⟩), (kids ⟨34, by decide⟩), (kids ⟨35, by decide⟩), (kids ⟨36, by decide⟩), (kids ⟨37, by decide⟩), (kids ⟨38, by decide⟩), (kids ⟨39, by decide⟩), (kids ⟨40, by decide⟩), (kids ⟨41, by decide⟩), (kids ⟨42, by decide⟩), (kids ⟨43, by decide⟩), (kids ⟨44, by decide⟩), (kids ⟨45, by decide⟩), (kids ⟨46, by decide⟩), (kids ⟨47, by decide⟩), (kids ⟨48, by decide⟩), (kids ⟨49, by decide⟩), (kids ⟨50, by decide⟩), (kids ⟨51, by decide⟩), (kids ⟨52, by decide⟩), (kids ⟨53, by decide⟩), (kids ⟨54, by decide⟩), (kids ⟨55, by decide⟩), (kids ⟨56, by decide⟩)]) 7 =
    .ok (armResult (drainingCharge id slot kids) (drainingRetry id slot kids)
      (drainingKids id slot kids)) := by
  rw [drain_entry, run_draining_cases 6]
  by_cases hl : (Prim.equal («FN2-CNS-LEASE» slot (kids ⟨17,by decide⟩)) (.int 1)).truthy = true
  · simp only [drainingLease, hl, ↓reduceIte, lease_run 3 id slot budget kids hb,
      except_ok_bind, drainingCharge, drainingRetry, drainingKids, drainingLease, hl, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [drainingLease, hl, ↓reduceIte, cleanup_run 0 id slot budget kids hb hd,
      except_ok_bind, drainingCharge, drainingRetry, drainingKids, drainingLease, hl, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem draining_emitted (id budget : Val) (kids : Fin 57 → Val)
    (h : «FN2-CNS-SNAPSHOT-READ-CODE» id (coreImage kids) = .sym ":OK") :
    let slot := «FN2-MACHINE-SLOT» id (coreImage kids)
    «FN2-CNS-RUN-DRAINING» id budget (coreImage kids) =
      Val.ofList [.int 0,drainingCharge id slot kids,.int 0,drainingRetry id slot kids,
        coreImage (drainingKids id slot kids)] := by
  dsimp only
  let slot := «FN2-MACHINE-SLOT» id (coreImage kids)
  change «FN2-CNS-RUN-DRAINING» id budget (coreImage kids) =
    Val.ofList [.int 0,drainingCharge id slot kids,.int 0,drainingRetry id slot kids,
      coreImage (drainingKids id slot kids)]
  have hr1 : «FN2-CNS-ROW-GENERATION» id (coreImage kids) = «FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩) := by
    simp only [«FN2-CNS-ROW-GENERATION», h, «EQ», Prim.equal, beq_self_eq_true,
      Val.ofBool, Val.t, Val.truthy, ↓reduceIte]
    rfl
  have hr2 : «FN2-CNS-ROW-LGEN» id (coreImage kids) = «FN2-CNS-LGEN» slot (kids ⟨17,by decide⟩) := by
    simp only [«FN2-CNS-ROW-LGEN», h, «EQ», Prim.equal, beq_self_eq_true,
      Val.ofBool, Val.t, Val.truthy, ↓reduceIte]
    rfl
  have hr3 : «FN2-CNS-ROW-LSLOT» id (coreImage kids) = «FN2-CNS-LSLOT» slot (kids ⟨17,by decide⟩) := by
    simp only [«FN2-CNS-ROW-LSLOT», h, «EQ», Prim.equal, beq_self_eq_true,
      Val.ofBool, Val.t, Val.truthy, ↓reduceIte]
    rfl
  have hr4 : «FN2-CNS-ROW-LEASE» id (coreImage kids) = «FN2-CNS-LEASE» slot (kids ⟨17,by decide⟩) := by
    simp only [«FN2-CNS-ROW-LEASE», h, «EQ», Prim.equal, beq_self_eq_true,
      Val.ofBool, Val.t, Val.truthy, ↓reduceIte]
    rfl
  have htest : («EQ» («FN2-CNS-SNAPSHOT-READ-CODE» id (coreImage kids)) (.sym ":OK")).truthy = true := by rw [h]; rfl
  unfold «FN2-CNS-RUN-DRAINING»
  simp only [htest, ↓reduceIte, hr1, hr2, hr3, hr4]
  by_cases hl : (Prim.equal («FN2-CNS-LEASE» slot (kids ⟨17,by decide⟩)) (.int 1)).truthy = true
  · simp only [drainingCharge, drainingRetry, drainingKids, drainingLease, hl, Bool.false_eq_true, ↓reduceIte]
    rw [release_adapter]
    change (if (Native.memberEqual (releaseRaw id slot kids).car (Val.ofList [.sym ":OK",.sym ":RETIRED"])).truthy then
      Val.ofList [.int 0,.int 24,.int 0,Val.t,
        «FN2-CNS-WRITE+LSLOT+LGEN+LEASE» id (.int 4294967295) (.int 0) (.int 0)
          (coreImage (patchKids kids (releaseRaw id slot kids).cdr.car (kids ⟨3,by decide⟩)
            (releaseRaw id slot kids).cdr.cdr.car (kids ⟨17,by decide⟩)))]
      else Val.ofList [.int 0,.int 1,.int 0,Val.nil,
        «FN2-CORE-STOP» (.int 15) (coreImage (patchKids kids (releaseRaw id slot kids).cdr.car
          (kids ⟨3,by decide⟩) (releaseRaw id slot kids).cdr.cdr.car (kids ⟨17,by decide⟩)))]) = _
    rw [← accepted_code]
    by_cases ha : codeIn (releaseRaw id slot kids).car [.sym ":OK",.sym ":RETIRED"] = true
    · simp only [leaseKids, ha, Bool.false_eq_true, ↓reduceIte]
      rw [lease_write _ _ ((snapshot_pool_control_frame _ _ _ _).trans h)]
      rfl
    · simp only [leaseKids, ha, Bool.false_eq_true, ↓reduceIte]
      rfl
  · simp only [drainingCharge, drainingRetry, drainingKids, drainingLease, hl, Bool.false_eq_true, ↓reduceIte]
    have hn : «FN2-MACHINE-FREE-HEAD» (.int 6) (coreImage kids) = cleanupHead kids := by rfl
    have hg : «NOT» (Prim.lt («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))
      («FN2-MACHINE-GEN-LIMIT» (coreImage kids))) = cleanupRetire slot kids := by rfl
    rw [hn, hg]
    have hw := cleanup_write id (cleanupGeneration (cleanupRetire slot kids)
      («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))) (cleanupHead kids)
      (cleanupRetire slot kids) (coreImage kids) h (by rfl)
    dsimp only [cleanupGeneration] at hw
    rw [hw]
    unfold cleanupKids
    by_cases hf : cleanupFits (cleanupGeneration (cleanupRetire slot kids)
      («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩))) (cleanupHead kids) = true
    · dsimp only [cleanupGeneration] at hf
      simp only [cleanupGeneration, hf, Bool.false_eq_true, ↓reduceIte]
      change Val.ofList [.int 0,.int 20,.int 0,Val.nil,
        «FN2-CNS-RECLAIM» id (.int 6) (cleanupRetire slot kids)
          (coreImage (patchKids kids (kids ⟨0,by decide⟩)
            («FN2-MACHINES-SET-WAIT-REASON» id (.int 0) (kids ⟨3,by decide⟩)) (kids ⟨5,by decide⟩)
            (cleanupOwn slot (cleanupPhase (cleanupRetire slot kids))
              (cleanupGeneration (cleanupRetire slot kids) («FN2-CNS-GENERATION» slot (kids ⟨17,by decide⟩)))
              (cleanupHead kids) (kids ⟨17,by decide⟩))))] = _
      rw [reclaim_adapter]
      rfl
    · dsimp only [cleanupGeneration] at hf
      simp only [cleanupGeneration, hf, Bool.false_eq_true, ↓reduceIte]
      change Val.ofList [.int 0,.int 20,.int 0,Val.nil,
        «FN2-CNS-RECLAIM» id (.int 6) (cleanupRetire slot kids)
          (coreImage (patchKids kids (kids ⟨0,by decide⟩) (kids ⟨3,by decide⟩)
            («FN2-CONTROL-RECORD-STOP» (.int 13) (kids ⟨5,by decide⟩)) (kids ⟨17,by decide⟩)))] = _
      rw [reclaim_adapter]
      rfl

theorem cns_draining_certificate (id budget : Val) (kids : Fin 57 → Val) :
    ∃ fuel result,
      runCore world coreTuple cns draining false [id,budget,coreImage kids] fuel = .ok result ∧
      result = «FN2-CNS-RUN-DRAINING» id budget (coreImage kids) := by
  apply Wrapper.certificate world coreTuple cns draining false
    [id,budget,coreImage kids] («FN2-CNS-RUN-DRAINING» id budget (coreImage kids))
    («FN2-CNS-SNAPSHOT-READ-CODE» id (coreImage kids)) (by rfl) (by rfl)
  · exact Fn2.Instances.CoreWorld.«FN2-CNS-SNAPSHOT-READ-CODE».dispatched
      (err := "no function FN2-CNS-SNAPSHOT-READ-CODE/2") _ _
  · intro h
    let slot := «FN2-MACHINE-SLOT» id (coreImage kids)
    obtain ⟨hi, hr, hs, hb⟩ := snapshot_bounds id (coreImage kids) h
    have hid : («FN2-MACHINE-IDP» id (coreImage kids)).truthy = true := by
      simp [«FN2-MACHINE-IDP», hi, hr]
    have hslot : slot = «FN2-MACHINES-SLOT» id (kids ⟨3,by decide⟩) := by
      simp [slot, «FN2-MACHINE-SLOT», «FN2-MACHINE-SLOT-READ-CODE», hid, «EQ», Prim.equal]
      rfl
    have hown : natLt slot («FN2-CNS-ROWS» (kids ⟨17,by decide⟩)) = true := by
      rw [← natp_lt, hslot]
      change ((«NATP» («FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» (coreImage kids)))).truthy &&
        (Prim.lt («FN2-MACHINES-SLOT» id («FN2-CORE-MACHINES» (coreImage kids)))
          («FN2-CNS-ROWS» («FN2-CNS-TABLE» (coreImage kids)))).truthy) = true
      rw [hs,hb]
      rfl
    have hdir : natLt id («FN2-MACHINES-ROWS» (kids ⟨3,by decide⟩)) = true := by
      rw [← natp_lt]
      change ((«NATP» id).truthy &&
        (Prim.lt id («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» (coreImage kids)))).truthy) = true
      rw [hi,hr]
      rfl
    refine ⟨slot,.int 11,7,
      armResult (drainingCharge id slot kids) (drainingRetry id slot kids) (drainingKids id slot kids),
      ?_,?_,?_,?_⟩
    · exact Fn2.Instances.CoreWorld.«FN2-MACHINE-SLOT».dispatched
        (err := "no function FN2-MACHINE-SLOT/2") _ _
    · rfl
    · exact draining_run id slot budget kids hown hdir
    · rw [draining_emitted id budget kids h]
      rfl
  · intro h
    unfold «FN2-CNS-RUN-DRAINING»
    simp only [«EQ», Prim.equal, beq_eq_false_iff_ne.mpr h, Val.ofBool, Bool.false_eq_true, ↓reduceIte]
    rfl

#print axioms cns_draining_certificate
def drainWitnessKids : Fin 57 → Val := fun i =>
  if i.val = 3 then
    Native.updateNth (.int 19) (Val.ofList (List.replicate 7 (.int 1)))
      (Native.updateNth (.int 18) (Val.ofList (List.replicate 7 (.int 0)))
        (Native.updateNth (.int 9) (.int 4)
          (Native.updateNth (.int 8) (Val.ofList (List.replicate 7 (.int 4294967295))) (witnessKids i))))
  else if i.val = 17 then
    fieldWrite 57 (.int 0) (.int 0) (fieldWrite 1 (.int 0) (.int 0) (fieldWrite 0 (.int 0) (.int 10) (witnessKids i)))
  else witnessKids i

def drainWitnessCore : Val := coreImage drainWitnessKids
def drainWitnessResult : Val := «FN2-CNS-RUN-DRAINING» (.int 0) (.int 0) drainWitnessCore

theorem draining_mutation_positive :
    drainWitnessCore.toList.length = coreTuple.length ∧
    «FN2-CNS-SNAPSHOT-READ-CODE» (.int 0) drainWitnessCore = .sym ":OK" ∧
    «FN2-CNS-PHASE» (.int 0) («FN2-CNS-TABLE» drainWitnessCore) = .int 10 ∧
    drainWitnessResult.toList.take 4 = [.int 0,.int 20,.int 0,Val.nil] ∧
    «FN2-CNS-PHASE» (.int 0) («FN2-CNS-TABLE» (Native.nth (.int 4) drainWitnessResult)) = .int 0 ∧
    «FN2-CNS-GENERATION» (.int 0) («FN2-CNS-TABLE» (Native.nth (.int 4) drainWitnessResult)) = .int 1 ∧
    «FN2-CNS-CTL» (.int 0) («FN2-CNS-TABLE» (Native.nth (.int 4) drainWitnessResult)) = .int 4294967295 ∧
    «FN2-CNS-NEXT-FREE» (.int 0) («FN2-CNS-TABLE» (Native.nth (.int 4) drainWitnessResult)) = .int 4294967295 ∧
    «FN2-MACHINES-FREE-HEADI» (.int 6) («FN2-CORE-MACHINES» (Native.nth (.int 4) drainWitnessResult)) = .int 0 ∧
    «FN2-MACHINES-ACTIVE-COUNTI» (.int 6) («FN2-CORE-MACHINES» (Native.nth (.int 4) drainWitnessResult)) = .int 0 ∧
    «FN2-MACHINES-ADMISSION-CREDITSI» (.int 6) («FN2-CORE-MACHINES» (Native.nth (.int 4) drainWitnessResult)) = .int 1 ∧
    «FN2-CORE-CONTROL» (Native.nth (.int 4) drainWitnessResult) = «FN2-CORE-CONTROL» drainWitnessCore := by decide +kernel

end Fn2.Arms.CoreValidation

end
