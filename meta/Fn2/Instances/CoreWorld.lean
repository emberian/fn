-- Canonical certificates use the actual emitted world and its checked dispatch equations.
import Fn2.ACL2.Fuel
import Fn2.ACL2.Translation
import Fn2.Instances.LayerAEqns1
import Fn2.Instances.LayerAEqns2
import Fn2.Instances.LayerAEqns3
import Fn2.Instances.LayerAEqns4
set_option maxRecDepth 100000
namespace Fn2.Instances.CoreWorld
open Fn2.ACL2 Fn2.Instances.LayerAWorld
def fns : Fns := Fn2.Instances.LayerAWorld.fns
private theorem native_prefixes : ∀ n ∈ nativeCallNames, n.startsWith "FN2-" = false := by decide +kernel
theorem fn2_not_native (n : String) (h : n.startsWith "FN2-" = true) : nativeCallNames.contains n = false := by
  apply Bool.eq_false_iff.mpr
  intro hm
  have hn : n ∈ nativeCallNames := by simpa using hm
  have hf := native_prefixes n hn
  rw [h] at hf
  contradiction
theorem «HARD-ERROR».dispatched {err : String} («CTX» : Val) («STR» : Val) («ALIST» : Val) :
    (match nativeCall "HARD-ERROR" [«CTX», «STR», «ALIST»] with | some x => Except.ok x | none => match fns "HARD-ERROR" [«CTX», «STR», «ALIST»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«HARD-ERROR» «CTX» «STR» «ALIST») := by
  simp only [nativeCall_none "HARD-ERROR" [«CTX», «STR», «ALIST»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«HARD-ERROR».fns_eq]
theorem «FN2-CORE-MACHINES».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-CORE-MACHINES" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CORE-MACHINES" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CORE-MACHINES» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CORE-MACHINES" [«FN2-CORE»] (fn2_not_native "FN2-CORE-MACHINES" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CORE-MACHINES».fns_eq]
theorem «FN2-MACHINES-SLOT$AI».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-SLOT$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-SLOT$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-SLOT$AI» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-SLOT$AI" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-SLOT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-SLOT$AI».fns_eq]
theorem «FN2-MACHINES-SLOT».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-SLOT" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-SLOT" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-SLOT» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-SLOT" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-SLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-SLOT».fns_eq]
theorem «FN2-MACHINES-ROWS».dispatched {err : String} («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-ROWS" [«FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-ROWS" [«FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-ROWS» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-ROWS" [«FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-ROWS».fns_eq]
theorem «NOT».dispatched {err : String} («P» : Val) :
    (match nativeCall "NOT" [«P»] with | some x => Except.ok x | none => match fns "NOT" [«P»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«NOT» «P») := by
  simp only [nativeCall_none "NOT" [«P»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«NOT».fns_eq]
theorem «NATP».dispatched {err : String} («X» : Val) :
    (match nativeCall "NATP" [«X»] with | some x => Except.ok x | none => match fns "NATP" [«X»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«NATP» «X») := by
  simp only [nativeCall_none "NATP" [«X»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«NATP».fns_eq]
theorem «FN2-MACHINE-IDP».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-IDP" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-IDP" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-IDP» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-IDP" [«ID», «FN2-CORE»] (fn2_not_native "FN2-MACHINE-IDP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-IDP».fns_eq]
theorem «FN2-MACHINE-SLOT-READ-CODE».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-SLOT-READ-CODE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-SLOT-READ-CODE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-SLOT-READ-CODE» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-SLOT-READ-CODE" [«ID», «FN2-CORE»] (fn2_not_native "FN2-MACHINE-SLOT-READ-CODE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-SLOT-READ-CODE».fns_eq]
theorem «EQ».dispatched {err : String} («X» : Val) («Y» : Val) :
    (match nativeCall "EQ" [«X», «Y»] with | some x => Except.ok x | none => match fns "EQ" [«X», «Y»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«EQ» «X» «Y») := by
  simp only [nativeCall_none "EQ" [«X», «Y»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«EQ».fns_eq]
theorem «FN2-MACHINE-SLOT».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-SLOT" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-SLOT" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-SLOT» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-SLOT" [«ID», «FN2-CORE»] (fn2_not_native "FN2-MACHINE-SLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-SLOT».fns_eq]
theorem «FN2-CNS-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-CNS-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TABLE».fns_eq]
theorem «FN2-CNS-LEASE$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LEASE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LEASE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LEASE$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LEASE$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LEASE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LEASE$AI».fns_eq]
theorem «FN2-CNS-LEASE».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LEASE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LEASE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LEASE» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LEASE" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LEASE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LEASE».fns_eq]
theorem «FN2-MACHINES-KIND$AI».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-KIND$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-KIND$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-KIND$AI» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-KIND$AI" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-KIND$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-KIND$AI».fns_eq]
theorem «FN2-MACHINES-KIND».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-KIND" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-KIND" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-KIND» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-KIND" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-KIND" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-KIND».fns_eq]
theorem «FN2-MACHINE-KIND-READ-CODE».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-KIND-READ-CODE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-KIND-READ-CODE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-KIND-READ-CODE» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-KIND-READ-CODE" [«ID», «FN2-CORE»] (fn2_not_native "FN2-MACHINE-KIND-READ-CODE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-KIND-READ-CODE».fns_eq]
theorem «FN2-MACHINE-KIND».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-KIND" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-KIND" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-KIND» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-KIND" [«ID», «FN2-CORE»] (fn2_not_native "FN2-MACHINE-KIND" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-KIND».fns_eq]
theorem «FN2-BOOT-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-BOOT-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-BOOT-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-BOOT-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-BOOT-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-BOOT-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-BOOT-TABLE».fns_eq]
theorem «FN2-BOOT-ROWS».dispatched {err : String} («FN2-BOOT» : Val) :
    (match nativeCall "FN2-BOOT-ROWS" [«FN2-BOOT»] with | some x => Except.ok x | none => match fns "FN2-BOOT-ROWS" [«FN2-BOOT»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-BOOT-ROWS» «FN2-BOOT») := by
  simp only [nativeCall_none "FN2-BOOT-ROWS" [«FN2-BOOT»] (fn2_not_native "FN2-BOOT-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-BOOT-ROWS».fns_eq]
theorem «FN2-AUTH-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-AUTH-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-AUTH-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-AUTH-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-AUTH-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-AUTH-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-AUTH-TABLE».fns_eq]
theorem «FN2-AUTH-ROWS».dispatched {err : String} («FN2-AUTH» : Val) :
    (match nativeCall "FN2-AUTH-ROWS" [«FN2-AUTH»] with | some x => Except.ok x | none => match fns "FN2-AUTH-ROWS" [«FN2-AUTH»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-AUTH-ROWS» «FN2-AUTH») := by
  simp only [nativeCall_none "FN2-AUTH-ROWS" [«FN2-AUTH»] (fn2_not_native "FN2-AUTH-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-AUTH-ROWS».fns_eq]
theorem «FN2-CNS-ROWS».dispatched {err : String} («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ROWS" [«FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ROWS" [«FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ROWS» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ROWS" [«FN2-CNS»] (fn2_not_native "FN2-CNS-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ROWS».fns_eq]
theorem «FN2-CTL-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-CTL-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CTL-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CTL-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CTL-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-CTL-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CTL-TABLE».fns_eq]
theorem «FN2-CTL-ROWS».dispatched {err : String} («FN2-CTL» : Val) :
    (match nativeCall "FN2-CTL-ROWS" [«FN2-CTL»] with | some x => Except.ok x | none => match fns "FN2-CTL-ROWS" [«FN2-CTL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CTL-ROWS» «FN2-CTL») := by
  simp only [nativeCall_none "FN2-CTL-ROWS" [«FN2-CTL»] (fn2_not_native "FN2-CTL-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CTL-ROWS».fns_eq]
theorem «FN2-CURSOR-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-CURSOR-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CURSOR-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CURSOR-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CURSOR-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-CURSOR-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CURSOR-TABLE».fns_eq]
theorem «FN2-CURSOR-ROWS».dispatched {err : String} («FN2-CURSOR» : Val) :
    (match nativeCall "FN2-CURSOR-ROWS" [«FN2-CURSOR»] with | some x => Except.ok x | none => match fns "FN2-CURSOR-ROWS" [«FN2-CURSOR»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CURSOR-ROWS» «FN2-CURSOR») := by
  simp only [nativeCall_none "FN2-CURSOR-ROWS" [«FN2-CURSOR»] (fn2_not_native "FN2-CURSOR-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CURSOR-ROWS».fns_eq]
theorem «FN2-TXN-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-TXN-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-TXN-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-TXN-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-TXN-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-TXN-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-TXN-TABLE».fns_eq]
theorem «FN2-TXN-ROWS».dispatched {err : String} («FN2-TXN» : Val) :
    (match nativeCall "FN2-TXN-ROWS" [«FN2-TXN»] with | some x => Except.ok x | none => match fns "FN2-TXN-ROWS" [«FN2-TXN»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-TXN-ROWS» «FN2-TXN») := by
  simp only [nativeCall_none "FN2-TXN-ROWS" [«FN2-TXN»] (fn2_not_native "FN2-TXN-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-TXN-ROWS».fns_eq]
theorem «FN2-UPLOAD-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-UPLOAD-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-UPLOAD-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-UPLOAD-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-UPLOAD-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-UPLOAD-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-UPLOAD-TABLE».fns_eq]
theorem «FN2-UPLOAD-ROWS».dispatched {err : String} («FN2-UPLOAD» : Val) :
    (match nativeCall "FN2-UPLOAD-ROWS" [«FN2-UPLOAD»] with | some x => Except.ok x | none => match fns "FN2-UPLOAD-ROWS" [«FN2-UPLOAD»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-UPLOAD-ROWS» «FN2-UPLOAD») := by
  simp only [nativeCall_none "FN2-UPLOAD-ROWS" [«FN2-UPLOAD»] (fn2_not_native "FN2-UPLOAD-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-UPLOAD-ROWS».fns_eq]
theorem «FN2-CONN-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-CONN-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CONN-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CONN-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CONN-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-CONN-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CONN-TABLE».fns_eq]
theorem «FN2-CONN-ROWS».dispatched {err : String} («FN2-CONN» : Val) :
    (match nativeCall "FN2-CONN-ROWS" [«FN2-CONN»] with | some x => Except.ok x | none => match fns "FN2-CONN-ROWS" [«FN2-CONN»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CONN-ROWS» «FN2-CONN») := by
  simp only [nativeCall_none "FN2-CONN-ROWS" [«FN2-CONN»] (fn2_not_native "FN2-CONN-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CONN-ROWS».fns_eq]
theorem «FN2-SEALER-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-SEALER-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-SEALER-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-SEALER-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-SEALER-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-SEALER-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-SEALER-TABLE».fns_eq]
theorem «FN2-SEALER-ROWS».dispatched {err : String} («FN2-SEALER» : Val) :
    (match nativeCall "FN2-SEALER-ROWS" [«FN2-SEALER»] with | some x => Except.ok x | none => match fns "FN2-SEALER-ROWS" [«FN2-SEALER»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-SEALER-ROWS» «FN2-SEALER») := by
  simp only [nativeCall_none "FN2-SEALER-ROWS" [«FN2-SEALER»] (fn2_not_native "FN2-SEALER-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-SEALER-ROWS».fns_eq]
theorem «FN2-RECOVERY-MACHINE-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-RECOVERY-MACHINE-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-RECOVERY-MACHINE-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-RECOVERY-MACHINE-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-RECOVERY-MACHINE-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-RECOVERY-MACHINE-TABLE».fns_eq]
theorem «FN2-RECOVERY-MACHINE-ROWS».dispatched {err : String} («FN2-RECOVERY-MACHINE» : Val) :
    (match nativeCall "FN2-RECOVERY-MACHINE-ROWS" [«FN2-RECOVERY-MACHINE»] with | some x => Except.ok x | none => match fns "FN2-RECOVERY-MACHINE-ROWS" [«FN2-RECOVERY-MACHINE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-RECOVERY-MACHINE-ROWS» «FN2-RECOVERY-MACHINE») := by
  simp only [nativeCall_none "FN2-RECOVERY-MACHINE-ROWS" [«FN2-RECOVERY-MACHINE»] (fn2_not_native "FN2-RECOVERY-MACHINE-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-RECOVERY-MACHINE-ROWS».fns_eq]
theorem «FN2-COMMIT-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-COMMIT-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-COMMIT-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-COMMIT-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-COMMIT-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-COMMIT-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-COMMIT-TABLE».fns_eq]
theorem «FN2-COMMIT-ROWS».dispatched {err : String} («FN2-COMMIT» : Val) :
    (match nativeCall "FN2-COMMIT-ROWS" [«FN2-COMMIT»] with | some x => Except.ok x | none => match fns "FN2-COMMIT-ROWS" [«FN2-COMMIT»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-COMMIT-ROWS» «FN2-COMMIT») := by
  simp only [nativeCall_none "FN2-COMMIT-ROWS" [«FN2-COMMIT»] (fn2_not_native "FN2-COMMIT-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-COMMIT-ROWS».fns_eq]
theorem «FN2-SCRIBE-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-SCRIBE-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-SCRIBE-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-SCRIBE-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-SCRIBE-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-SCRIBE-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-SCRIBE-TABLE».fns_eq]
theorem «FN2-SCRIBE-ROWS».dispatched {err : String} («FN2-SCRIBE» : Val) :
    (match nativeCall "FN2-SCRIBE-ROWS" [«FN2-SCRIBE»] with | some x => Except.ok x | none => match fns "FN2-SCRIBE-ROWS" [«FN2-SCRIBE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-SCRIBE-ROWS» «FN2-SCRIBE») := by
  simp only [nativeCall_none "FN2-SCRIBE-ROWS" [«FN2-SCRIBE»] (fn2_not_native "FN2-SCRIBE-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-SCRIBE-ROWS».fns_eq]
theorem «FN2-ECHO-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-ECHO-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-ECHO-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-ECHO-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-ECHO-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-ECHO-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-ECHO-TABLE».fns_eq]
theorem «FN2-ECHO-ROWS».dispatched {err : String} («FN2-ECHO» : Val) :
    (match nativeCall "FN2-ECHO-ROWS" [«FN2-ECHO»] with | some x => Except.ok x | none => match fns "FN2-ECHO-ROWS" [«FN2-ECHO»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-ECHO-ROWS» «FN2-ECHO») := by
  simp only [nativeCall_none "FN2-ECHO-ROWS" [«FN2-ECHO»] (fn2_not_native "FN2-ECHO-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-ECHO-ROWS».fns_eq]
theorem «FN2-LISTENER-TABLE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-LISTENER-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-LISTENER-TABLE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-LISTENER-TABLE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-LISTENER-TABLE" [«FN2-CORE»] (fn2_not_native "FN2-LISTENER-TABLE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-LISTENER-TABLE».fns_eq]
theorem «FN2-LISTENER-ROWS».dispatched {err : String} («FN2-LISTENER» : Val) :
    (match nativeCall "FN2-LISTENER-ROWS" [«FN2-LISTENER»] with | some x => Except.ok x | none => match fns "FN2-LISTENER-ROWS" [«FN2-LISTENER»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-LISTENER-ROWS» «FN2-LISTENER») := by
  simp only [nativeCall_none "FN2-LISTENER-ROWS" [«FN2-LISTENER»] (fn2_not_native "FN2-LISTENER-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-LISTENER-ROWS».fns_eq]
theorem «EQL».dispatched {err : String} («X» : Val) («Y» : Val) :
    (match nativeCall "EQL" [«X», «Y»] with | some x => Except.ok x | none => match fns "EQL" [«X», «Y»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«EQL» «X» «Y») := by
  simp only [nativeCall_none "EQL" [«X», «Y»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«EQL».fns_eq]
theorem «FN2-MACHINE-PHASE-READ-CODE».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-PHASE-READ-CODE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-PHASE-READ-CODE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-PHASE-READ-CODE" [«ID», «FN2-CORE»] (fn2_not_native "FN2-MACHINE-PHASE-READ-CODE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-PHASE-READ-CODE».fns_eq]
theorem «FN2-CNS-SNAPSHOT-READ-CODE».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-SNAPSHOT-READ-CODE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-SNAPSHOT-READ-CODE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SNAPSHOT-READ-CODE» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-SNAPSHOT-READ-CODE" [«ID», «FN2-CORE»] (fn2_not_native "FN2-CNS-SNAPSHOT-READ-CODE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SNAPSHOT-READ-CODE».fns_eq]
theorem «FN2-CNS-ROW-LEASE».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-ROW-LEASE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-ROW-LEASE" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ROW-LEASE» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-ROW-LEASE" [«ID», «FN2-CORE»] (fn2_not_native "FN2-CNS-ROW-LEASE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ROW-LEASE».fns_eq]
theorem «FN2-CNS-LSLOT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LSLOT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LSLOT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LSLOT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LSLOT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LSLOT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LSLOT$AI».fns_eq]
theorem «FN2-CNS-LSLOT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LSLOT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LSLOT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LSLOT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LSLOT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LSLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LSLOT».fns_eq]
theorem «FN2-CNS-ROW-LSLOT».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-ROW-LSLOT" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-ROW-LSLOT" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ROW-LSLOT» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-ROW-LSLOT" [«ID», «FN2-CORE»] (fn2_not_native "FN2-CNS-ROW-LSLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ROW-LSLOT».fns_eq]
theorem «FN2-CNS-LGEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LGEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LGEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LGEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LGEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LGEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LGEN$AI».fns_eq]
theorem «FN2-CNS-LGEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LGEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LGEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LGEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LGEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LGEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LGEN».fns_eq]
theorem «FN2-CNS-ROW-LGEN».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-ROW-LGEN" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-ROW-LGEN" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ROW-LGEN» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-ROW-LGEN" [«ID», «FN2-CORE»] (fn2_not_native "FN2-CNS-ROW-LGEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ROW-LGEN».fns_eq]
theorem «FN2-CNS-GENERATION$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-GENERATION$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-GENERATION$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-GENERATION$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-GENERATION$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-GENERATION$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-GENERATION$AI».fns_eq]
theorem «FN2-CNS-GENERATION».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-GENERATION" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-GENERATION" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-GENERATION» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-GENERATION" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-GENERATION" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-GENERATION».fns_eq]
theorem «FN2-CNS-ROW-GENERATION».dispatched {err : String} («ID» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-ROW-GENERATION" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-ROW-GENERATION" [«ID», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ROW-GENERATION» «ID» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-ROW-GENERATION" [«ID», «FN2-CORE»] (fn2_not_native "FN2-CNS-ROW-GENERATION" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ROW-GENERATION».fns_eq]
theorem «FN2-MACHINES-FREE-HEADI».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-FREE-HEADI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-FREE-HEADI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-FREE-HEADI» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-FREE-HEADI" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-FREE-HEADI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-FREE-HEADI».fns_eq]
theorem «FN2-MACHINE-FREE-HEAD».dispatched {err : String} («ORD» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-FREE-HEAD" [«ORD», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-FREE-HEAD" [«ORD», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-FREE-HEAD» «ORD» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-FREE-HEAD" [«ORD», «FN2-CORE»] (fn2_not_native "FN2-MACHINE-FREE-HEAD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-FREE-HEAD».fns_eq]
theorem «FN2-MACHINES-GEN-LIMIT».dispatched {err : String} («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-GEN-LIMIT" [«FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-GEN-LIMIT" [«FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-GEN-LIMIT» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-GEN-LIMIT" [«FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-GEN-LIMIT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-GEN-LIMIT».fns_eq]
theorem «FN2-MACHINE-GEN-LIMIT».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-GEN-LIMIT" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-GEN-LIMIT" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-GEN-LIMIT» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-GEN-LIMIT" [«FN2-CORE»] (fn2_not_native "FN2-MACHINE-GEN-LIMIT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-GEN-LIMIT».fns_eq]
theorem «UPDATE-NTH-ARRAY».dispatched {err : String} («J» : Val) («KEY» : Val) («VAL» : Val) («L» : Val) :
    (match nativeCall "UPDATE-NTH-ARRAY" [«J», «KEY», «VAL», «L»] with | some x => Except.ok x | none => match fns "UPDATE-NTH-ARRAY" [«J», «KEY», «VAL», «L»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-NTH-ARRAY» «J» «KEY» «VAL» «L») := by
  simp only [nativeCall_none "UPDATE-NTH-ARRAY" [«J», «KEY», «VAL», «L»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-NTH-ARRAY».fns_eq]
theorem «UPDATE-FN2-CNS-PHASE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-PHASE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-PHASE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PHASE$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-PHASE$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PHASE$AI».fns_eq]
theorem «FN2-CNS-SET-PHASE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-PHASE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-PHASE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PHASE» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-PHASE" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-PHASE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PHASE».fns_eq]
theorem «UPDATE-FN2-CNS-GENERATION$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-GENERATION$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-GENERATION$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-GENERATION$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-GENERATION$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-GENERATION$AI».fns_eq]
theorem «FN2-CNS-SET-GENERATION».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-GENERATION" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-GENERATION" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-GENERATION» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-GENERATION" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-GENERATION" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-GENERATION».fns_eq]
theorem «UPDATE-FN2-CNS-CTL$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-CTL$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-CTL$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CTL$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-CTL$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CTL$AI».fns_eq]
theorem «FN2-CNS-SET-CTL».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-CTL" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-CTL" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CTL» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-CTL" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-CTL" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CTL».fns_eq]
theorem «UPDATE-FN2-CNS-CTL-GEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-CTL-GEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-CTL-GEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CTL-GEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-CTL-GEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CTL-GEN$AI».fns_eq]
theorem «FN2-CNS-SET-CTL-GEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-CTL-GEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-CTL-GEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CTL-GEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-CTL-GEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-CTL-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CTL-GEN».fns_eq]
theorem «UPDATE-FN2-CNS-EDGE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-EDGE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-EDGE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-EDGE$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-EDGE$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-EDGE$AI».fns_eq]
theorem «FN2-CNS-SET-EDGE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-EDGE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-EDGE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-EDGE» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-EDGE" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-EDGE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-EDGE».fns_eq]
theorem «UPDATE-FN2-CNS-TXN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-TXN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-TXN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TXN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-TXN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TXN$AI».fns_eq]
theorem «FN2-CNS-SET-TXN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-TXN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-TXN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TXN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-TXN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-TXN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TXN».fns_eq]
theorem «UPDATE-FN2-CNS-TXN-GEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-TXN-GEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-TXN-GEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TXN-GEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-TXN-GEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TXN-GEN$AI».fns_eq]
theorem «FN2-CNS-SET-TXN-GEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-TXN-GEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-TXN-GEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TXN-GEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-TXN-GEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-TXN-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TXN-GEN».fns_eq]
theorem «UPDATE-FN2-CNS-TX-SLOT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-TX-SLOT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-TX-SLOT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TX-SLOT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-TX-SLOT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TX-SLOT$AI».fns_eq]
theorem «FN2-CNS-SET-TX-SLOT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-TX-SLOT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-TX-SLOT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TX-SLOT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-TX-SLOT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-TX-SLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TX-SLOT».fns_eq]
theorem «UPDATE-FN2-CNS-TX-GEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-TX-GEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-TX-GEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TX-GEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-TX-GEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TX-GEN$AI».fns_eq]
theorem «FN2-CNS-SET-TX-GEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-TX-GEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-TX-GEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TX-GEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-TX-GEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-TX-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TX-GEN».fns_eq]
theorem «UPDATE-FN2-CNS-UPLOAD$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-UPLOAD$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-UPLOAD$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-UPLOAD$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-UPLOAD$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-UPLOAD$AI».fns_eq]
theorem «FN2-CNS-SET-UPLOAD».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-UPLOAD" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-UPLOAD" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-UPLOAD» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-UPLOAD" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-UPLOAD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-UPLOAD».fns_eq]
theorem «UPDATE-FN2-CNS-UPLOAD-GEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-UPLOAD-GEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-UPLOAD-GEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-UPLOAD-GEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-UPLOAD-GEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-UPLOAD-GEN$AI».fns_eq]
theorem «FN2-CNS-SET-UPLOAD-GEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-UPLOAD-GEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-UPLOAD-GEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-UPLOAD-GEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-UPLOAD-GEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-UPLOAD-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-UPLOAD-GEN».fns_eq]
theorem «UPDATE-FN2-CNS-NEXT-FREE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-NEXT-FREE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-NEXT-FREE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-NEXT-FREE$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-NEXT-FREE$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-NEXT-FREE$AI».fns_eq]
theorem «FN2-CNS-SET-NEXT-FREE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-NEXT-FREE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-NEXT-FREE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NEXT-FREE» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-NEXT-FREE" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-NEXT-FREE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NEXT-FREE».fns_eq]
theorem «INTEGER-RANGE-P».dispatched {err : String} («LOWER» : Val) («UPPER» : Val) («X» : Val) :
    (match nativeCall "INTEGER-RANGE-P" [«LOWER», «UPPER», «X»] with | some x => Except.ok x | none => match fns "INTEGER-RANGE-P" [«LOWER», «UPPER», «X»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«INTEGER-RANGE-P» «LOWER» «UPPER» «X») := by
  simp only [nativeCall_none "INTEGER-RANGE-P" [«LOWER», «UPPER», «X»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«INTEGER-RANGE-P».fns_eq]
theorem «UNSIGNED-BYTE-P».dispatched {err : String} («BITS» : Val) («X» : Val) :
    (match nativeCall "UNSIGNED-BYTE-P" [«BITS», «X»] with | some x => Except.ok x | none => match fns "UNSIGNED-BYTE-P" [«BITS», «X»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UNSIGNED-BYTE-P» «BITS» «X») := by
  simp only [nativeCall_none "UNSIGNED-BYTE-P" [«BITS», «X»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UNSIGNED-BYTE-P».fns_eq]
theorem «THROW-NONEXEC-ERROR».dispatched {err : String} («FN» : Val) («ACTUALS» : Val) :
    (match nativeCall "THROW-NONEXEC-ERROR" [«FN», «ACTUALS»] with | some x => Except.ok x | none => match fns "THROW-NONEXEC-ERROR" [«FN», «ACTUALS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«THROW-NONEXEC-ERROR» «FN» «ACTUALS») := by
  simp only [nativeCall_none "THROW-NONEXEC-ERROR" [«FN», «ACTUALS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«THROW-NONEXEC-ERROR».fns_eq]
theorem «UPDATE-FN2-CNS-TABLE».dispatched {err : String} («FN2-CNS» : Val) («FN2-CORE» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-TABLE" [«FN2-CNS», «FN2-CORE»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-TABLE" [«FN2-CNS», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TABLE» «FN2-CNS» «FN2-CORE») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-TABLE" [«FN2-CNS», «FN2-CORE»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TABLE».fns_eq]
theorem «UPDATE-FN2-MACHINES-WAIT-REASON$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "UPDATE-FN2-MACHINES-WAIT-REASON$AI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-MACHINES-WAIT-REASON$AI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-WAIT-REASON$AI» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "UPDATE-FN2-MACHINES-WAIT-REASON$AI" [«I», «V», «FN2-MACHINES»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-WAIT-REASON$AI».fns_eq]
theorem «FN2-MACHINES-SET-WAIT-REASON».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-SET-WAIT-REASON" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-SET-WAIT-REASON" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-SET-WAIT-REASON» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-SET-WAIT-REASON" [«I», «V», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-SET-WAIT-REASON" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-SET-WAIT-REASON».fns_eq]
theorem «UPDATE-FN2-CORE-MACHINES».dispatched {err : String} («FN2-MACHINES» : Val) («FN2-CORE» : Val) :
    (match nativeCall "UPDATE-FN2-CORE-MACHINES" [«FN2-MACHINES», «FN2-CORE»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CORE-MACHINES" [«FN2-MACHINES», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CORE-MACHINES» «FN2-MACHINES» «FN2-CORE») := by
  simp only [nativeCall_none "UPDATE-FN2-CORE-MACHINES" [«FN2-MACHINES», «FN2-CORE»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CORE-MACHINES».fns_eq]
theorem «FN2-CORE-CONTROL».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-CORE-CONTROL" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CORE-CONTROL" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CORE-CONTROL» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CORE-CONTROL" [«FN2-CORE»] (fn2_not_native "FN2-CORE-CONTROL" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CORE-CONTROL».fns_eq]
theorem «UPDATE-FN2-CONTROL-STOP».dispatched {err : String} («V» : Val) («FN2-CONTROL» : Val) :
    (match nativeCall "UPDATE-FN2-CONTROL-STOP" [«V», «FN2-CONTROL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CONTROL-STOP" [«V», «FN2-CONTROL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CONTROL-STOP» «V» «FN2-CONTROL») := by
  simp only [nativeCall_none "UPDATE-FN2-CONTROL-STOP" [«V», «FN2-CONTROL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CONTROL-STOP».fns_eq]
theorem «UPDATE-FN2-CONTROL-STOP-REASON».dispatched {err : String} («V» : Val) («FN2-CONTROL» : Val) :
    (match nativeCall "UPDATE-FN2-CONTROL-STOP-REASON" [«V», «FN2-CONTROL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CONTROL-STOP-REASON" [«V», «FN2-CONTROL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CONTROL-STOP-REASON» «V» «FN2-CONTROL») := by
  simp only [nativeCall_none "UPDATE-FN2-CONTROL-STOP-REASON" [«V», «FN2-CONTROL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CONTROL-STOP-REASON».fns_eq]
theorem «FN2-CONTROL-STOP».dispatched {err : String} («FN2-CONTROL» : Val) :
    (match nativeCall "FN2-CONTROL-STOP" [«FN2-CONTROL»] with | some x => Except.ok x | none => match fns "FN2-CONTROL-STOP" [«FN2-CONTROL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CONTROL-STOP» «FN2-CONTROL») := by
  simp only [nativeCall_none "FN2-CONTROL-STOP" [«FN2-CONTROL»] (fn2_not_native "FN2-CONTROL-STOP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CONTROL-STOP».fns_eq]
theorem «=».dispatched {err : String} («X» : Val) («Y» : Val) :
    (match nativeCall "=" [«X», «Y»] with | some x => Except.ok x | none => match fns "=" [«X», «Y»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«=» «X» «Y») := by
  simp only [nativeCall_none "=" [«X», «Y»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«=».fns_eq]
theorem «FN2-CONTROL-RECORD-STOP».dispatched {err : String} («REASON» : Val) («FN2-CONTROL» : Val) :
    (match nativeCall "FN2-CONTROL-RECORD-STOP" [«REASON», «FN2-CONTROL»] with | some x => Except.ok x | none => match fns "FN2-CONTROL-RECORD-STOP" [«REASON», «FN2-CONTROL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CONTROL-RECORD-STOP» «REASON» «FN2-CONTROL») := by
  simp only [nativeCall_none "FN2-CONTROL-RECORD-STOP" [«REASON», «FN2-CONTROL»] (fn2_not_native "FN2-CONTROL-RECORD-STOP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CONTROL-RECORD-STOP».fns_eq]
theorem «UPDATE-FN2-CORE-CONTROL».dispatched {err : String} («FN2-CONTROL» : Val) («FN2-CORE» : Val) :
    (match nativeCall "UPDATE-FN2-CORE-CONTROL" [«FN2-CONTROL», «FN2-CORE»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CORE-CONTROL" [«FN2-CONTROL», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CORE-CONTROL» «FN2-CONTROL» «FN2-CORE») := by
  simp only [nativeCall_none "UPDATE-FN2-CORE-CONTROL" [«FN2-CONTROL», «FN2-CORE»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CORE-CONTROL».fns_eq]
theorem «FN2-CORE-STOP».dispatched {err : String} («REASON» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CORE-STOP" [«REASON», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CORE-STOP" [«REASON», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CORE-STOP» «REASON» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CORE-STOP" [«REASON», «FN2-CORE»] (fn2_not_native "FN2-CORE-STOP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CORE-STOP».fns_eq]
theorem «FN2-MACHINE-REFUSE-WRITE».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-MACHINE-REFUSE-WRITE" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-MACHINE-REFUSE-WRITE" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINE-REFUSE-WRITE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-MACHINE-REFUSE-WRITE" [«FN2-CORE»] (fn2_not_native "FN2-MACHINE-REFUSE-WRITE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINE-REFUSE-WRITE».fns_eq]
theorem «FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE».dispatched {err : String} («ID» : Val) («FN2-ARMS-W-PHASE» : Val) («FN2-ARMS-W-GENERATION» : Val) («FN2-ARMS-W-WAIT-REASON» : Val) («FN2-ARMS-W-CTL» : Val) («FN2-ARMS-W-CTL-GEN» : Val) («FN2-ARMS-W-EDGE» : Val) («FN2-ARMS-W-TXN» : Val) («FN2-ARMS-W-TXN-GEN» : Val) («FN2-ARMS-W-TX-SLOT» : Val) («FN2-ARMS-W-TX-GEN» : Val) («FN2-ARMS-W-UPLOAD» : Val) («FN2-ARMS-W-UPLOAD-GEN» : Val) («FN2-ARMS-W-NEXT-FREE» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE" [«ID», «FN2-ARMS-W-PHASE», «FN2-ARMS-W-GENERATION», «FN2-ARMS-W-WAIT-REASON», «FN2-ARMS-W-CTL», «FN2-ARMS-W-CTL-GEN», «FN2-ARMS-W-EDGE», «FN2-ARMS-W-TXN», «FN2-ARMS-W-TXN-GEN», «FN2-ARMS-W-TX-SLOT», «FN2-ARMS-W-TX-GEN», «FN2-ARMS-W-UPLOAD», «FN2-ARMS-W-UPLOAD-GEN», «FN2-ARMS-W-NEXT-FREE», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE" [«ID», «FN2-ARMS-W-PHASE», «FN2-ARMS-W-GENERATION», «FN2-ARMS-W-WAIT-REASON», «FN2-ARMS-W-CTL», «FN2-ARMS-W-CTL-GEN», «FN2-ARMS-W-EDGE», «FN2-ARMS-W-TXN», «FN2-ARMS-W-TXN-GEN», «FN2-ARMS-W-TX-SLOT», «FN2-ARMS-W-TX-GEN», «FN2-ARMS-W-UPLOAD», «FN2-ARMS-W-UPLOAD-GEN», «FN2-ARMS-W-NEXT-FREE», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE» «ID» «FN2-ARMS-W-PHASE» «FN2-ARMS-W-GENERATION» «FN2-ARMS-W-WAIT-REASON» «FN2-ARMS-W-CTL» «FN2-ARMS-W-CTL-GEN» «FN2-ARMS-W-EDGE» «FN2-ARMS-W-TXN» «FN2-ARMS-W-TXN-GEN» «FN2-ARMS-W-TX-SLOT» «FN2-ARMS-W-TX-GEN» «FN2-ARMS-W-UPLOAD» «FN2-ARMS-W-UPLOAD-GEN» «FN2-ARMS-W-NEXT-FREE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE" [«ID», «FN2-ARMS-W-PHASE», «FN2-ARMS-W-GENERATION», «FN2-ARMS-W-WAIT-REASON», «FN2-ARMS-W-CTL», «FN2-ARMS-W-CTL-GEN», «FN2-ARMS-W-EDGE», «FN2-ARMS-W-TXN», «FN2-ARMS-W-TXN-GEN», «FN2-ARMS-W-TX-SLOT», «FN2-ARMS-W-TX-GEN», «FN2-ARMS-W-UPLOAD», «FN2-ARMS-W-UPLOAD-GEN», «FN2-ARMS-W-NEXT-FREE», «FN2-CORE»] (fn2_not_native "FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-WRITE+PHASE+GENERATION+WAIT-REASON+CTL+CTL-GEN+EDGE+TXN+TXN-GEN+TX-SLOT+TX-GEN+UPLOAD+UPLOAD-GEN+NEXT-FREE».fns_eq]
theorem «FN2-MACHINES-ACTIVE-COUNTI».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-ACTIVE-COUNTI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-ACTIVE-COUNTI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-ACTIVE-COUNTI» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-ACTIVE-COUNTI" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-ACTIVE-COUNTI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-ACTIVE-COUNTI».fns_eq]
theorem «UPDATE-FN2-MACHINES-FREE-HEADI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "UPDATE-FN2-MACHINES-FREE-HEADI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-MACHINES-FREE-HEADI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-FREE-HEADI» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "UPDATE-FN2-MACHINES-FREE-HEADI" [«I», «V», «FN2-MACHINES»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-FREE-HEADI».fns_eq]
theorem «FN2-MACHINES-ADMISSION-CREDITSI».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-ADMISSION-CREDITSI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-ADMISSION-CREDITSI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-ADMISSION-CREDITSI» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-ADMISSION-CREDITSI" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-ADMISSION-CREDITSI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-ADMISSION-CREDITSI».fns_eq]
theorem «UPDATE-FN2-MACHINES-ADMISSION-CREDITSI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "UPDATE-FN2-MACHINES-ADMISSION-CREDITSI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-MACHINES-ADMISSION-CREDITSI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-ADMISSION-CREDITSI» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "UPDATE-FN2-MACHINES-ADMISSION-CREDITSI" [«I», «V», «FN2-MACHINES»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-ADMISSION-CREDITSI».fns_eq]
theorem «UPDATE-FN2-MACHINES-ACTIVE-COUNTI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "UPDATE-FN2-MACHINES-ACTIVE-COUNTI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-MACHINES-ACTIVE-COUNTI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-ACTIVE-COUNTI» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "UPDATE-FN2-MACHINES-ACTIVE-COUNTI" [«I», «V», «FN2-MACHINES»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-ACTIVE-COUNTI».fns_eq]
theorem «ZP».dispatched {err : String} («X» : Val) :
    (match nativeCall "ZP" [«X»] with | some x => Except.ok x | none => match fns "ZP" [«X»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«ZP» «X») := by
  simp only [nativeCall_none "ZP" [«X»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«ZP».fns_eq]
theorem «FN2-MACHINES-STOP-WRITE».dispatched {err : String} («FN2-MACHINES» : Val) («FN2-CONTROL» : Val) :
    (match nativeCall "FN2-MACHINES-STOP-WRITE" [«FN2-MACHINES», «FN2-CONTROL»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-STOP-WRITE" [«FN2-MACHINES», «FN2-CONTROL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-STOP-WRITE» «FN2-MACHINES» «FN2-CONTROL») := by
  simp only [nativeCall_none "FN2-MACHINES-STOP-WRITE" [«FN2-MACHINES», «FN2-CONTROL»] (fn2_not_native "FN2-MACHINES-STOP-WRITE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-STOP-WRITE».fns_eq]
theorem «FN2-MACHINES-RECLAIM».dispatched {err : String} («ID» : Val) («ORD» : Val) («RETIRE» : Val) («FN2-MACHINES» : Val) («FN2-CONTROL» : Val) :
    (match nativeCall "FN2-MACHINES-RECLAIM" [«ID», «ORD», «RETIRE», «FN2-MACHINES», «FN2-CONTROL»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-RECLAIM" [«ID», «ORD», «RETIRE», «FN2-MACHINES», «FN2-CONTROL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-RECLAIM» «ID» «ORD» «RETIRE» «FN2-MACHINES» «FN2-CONTROL») := by
  simp only [nativeCall_none "FN2-MACHINES-RECLAIM" [«ID», «ORD», «RETIRE», «FN2-MACHINES», «FN2-CONTROL»] (fn2_not_native "FN2-MACHINES-RECLAIM" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-RECLAIM».fns_eq]
theorem «FN2-CNS-RECLAIM».dispatched {err : String} («ID» : Val) («ORD» : Val) («RETIRE» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-RECLAIM" [«ID», «ORD», «RETIRE», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-RECLAIM" [«ID», «ORD», «RETIRE», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-RECLAIM» «ID» «ORD» «RETIRE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-RECLAIM" [«ID», «ORD», «RETIRE», «FN2-CORE»] (fn2_not_native "FN2-CNS-RECLAIM" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-RECLAIM».fns_eq]
theorem «FN2-CORE-POOL».dispatched {err : String} («FN2-CORE» : Val) :
    (match nativeCall "FN2-CORE-POOL" [«FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CORE-POOL" [«FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CORE-POOL» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CORE-POOL" [«FN2-CORE»] (fn2_not_native "FN2-CORE-POOL" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CORE-POOL».fns_eq]
theorem «FN2-POOL-GEN$AI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-GEN$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-GEN$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-GEN$AI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-GEN$AI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-GEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-GEN$AI».fns_eq]
theorem «FN2-POOL-GEN».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-GEN" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-GEN" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-GEN» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-GEN" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-GEN».fns_eq]
theorem «FN2-POOL-ROWS».dispatched {err : String} («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-ROWS" [«FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-ROWS" [«FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-ROWS» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-ROWS" [«FN2-POOL»] (fn2_not_native "FN2-POOL-ROWS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-ROWS».fns_eq]
theorem «FN2-POOL-HANDLE-CODE».dispatched {err : String} («SLOT» : Val) («GEN» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-HANDLE-CODE" [«SLOT», «GEN», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-HANDLE-CODE" [«SLOT», «GEN», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-HANDLE-CODE» «SLOT» «GEN» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-HANDLE-CODE" [«SLOT», «GEN», «FN2-POOL»] (fn2_not_native "FN2-POOL-HANDLE-CODE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-HANDLE-CODE».fns_eq]
theorem «FN2-POOL-OUT-COUNT$AI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OUT-COUNT$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OUT-COUNT$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OUT-COUNT$AI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OUT-COUNT$AI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-OUT-COUNT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OUT-COUNT$AI».fns_eq]
theorem «FN2-POOL-OUT-COUNT».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OUT-COUNT" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OUT-COUNT" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OUT-COUNT» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OUT-COUNT" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-OUT-COUNT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OUT-COUNT».fns_eq]
theorem «FN2-POOL-OWNER-GEN$AI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OWNER-GEN$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OWNER-GEN$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-GEN$AI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OWNER-GEN$AI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-OWNER-GEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-GEN$AI».fns_eq]
theorem «FN2-POOL-OWNER-GEN».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OWNER-GEN" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OWNER-GEN" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-GEN» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OWNER-GEN" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-OWNER-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-GEN».fns_eq]
theorem «FN2-POOL-OWNER-SLOT$AI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OWNER-SLOT$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OWNER-SLOT$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-SLOT$AI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OWNER-SLOT$AI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-OWNER-SLOT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-SLOT$AI».fns_eq]
theorem «FN2-POOL-OWNER-SLOT».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OWNER-SLOT" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OWNER-SLOT" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-SLOT» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OWNER-SLOT" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-OWNER-SLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-SLOT».fns_eq]
theorem «FN2-POOL-OWNER-KIND$AI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OWNER-KIND$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OWNER-KIND$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-KIND$AI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OWNER-KIND$AI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-OWNER-KIND$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-KIND$AI».fns_eq]
theorem «FN2-POOL-OWNER-KIND».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OWNER-KIND" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OWNER-KIND" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-KIND» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OWNER-KIND" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-OWNER-KIND" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OWNER-KIND».fns_eq]
theorem «FN2-POOL-OWNERP».dispatched {err : String} («SLOT» : Val) («OKIND» : Val) («OSLOT» : Val) («OGEN» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-OWNERP" [«SLOT», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-OWNERP" [«SLOT», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-OWNERP» «SLOT» «OKIND» «OSLOT» «OGEN» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-OWNERP" [«SLOT», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] (fn2_not_native "FN2-POOL-OWNERP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-OWNERP».fns_eq]
theorem «FN2-POOL-STATE$AI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-STATE$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-STATE$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-STATE$AI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-STATE$AI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-STATE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-STATE$AI».fns_eq]
theorem «FN2-POOL-STATE».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-STATE" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-STATE" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-STATE» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-STATE" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-STATE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-STATE».fns_eq]
theorem «FN2-POOL-WORKSPACE-CODE».dispatched {err : String} («SLOT» : Val) («GEN» : Val) («OKIND» : Val) («OSLOT» : Val) («OGEN» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-WORKSPACE-CODE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-WORKSPACE-CODE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-WORKSPACE-CODE» «SLOT» «GEN» «OKIND» «OSLOT» «OGEN» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-WORKSPACE-CODE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] (fn2_not_native "FN2-POOL-WORKSPACE-CODE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-WORKSPACE-CODE».fns_eq]
theorem «FN2-POOL-CLASS$AI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-CLASS$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-CLASS$AI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-CLASS$AI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-CLASS$AI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-CLASS$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-CLASS$AI».fns_eq]
theorem «FN2-POOL-CLASS».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-CLASS" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-CLASS" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-CLASS» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-CLASS" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-CLASS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-CLASS».fns_eq]
theorem «FN2-POOL-CLASS-COUNTSI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-CLASS-COUNTSI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-CLASS-COUNTSI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-CLASS-COUNTSI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-CLASS-COUNTSI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-CLASS-COUNTSI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-CLASS-COUNTSI».fns_eq]
theorem «FN2-POOL-CLASS-HEADSI».dispatched {err : String} («I» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-CLASS-HEADSI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-CLASS-HEADSI" [«I», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-CLASS-HEADSI» «I» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-CLASS-HEADSI" [«I», «FN2-POOL»] (fn2_not_native "FN2-POOL-CLASS-HEADSI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-CLASS-HEADSI».fns_eq]
theorem «UPDATE-FN2-POOL-GEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "UPDATE-FN2-POOL-GEN$AI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-POOL-GEN$AI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-GEN$AI» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "UPDATE-FN2-POOL-GEN$AI" [«I», «V», «FN2-POOL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-GEN$AI».fns_eq]
theorem «FN2-POOL-SET-GEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-SET-GEN" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-SET-GEN" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-SET-GEN» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-SET-GEN" [«I», «V», «FN2-POOL»] (fn2_not_native "FN2-POOL-SET-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-SET-GEN».fns_eq]
theorem «UPDATE-FN2-POOL-NEXT-FREE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "UPDATE-FN2-POOL-NEXT-FREE$AI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-POOL-NEXT-FREE$AI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-NEXT-FREE$AI» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "UPDATE-FN2-POOL-NEXT-FREE$AI" [«I», «V», «FN2-POOL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-NEXT-FREE$AI».fns_eq]
theorem «FN2-POOL-SET-NEXT-FREE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-SET-NEXT-FREE" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-SET-NEXT-FREE" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-SET-NEXT-FREE» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-SET-NEXT-FREE" [«I», «V», «FN2-POOL»] (fn2_not_native "FN2-POOL-SET-NEXT-FREE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-SET-NEXT-FREE».fns_eq]
theorem «UPDATE-FN2-POOL-FILL$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "UPDATE-FN2-POOL-FILL$AI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-POOL-FILL$AI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-FILL$AI» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "UPDATE-FN2-POOL-FILL$AI" [«I», «V», «FN2-POOL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-FILL$AI».fns_eq]
theorem «FN2-POOL-SET-FILL».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-SET-FILL" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-SET-FILL" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-SET-FILL» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-SET-FILL" [«I», «V», «FN2-POOL»] (fn2_not_native "FN2-POOL-SET-FILL" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-SET-FILL».fns_eq]
theorem «UPDATE-FN2-POOL-CLASS-HEADSI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "UPDATE-FN2-POOL-CLASS-HEADSI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-POOL-CLASS-HEADSI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-CLASS-HEADSI» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "UPDATE-FN2-POOL-CLASS-HEADSI" [«I», «V», «FN2-POOL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-CLASS-HEADSI».fns_eq]
theorem «UPDATE-FN2-POOL-CLASS-COUNTSI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "UPDATE-FN2-POOL-CLASS-COUNTSI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-POOL-CLASS-COUNTSI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-CLASS-COUNTSI» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "UPDATE-FN2-POOL-CLASS-COUNTSI" [«I», «V», «FN2-POOL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-CLASS-COUNTSI».fns_eq]
theorem «FN2-POOL-NCLASSES».dispatched {err : String} («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-NCLASSES" [«FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-NCLASSES" [«FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-NCLASSES» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-NCLASSES" [«FN2-POOL»] (fn2_not_native "FN2-POOL-NCLASSES" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-NCLASSES».fns_eq]
theorem «FN2-POOL-RETIRED-COUNT».dispatched {err : String} («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-RETIRED-COUNT" [«FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-RETIRED-COUNT" [«FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-RETIRED-COUNT» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-RETIRED-COUNT" [«FN2-POOL»] (fn2_not_native "FN2-POOL-RETIRED-COUNT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-RETIRED-COUNT».fns_eq]
theorem «UPDATE-FN2-POOL-STATE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "UPDATE-FN2-POOL-STATE$AI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-POOL-STATE$AI" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-STATE$AI» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "UPDATE-FN2-POOL-STATE$AI" [«I», «V», «FN2-POOL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-STATE$AI».fns_eq]
theorem «FN2-POOL-SET-STATE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-SET-STATE" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-SET-STATE" [«I», «V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-SET-STATE» «I» «V» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-SET-STATE" [«I», «V», «FN2-POOL»] (fn2_not_native "FN2-POOL-SET-STATE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-SET-STATE».fns_eq]
theorem «UPDATE-FN2-POOL-RETIRED-COUNT».dispatched {err : String} («V» : Val) («FN2-POOL» : Val) :
    (match nativeCall "UPDATE-FN2-POOL-RETIRED-COUNT" [«V», «FN2-POOL»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-POOL-RETIRED-COUNT" [«V», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-RETIRED-COUNT» «V» «FN2-POOL») := by
  simp only [nativeCall_none "UPDATE-FN2-POOL-RETIRED-COUNT" [«V», «FN2-POOL»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-POOL-RETIRED-COUNT».fns_eq]
theorem «FN2-POOL-GEN-LIMIT».dispatched {err : String} («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-GEN-LIMIT" [«FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-GEN-LIMIT" [«FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-GEN-LIMIT» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-GEN-LIMIT" [«FN2-POOL»] (fn2_not_native "FN2-POOL-GEN-LIMIT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-GEN-LIMIT».fns_eq]
theorem «FN2-POOL-RELEASE-COUNTP».dispatched {err : String} («SLOT» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-RELEASE-COUNTP" [«SLOT», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-RELEASE-COUNTP" [«SLOT», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-RELEASE-COUNTP» «SLOT» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-RELEASE-COUNTP" [«SLOT», «FN2-POOL»] (fn2_not_native "FN2-POOL-RELEASE-COUNTP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-RELEASE-COUNTP».fns_eq]
theorem «FN2-POOL-RELEASE».dispatched {err : String} («SLOT» : Val) («GEN» : Val) («OKIND» : Val) («OSLOT» : Val) («OGEN» : Val) («FN2-POOL» : Val) :
    (match nativeCall "FN2-POOL-RELEASE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] with | some x => Except.ok x | none => match fns "FN2-POOL-RELEASE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-POOL-RELEASE» «SLOT» «GEN» «OKIND» «OSLOT» «OGEN» «FN2-POOL») := by
  simp only [nativeCall_none "FN2-POOL-RELEASE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL»] (fn2_not_native "FN2-POOL-RELEASE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-POOL-RELEASE».fns_eq]
theorem «FN2-CORE-RELEASE-CHILDREN».dispatched {err : String} («SLOT» : Val) («GEN» : Val) («OKIND» : Val) («OSLOT» : Val) («OGEN» : Val) («FN2-POOL» : Val) («FN2-CONTROL» : Val) :
    (match nativeCall "FN2-CORE-RELEASE-CHILDREN" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL», «FN2-CONTROL»] with | some x => Except.ok x | none => match fns "FN2-CORE-RELEASE-CHILDREN" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL», «FN2-CONTROL»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CORE-RELEASE-CHILDREN» «SLOT» «GEN» «OKIND» «OSLOT» «OGEN» «FN2-POOL» «FN2-CONTROL») := by
  simp only [nativeCall_none "FN2-CORE-RELEASE-CHILDREN" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-POOL», «FN2-CONTROL»] (fn2_not_native "FN2-CORE-RELEASE-CHILDREN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CORE-RELEASE-CHILDREN».fns_eq]
theorem «UPDATE-FN2-CORE-POOL».dispatched {err : String} («FN2-POOL» : Val) («FN2-CORE» : Val) :
    (match nativeCall "UPDATE-FN2-CORE-POOL" [«FN2-POOL», «FN2-CORE»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CORE-POOL" [«FN2-POOL», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CORE-POOL» «FN2-POOL» «FN2-CORE») := by
  simp only [nativeCall_none "UPDATE-FN2-CORE-POOL" [«FN2-POOL», «FN2-CORE»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CORE-POOL».fns_eq]
theorem «FN2-CNS-LEASE-RELEASE».dispatched {err : String} («SLOT» : Val) («GEN» : Val) («OKIND» : Val) («OSLOT» : Val) («OGEN» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-LEASE-RELEASE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-LEASE-RELEASE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LEASE-RELEASE» «SLOT» «GEN» «OKIND» «OSLOT» «OGEN» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-LEASE-RELEASE" [«SLOT», «GEN», «OKIND», «OSLOT», «OGEN», «FN2-CORE»] (fn2_not_native "FN2-CNS-LEASE-RELEASE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LEASE-RELEASE».fns_eq]
theorem «UPDATE-FN2-CNS-LSLOT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-LSLOT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-LSLOT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LSLOT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-LSLOT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LSLOT$AI».fns_eq]
theorem «FN2-CNS-SET-LSLOT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-LSLOT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-LSLOT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LSLOT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-LSLOT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-LSLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LSLOT».fns_eq]
theorem «UPDATE-FN2-CNS-LGEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-LGEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-LGEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LGEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-LGEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LGEN$AI».fns_eq]
theorem «FN2-CNS-SET-LGEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-LGEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-LGEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LGEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-LGEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-LGEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LGEN».fns_eq]
theorem «UPDATE-FN2-CNS-LEASE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-LEASE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-LEASE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LEASE$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-LEASE$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LEASE$AI».fns_eq]
theorem «FN2-CNS-SET-LEASE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-LEASE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-LEASE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LEASE» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-LEASE" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-LEASE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LEASE».fns_eq]
theorem «FN2-CNS-WRITE+LSLOT+LGEN+LEASE».dispatched {err : String} («ID» : Val) («FN2-ARMS-W-LSLOT» : Val) («FN2-ARMS-W-LGEN» : Val) («FN2-ARMS-W-LEASE» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-WRITE+LSLOT+LGEN+LEASE" [«ID», «FN2-ARMS-W-LSLOT», «FN2-ARMS-W-LGEN», «FN2-ARMS-W-LEASE», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-WRITE+LSLOT+LGEN+LEASE" [«ID», «FN2-ARMS-W-LSLOT», «FN2-ARMS-W-LGEN», «FN2-ARMS-W-LEASE», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-WRITE+LSLOT+LGEN+LEASE» «ID» «FN2-ARMS-W-LSLOT» «FN2-ARMS-W-LGEN» «FN2-ARMS-W-LEASE» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-WRITE+LSLOT+LGEN+LEASE" [«ID», «FN2-ARMS-W-LSLOT», «FN2-ARMS-W-LGEN», «FN2-ARMS-W-LEASE», «FN2-CORE»] (fn2_not_native "FN2-CNS-WRITE+LSLOT+LGEN+LEASE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-WRITE+LSLOT+LGEN+LEASE».fns_eq]
theorem «MEMBER-EQ-EXEC$GUARD-CHECK».dispatched {err : String} («X» : Val) («LST» : Val) :
    (match nativeCall "MEMBER-EQ-EXEC$GUARD-CHECK" [«X», «LST»] with | some x => Except.ok x | none => match fns "MEMBER-EQ-EXEC$GUARD-CHECK" [«X», «LST»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«MEMBER-EQ-EXEC$GUARD-CHECK» «X» «LST») := by
  simp only [nativeCall_none "MEMBER-EQ-EXEC$GUARD-CHECK" [«X», «LST»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«MEMBER-EQ-EXEC$GUARD-CHECK».fns_eq]
theorem «ATOM».dispatched {err : String} («X» : Val) :
    (match nativeCall "ATOM" [«X»] with | some x => Except.ok x | none => match fns "ATOM" [«X»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«ATOM» «X») := by
  simp only [nativeCall_none "ATOM" [«X»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«ATOM».fns_eq]
theorem «ENDP».dispatched {err : String} («X» : Val) :
    (match nativeCall "ENDP" [«X»] with | some x => Except.ok x | none => match fns "ENDP" [«X»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«ENDP» «X») := by
  simp only [nativeCall_none "ENDP" [«X»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«ENDP».fns_eq]
theorem «MEMBER-EQ-EXEC».dispatched {err : String} («X» : Val) («LST» : Val) :
    (match nativeCall "MEMBER-EQ-EXEC" [«X», «LST»] with | some x => Except.ok x | none => match fns "MEMBER-EQ-EXEC" [«X», «LST»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«MEMBER-EQ-EXEC» «X» «LST») := by
  simp only [nativeCall_none "MEMBER-EQ-EXEC" [«X», «LST»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«MEMBER-EQ-EXEC».fns_eq]
theorem «FN2-CNS-RUN-DRAINING».dispatched {err : String} («ID» : Val) («BUDGET» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-RUN-DRAINING" [«ID», «BUDGET», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-RUN-DRAINING" [«ID», «BUDGET», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-RUN-DRAINING» «ID» «BUDGET» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-RUN-DRAINING" [«ID», «BUDGET», «FN2-CORE»] (fn2_not_native "FN2-CNS-RUN-DRAINING" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-RUN-DRAINING».fns_eq]
theorem «UPDATE-FN2-CNS-REVENT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-REVENT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-REVENT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-REVENT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-REVENT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-REVENT$AI».fns_eq]
theorem «FN2-CNS-SET-REVENT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-REVENT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-REVENT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REVENT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-REVENT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-REVENT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REVENT».fns_eq]
theorem «UPDATE-FN2-CNS-ROUTCOME$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-ROUTCOME$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-ROUTCOME$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ROUTCOME$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-ROUTCOME$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ROUTCOME$AI».fns_eq]
theorem «FN2-CNS-SET-ROUTCOME».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-ROUTCOME" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-ROUTCOME" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ROUTCOME» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-ROUTCOME" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-ROUTCOME" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ROUTCOME».fns_eq]
theorem «UPDATE-FN2-CNS-RCOUNT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-RCOUNT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-RCOUNT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-RCOUNT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-RCOUNT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-RCOUNT$AI».fns_eq]
theorem «FN2-CNS-SET-RCOUNT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-RCOUNT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-RCOUNT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-RCOUNT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-RCOUNT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-RCOUNT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-RCOUNT».fns_eq]
theorem «UPDATE-FN2-CNS-RREADY$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-RREADY$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-RREADY$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-RREADY$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-RREADY$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-RREADY$AI».fns_eq]
theorem «FN2-CNS-SET-RREADY».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-RREADY" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-RREADY" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-RREADY» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-RREADY" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-RREADY" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-RREADY».fns_eq]
theorem «FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY».dispatched {err : String} («ID» : Val) («FN2-ARMS-W-REVENT» : Val) («FN2-ARMS-W-ROUTCOME» : Val) («FN2-ARMS-W-RCOUNT» : Val) («FN2-ARMS-W-RREADY» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY" [«ID», «FN2-ARMS-W-REVENT», «FN2-ARMS-W-ROUTCOME», «FN2-ARMS-W-RCOUNT», «FN2-ARMS-W-RREADY», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY" [«ID», «FN2-ARMS-W-REVENT», «FN2-ARMS-W-ROUTCOME», «FN2-ARMS-W-RCOUNT», «FN2-ARMS-W-RREADY», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY» «ID» «FN2-ARMS-W-REVENT» «FN2-ARMS-W-ROUTCOME» «FN2-ARMS-W-RCOUNT» «FN2-ARMS-W-RREADY» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY" [«ID», «FN2-ARMS-W-REVENT», «FN2-ARMS-W-ROUTCOME», «FN2-ARMS-W-RCOUNT», «FN2-ARMS-W-RREADY», «FN2-CORE»] (fn2_not_native "FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-WRITE+REVENT+ROUTCOME+RCOUNT+RREADY».fns_eq]
theorem «FN2-CNS-ON-READ-RESULT».dispatched {err : String} («ID» : Val) («EVENT» : Val) («OUTCOME» : Val) («REASON» : Val) («COUNT» : Val) («AUX0» : Val) («AUX1» : Val) («FN2-CORE» : Val) :
    (match nativeCall "FN2-CNS-ON-READ-RESULT" [«ID», «EVENT», «OUTCOME», «REASON», «COUNT», «AUX0», «AUX1», «FN2-CORE»] with | some x => Except.ok x | none => match fns "FN2-CNS-ON-READ-RESULT" [«ID», «EVENT», «OUTCOME», «REASON», «COUNT», «AUX0», «AUX1», «FN2-CORE»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ON-READ-RESULT» «ID» «EVENT» «OUTCOME» «REASON» «COUNT» «AUX0» «AUX1» «FN2-CORE») := by
  simp only [nativeCall_none "FN2-CNS-ON-READ-RESULT" [«ID», «EVENT», «OUTCOME», «REASON», «COUNT», «AUX0», «AUX1», «FN2-CORE»] (fn2_not_native "FN2-CNS-ON-READ-RESULT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ON-READ-RESULT».fns_eq]
theorem «FN2-CNS-PHASE$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PHASE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PHASE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PHASE$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PHASE$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PHASE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PHASE$AI».fns_eq]
theorem «FN2-CNS-PHASE».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PHASE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PHASE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PHASE» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PHASE" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PHASE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PHASE».fns_eq]
theorem «FN2-CNS-PRINCIPAL-SLOT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PRINCIPAL-SLOT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PRINCIPAL-SLOT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PRINCIPAL-SLOT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PRINCIPAL-SLOT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PRINCIPAL-SLOT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PRINCIPAL-SLOT$AI».fns_eq]
theorem «FN2-CNS-PRINCIPAL-SLOT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PRINCIPAL-SLOT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PRINCIPAL-SLOT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PRINCIPAL-SLOT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PRINCIPAL-SLOT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PRINCIPAL-SLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PRINCIPAL-SLOT».fns_eq]
theorem «UPDATE-FN2-CNS-PRINCIPAL-SLOT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-PRINCIPAL-SLOT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-PRINCIPAL-SLOT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PRINCIPAL-SLOT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-PRINCIPAL-SLOT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PRINCIPAL-SLOT$AI».fns_eq]
theorem «FN2-CNS-SET-PRINCIPAL-SLOT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-PRINCIPAL-SLOT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-PRINCIPAL-SLOT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PRINCIPAL-SLOT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-PRINCIPAL-SLOT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-PRINCIPAL-SLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PRINCIPAL-SLOT».fns_eq]
theorem «FN2-CNS-ACCOUNT-REF$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ACCOUNT-REF$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ACCOUNT-REF$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ACCOUNT-REF$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ACCOUNT-REF$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ACCOUNT-REF$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ACCOUNT-REF$AI».fns_eq]
theorem «FN2-CNS-ACCOUNT-REF».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ACCOUNT-REF" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ACCOUNT-REF" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ACCOUNT-REF» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ACCOUNT-REF" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ACCOUNT-REF" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ACCOUNT-REF».fns_eq]
theorem «UPDATE-FN2-CNS-ACCOUNT-REF$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-ACCOUNT-REF$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-ACCOUNT-REF$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ACCOUNT-REF$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-ACCOUNT-REF$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ACCOUNT-REF$AI».fns_eq]
theorem «FN2-CNS-SET-ACCOUNT-REF».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-ACCOUNT-REF" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-ACCOUNT-REF" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ACCOUNT-REF» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-ACCOUNT-REF" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-ACCOUNT-REF" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ACCOUNT-REF».fns_eq]
theorem «FN2-CNS-DEADLINE$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-DEADLINE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-DEADLINE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-DEADLINE$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-DEADLINE$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-DEADLINE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-DEADLINE$AI».fns_eq]
theorem «FN2-CNS-DEADLINE».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-DEADLINE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-DEADLINE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-DEADLINE» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-DEADLINE" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-DEADLINE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-DEADLINE».fns_eq]
theorem «UPDATE-FN2-CNS-DEADLINE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-DEADLINE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-DEADLINE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-DEADLINE$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-DEADLINE$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-DEADLINE$AI».fns_eq]
theorem «FN2-CNS-SET-DEADLINE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-DEADLINE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-DEADLINE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-DEADLINE» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-DEADLINE" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-DEADLINE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-DEADLINE».fns_eq]
theorem «FN2-CNS-CTL$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CTL$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CTL$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CTL$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CTL$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CTL$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CTL$AI».fns_eq]
theorem «FN2-CNS-CTL».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CTL" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CTL" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CTL» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CTL" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CTL" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CTL».fns_eq]
theorem «FN2-CNS-CTL-GEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CTL-GEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CTL-GEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CTL-GEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CTL-GEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CTL-GEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CTL-GEN$AI».fns_eq]
theorem «FN2-CNS-CTL-GEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CTL-GEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CTL-GEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CTL-GEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CTL-GEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CTL-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CTL-GEN».fns_eq]
theorem «FN2-CNS-REQUEST$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-REQUEST$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-REQUEST$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-REQUEST$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-REQUEST$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-REQUEST$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-REQUEST$AI».fns_eq]
theorem «FN2-CNS-REQUEST».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-REQUEST" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-REQUEST" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-REQUEST» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-REQUEST" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-REQUEST" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-REQUEST».fns_eq]
theorem «UPDATE-FN2-CNS-REQUEST$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-REQUEST$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-REQUEST$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-REQUEST$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-REQUEST$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-REQUEST$AI».fns_eq]
theorem «FN2-CNS-SET-REQUEST».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-REQUEST" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-REQUEST" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REQUEST» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-REQUEST" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-REQUEST" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REQUEST».fns_eq]
theorem «FN2-CNS-FPOS$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FPOS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FPOS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FPOS$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FPOS$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FPOS$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FPOS$AI».fns_eq]
theorem «FN2-CNS-FPOS».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FPOS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FPOS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FPOS» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FPOS" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FPOS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FPOS».fns_eq]
theorem «UPDATE-FN2-CNS-FPOS$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-FPOS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-FPOS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FPOS$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-FPOS$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FPOS$AI».fns_eq]
theorem «FN2-CNS-SET-FPOS».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-FPOS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-FPOS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FPOS» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-FPOS" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-FPOS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FPOS».fns_eq]
theorem «FN2-CNS-FLEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FLEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FLEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FLEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FLEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FLEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FLEN$AI».fns_eq]
theorem «FN2-CNS-FLEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FLEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FLEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FLEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FLEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FLEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FLEN».fns_eq]
theorem «UPDATE-FN2-CNS-FLEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-FLEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-FLEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FLEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-FLEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FLEN$AI».fns_eq]
theorem «FN2-CNS-SET-FLEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-FLEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-FLEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FLEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-FLEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-FLEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FLEN».fns_eq]
theorem «FN2-CNS-FKIND$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FKIND$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FKIND$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FKIND$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FKIND$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FKIND$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FKIND$AI».fns_eq]
theorem «FN2-CNS-FKIND».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FKIND" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FKIND" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FKIND» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FKIND" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FKIND" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FKIND».fns_eq]
theorem «UPDATE-FN2-CNS-FKIND$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-FKIND$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-FKIND$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FKIND$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-FKIND$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FKIND$AI».fns_eq]
theorem «FN2-CNS-SET-FKIND».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-FKIND" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-FKIND" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FKIND» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-FKIND" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-FKIND" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FKIND».fns_eq]
theorem «FN2-CNS-VERB$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-VERB$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-VERB$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-VERB$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-VERB$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-VERB$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-VERB$AI».fns_eq]
theorem «FN2-CNS-VERB».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-VERB" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-VERB" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-VERB» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-VERB" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-VERB" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-VERB».fns_eq]
theorem «UPDATE-FN2-CNS-VERB$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-VERB$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-VERB$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-VERB$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-VERB$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-VERB$AI».fns_eq]
theorem «FN2-CNS-SET-VERB».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-VERB" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-VERB" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-VERB» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-VERB" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-VERB" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-VERB».fns_eq]
theorem «FN2-CNS-CONSUMER$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CONSUMER$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CONSUMER$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CONSUMER$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CONSUMER$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CONSUMER$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CONSUMER$AI».fns_eq]
theorem «FN2-CNS-CONSUMER».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CONSUMER" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CONSUMER" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CONSUMER» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CONSUMER" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CONSUMER" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CONSUMER».fns_eq]
theorem «UPDATE-FN2-CNS-CONSUMER$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-CONSUMER$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-CONSUMER$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CONSUMER$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-CONSUMER$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CONSUMER$AI».fns_eq]
theorem «FN2-CNS-SET-CONSUMER».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-CONSUMER" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-CONSUMER" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CONSUMER» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-CONSUMER" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-CONSUMER" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CONSUMER».fns_eq]
theorem «FN2-CNS-EPOCH$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-EPOCH$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-EPOCH$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-EPOCH$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-EPOCH$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-EPOCH$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-EPOCH$AI».fns_eq]
theorem «FN2-CNS-EPOCH».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-EPOCH" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-EPOCH" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-EPOCH» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-EPOCH" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-EPOCH" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-EPOCH».fns_eq]
theorem «UPDATE-FN2-CNS-EPOCH$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-EPOCH$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-EPOCH$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-EPOCH$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-EPOCH$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-EPOCH$AI».fns_eq]
theorem «FN2-CNS-SET-EPOCH».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-EPOCH" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-EPOCH" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-EPOCH» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-EPOCH" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-EPOCH" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-EPOCH».fns_eq]
theorem «FN2-CNS-OP$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-OP$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-OP$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-OP$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-OP$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-OP$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-OP$AI».fns_eq]
theorem «FN2-CNS-OP».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-OP" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-OP" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-OP» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-OP" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-OP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-OP».fns_eq]
theorem «UPDATE-FN2-CNS-OP$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-OP$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-OP$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-OP$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-OP$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-OP$AI».fns_eq]
theorem «FN2-CNS-SET-OP».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-OP" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-OP" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-OP» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-OP" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-OP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-OP».fns_eq]
theorem «FN2-CNS-TO$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TO$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TO$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TO$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TO$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TO$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TO$AI».fns_eq]
theorem «FN2-CNS-TO».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TO" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TO" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TO» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TO" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TO" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TO».fns_eq]
theorem «UPDATE-FN2-CNS-TO$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-TO$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-TO$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TO$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-TO$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-TO$AI».fns_eq]
theorem «FN2-CNS-SET-TO».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-TO" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-TO" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TO» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-TO" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-TO" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-TO».fns_eq]
theorem «FN2-CNS-CSTART$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CSTART$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CSTART$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CSTART$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CSTART$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CSTART$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CSTART$AI».fns_eq]
theorem «FN2-CNS-CSTART».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CSTART" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CSTART" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CSTART» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CSTART" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CSTART" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CSTART».fns_eq]
theorem «UPDATE-FN2-CNS-CSTART$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-CSTART$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-CSTART$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CSTART$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-CSTART$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CSTART$AI».fns_eq]
theorem «FN2-CNS-SET-CSTART».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-CSTART" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-CSTART" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CSTART» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-CSTART" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-CSTART" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CSTART».fns_eq]
theorem «FN2-CNS-PAGE-LIMIT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PAGE-LIMIT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PAGE-LIMIT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PAGE-LIMIT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PAGE-LIMIT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PAGE-LIMIT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PAGE-LIMIT$AI».fns_eq]
theorem «FN2-CNS-PAGE-LIMIT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PAGE-LIMIT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PAGE-LIMIT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PAGE-LIMIT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PAGE-LIMIT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PAGE-LIMIT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PAGE-LIMIT».fns_eq]
theorem «UPDATE-FN2-CNS-PAGE-LIMIT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-PAGE-LIMIT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-PAGE-LIMIT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PAGE-LIMIT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-PAGE-LIMIT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PAGE-LIMIT$AI».fns_eq]
theorem «FN2-CNS-SET-PAGE-LIMIT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-PAGE-LIMIT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-PAGE-LIMIT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PAGE-LIMIT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-PAGE-LIMIT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-PAGE-LIMIT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PAGE-LIMIT».fns_eq]
theorem «FN2-CNS-WAIT-MS$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-WAIT-MS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-WAIT-MS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-WAIT-MS$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-WAIT-MS$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-WAIT-MS$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-WAIT-MS$AI».fns_eq]
theorem «FN2-CNS-WAIT-MS».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-WAIT-MS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-WAIT-MS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-WAIT-MS» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-WAIT-MS" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-WAIT-MS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-WAIT-MS».fns_eq]
theorem «UPDATE-FN2-CNS-WAIT-MS$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-WAIT-MS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-WAIT-MS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-WAIT-MS$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-WAIT-MS$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-WAIT-MS$AI».fns_eq]
theorem «FN2-CNS-SET-WAIT-MS».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-WAIT-MS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-WAIT-MS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-WAIT-MS» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-WAIT-MS" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-WAIT-MS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-WAIT-MS».fns_eq]
theorem «FN2-CNS-CPOS$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CPOS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CPOS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CPOS$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CPOS$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CPOS$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CPOS$AI».fns_eq]
theorem «FN2-CNS-CPOS».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CPOS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CPOS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CPOS» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CPOS" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CPOS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CPOS».fns_eq]
theorem «UPDATE-FN2-CNS-CPOS$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-CPOS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-CPOS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CPOS$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-CPOS$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CPOS$AI».fns_eq]
theorem «FN2-CNS-SET-CPOS».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-CPOS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-CPOS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CPOS» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-CPOS" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-CPOS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CPOS».fns_eq]
theorem «FN2-CNS-VERSION$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-VERSION$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-VERSION$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-VERSION$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-VERSION$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-VERSION$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-VERSION$AI».fns_eq]
theorem «FN2-CNS-VERSION».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-VERSION" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-VERSION" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-VERSION» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-VERSION" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-VERSION" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-VERSION».fns_eq]
theorem «UPDATE-FN2-CNS-VERSION$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-VERSION$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-VERSION$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-VERSION$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-VERSION$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-VERSION$AI».fns_eq]
theorem «FN2-CNS-SET-VERSION».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-VERSION" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-VERSION" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-VERSION» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-VERSION" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-VERSION" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-VERSION».fns_eq]
theorem «FN2-CNS-PUB-FRONTIER$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PUB-FRONTIER$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PUB-FRONTIER$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PUB-FRONTIER$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PUB-FRONTIER$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PUB-FRONTIER$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PUB-FRONTIER$AI».fns_eq]
theorem «FN2-CNS-PUB-FRONTIER».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PUB-FRONTIER" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PUB-FRONTIER" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PUB-FRONTIER» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PUB-FRONTIER" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PUB-FRONTIER" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PUB-FRONTIER».fns_eq]
theorem «UPDATE-FN2-CNS-PUB-FRONTIER$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-PUB-FRONTIER$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-PUB-FRONTIER$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PUB-FRONTIER$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-PUB-FRONTIER$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PUB-FRONTIER$AI».fns_eq]
theorem «FN2-CNS-SET-PUB-FRONTIER».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-PUB-FRONTIER" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-PUB-FRONTIER" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PUB-FRONTIER» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-PUB-FRONTIER" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-PUB-FRONTIER" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PUB-FRONTIER».fns_eq]
theorem «FN2-CNS-COUNT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-COUNT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-COUNT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-COUNT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-COUNT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-COUNT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-COUNT$AI».fns_eq]
theorem «FN2-CNS-COUNT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-COUNT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-COUNT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-COUNT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-COUNT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-COUNT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-COUNT».fns_eq]
theorem «UPDATE-FN2-CNS-COUNT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-COUNT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-COUNT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-COUNT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-COUNT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-COUNT$AI».fns_eq]
theorem «FN2-CNS-SET-COUNT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-COUNT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-COUNT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-COUNT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-COUNT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-COUNT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-COUNT».fns_eq]
theorem «FN2-CNS-MORE$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-MORE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-MORE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-MORE$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-MORE$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-MORE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-MORE$AI».fns_eq]
theorem «FN2-CNS-MORE».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-MORE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-MORE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-MORE» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-MORE" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-MORE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-MORE».fns_eq]
theorem «UPDATE-FN2-CNS-MORE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-MORE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-MORE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-MORE$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-MORE$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-MORE$AI».fns_eq]
theorem «FN2-CNS-SET-MORE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-MORE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-MORE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-MORE» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-MORE" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-MORE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-MORE».fns_eq]
theorem «FN2-CNS-OUTCOME$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-OUTCOME$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-OUTCOME$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-OUTCOME$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-OUTCOME$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-OUTCOME$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-OUTCOME$AI».fns_eq]
theorem «FN2-CNS-OUTCOME».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-OUTCOME" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-OUTCOME" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-OUTCOME» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-OUTCOME" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-OUTCOME" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-OUTCOME».fns_eq]
theorem «UPDATE-FN2-CNS-OUTCOME$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-OUTCOME$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-OUTCOME$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-OUTCOME$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-OUTCOME$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-OUTCOME$AI».fns_eq]
theorem «FN2-CNS-SET-OUTCOME».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-OUTCOME" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-OUTCOME" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-OUTCOME» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-OUTCOME" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-OUTCOME" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-OUTCOME».fns_eq]
theorem «FN2-CNS-REASON$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-REASON$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-REASON$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-REASON$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-REASON$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-REASON$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-REASON$AI».fns_eq]
theorem «FN2-CNS-REASON».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-REASON" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-REASON" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-REASON» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-REASON" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-REASON" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-REASON».fns_eq]
theorem «UPDATE-FN2-CNS-REASON$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-REASON$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-REASON$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-REASON$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-REASON$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-REASON$AI».fns_eq]
theorem «FN2-CNS-SET-REASON».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-REASON" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-REASON" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REASON» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-REASON" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-REASON" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-REASON».fns_eq]
theorem «FN2-CNS-POSTED$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-POSTED$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-POSTED$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-POSTED$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-POSTED$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-POSTED$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-POSTED$AI».fns_eq]
theorem «FN2-CNS-POSTED».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-POSTED" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-POSTED" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-POSTED» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-POSTED" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-POSTED" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-POSTED».fns_eq]
theorem «UPDATE-FN2-CNS-POSTED$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-POSTED$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-POSTED$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-POSTED$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-POSTED$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-POSTED$AI».fns_eq]
theorem «FN2-CNS-SET-POSTED».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-POSTED" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-POSTED" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-POSTED» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-POSTED" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-POSTED" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-POSTED».fns_eq]
theorem «FN2-CNS-POSTED-WORD$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-POSTED-WORD$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-POSTED-WORD$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-POSTED-WORD$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-POSTED-WORD$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-POSTED-WORD$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-POSTED-WORD$AI».fns_eq]
theorem «FN2-CNS-POSTED-WORD».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-POSTED-WORD" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-POSTED-WORD" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-POSTED-WORD» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-POSTED-WORD" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-POSTED-WORD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-POSTED-WORD».fns_eq]
theorem «UPDATE-FN2-CNS-POSTED-WORD$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-POSTED-WORD$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-POSTED-WORD$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-POSTED-WORD$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-POSTED-WORD$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-POSTED-WORD$AI».fns_eq]
theorem «FN2-CNS-SET-POSTED-WORD».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-POSTED-WORD" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-POSTED-WORD" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-POSTED-WORD» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-POSTED-WORD" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-POSTED-WORD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-POSTED-WORD».fns_eq]
theorem «FN2-CNS-EDGE$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-EDGE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-EDGE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-EDGE$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-EDGE$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-EDGE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-EDGE$AI».fns_eq]
theorem «FN2-CNS-EDGE».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-EDGE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-EDGE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-EDGE» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-EDGE" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-EDGE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-EDGE».fns_eq]
theorem «FN2-CNS-TXN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TXN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TXN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TXN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TXN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TXN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TXN$AI».fns_eq]
theorem «FN2-CNS-TXN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TXN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TXN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TXN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TXN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TXN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TXN».fns_eq]
theorem «FN2-CNS-TXN-GEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TXN-GEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TXN-GEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TXN-GEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TXN-GEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TXN-GEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TXN-GEN$AI».fns_eq]
theorem «FN2-CNS-TXN-GEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TXN-GEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TXN-GEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TXN-GEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TXN-GEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TXN-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TXN-GEN».fns_eq]
theorem «FN2-CNS-TX-SLOT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TX-SLOT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TX-SLOT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TX-SLOT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TX-SLOT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TX-SLOT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TX-SLOT$AI».fns_eq]
theorem «FN2-CNS-TX-SLOT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TX-SLOT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TX-SLOT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TX-SLOT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TX-SLOT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TX-SLOT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TX-SLOT».fns_eq]
theorem «FN2-CNS-TX-GEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TX-GEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TX-GEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TX-GEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TX-GEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TX-GEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TX-GEN$AI».fns_eq]
theorem «FN2-CNS-TX-GEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-TX-GEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-TX-GEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-TX-GEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-TX-GEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-TX-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-TX-GEN».fns_eq]
theorem «FN2-CNS-UPLOAD$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-UPLOAD$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-UPLOAD$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-UPLOAD$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-UPLOAD$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-UPLOAD$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-UPLOAD$AI».fns_eq]
theorem «FN2-CNS-UPLOAD».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-UPLOAD" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-UPLOAD" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-UPLOAD» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-UPLOAD" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-UPLOAD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-UPLOAD».fns_eq]
theorem «FN2-CNS-UPLOAD-GEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-UPLOAD-GEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-UPLOAD-GEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-UPLOAD-GEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-UPLOAD-GEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-UPLOAD-GEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-UPLOAD-GEN$AI».fns_eq]
theorem «FN2-CNS-UPLOAD-GEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-UPLOAD-GEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-UPLOAD-GEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-UPLOAD-GEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-UPLOAD-GEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-UPLOAD-GEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-UPLOAD-GEN».fns_eq]
theorem «FN2-CNS-FSTART$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FSTART$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FSTART$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FSTART$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FSTART$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FSTART$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FSTART$AI».fns_eq]
theorem «FN2-CNS-FSTART».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FSTART" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FSTART" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FSTART» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FSTART" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FSTART" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FSTART».fns_eq]
theorem «UPDATE-FN2-CNS-FSTART$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-FSTART$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-FSTART$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FSTART$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-FSTART$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FSTART$AI».fns_eq]
theorem «FN2-CNS-SET-FSTART».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-FSTART" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-FSTART" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FSTART» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-FSTART" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-FSTART" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FSTART».fns_eq]
theorem «FN2-CNS-FED$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FED$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FED$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FED$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FED$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FED$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FED$AI».fns_eq]
theorem «FN2-CNS-FED».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FED" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FED" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FED» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FED" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FED" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FED».fns_eq]
theorem «UPDATE-FN2-CNS-FED$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-FED$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-FED$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FED$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-FED$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FED$AI».fns_eq]
theorem «FN2-CNS-SET-FED».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-FED" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-FED" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FED» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-FED" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-FED" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FED».fns_eq]
theorem «FN2-CNS-FEED-MODE$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FEED-MODE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FEED-MODE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FEED-MODE$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FEED-MODE$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FEED-MODE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FEED-MODE$AI».fns_eq]
theorem «FN2-CNS-FEED-MODE».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FEED-MODE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FEED-MODE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FEED-MODE» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FEED-MODE" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FEED-MODE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FEED-MODE».fns_eq]
theorem «UPDATE-FN2-CNS-FEED-MODE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-FEED-MODE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-FEED-MODE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FEED-MODE$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-FEED-MODE$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FEED-MODE$AI».fns_eq]
theorem «FN2-CNS-SET-FEED-MODE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-FEED-MODE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-FEED-MODE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FEED-MODE» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-FEED-MODE" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-FEED-MODE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FEED-MODE».fns_eq]
theorem «FN2-CNS-FEED-DISCARD$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FEED-DISCARD$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FEED-DISCARD$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FEED-DISCARD$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FEED-DISCARD$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FEED-DISCARD$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FEED-DISCARD$AI».fns_eq]
theorem «FN2-CNS-FEED-DISCARD».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-FEED-DISCARD" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-FEED-DISCARD" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-FEED-DISCARD» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-FEED-DISCARD" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-FEED-DISCARD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-FEED-DISCARD».fns_eq]
theorem «UPDATE-FN2-CNS-FEED-DISCARD$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-FEED-DISCARD$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-FEED-DISCARD$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FEED-DISCARD$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-FEED-DISCARD$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-FEED-DISCARD$AI».fns_eq]
theorem «FN2-CNS-SET-FEED-DISCARD».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-FEED-DISCARD" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-FEED-DISCARD" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FEED-DISCARD» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-FEED-DISCARD" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-FEED-DISCARD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-FEED-DISCARD».fns_eq]
theorem «FN2-CNS-NAME-OFF$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-NAME-OFF$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-NAME-OFF$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-NAME-OFF$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-NAME-OFF$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-NAME-OFF$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-NAME-OFF$AI».fns_eq]
theorem «FN2-CNS-NAME-OFF».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-NAME-OFF" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-NAME-OFF" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-NAME-OFF» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-NAME-OFF" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-NAME-OFF" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-NAME-OFF».fns_eq]
theorem «UPDATE-FN2-CNS-NAME-OFF$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-NAME-OFF$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-NAME-OFF$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-NAME-OFF$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-NAME-OFF$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-NAME-OFF$AI».fns_eq]
theorem «FN2-CNS-SET-NAME-OFF».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-NAME-OFF" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-NAME-OFF" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NAME-OFF» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-NAME-OFF" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-NAME-OFF" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NAME-OFF».fns_eq]
theorem «FN2-CNS-NAME-LEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-NAME-LEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-NAME-LEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-NAME-LEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-NAME-LEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-NAME-LEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-NAME-LEN$AI».fns_eq]
theorem «FN2-CNS-NAME-LEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-NAME-LEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-NAME-LEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-NAME-LEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-NAME-LEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-NAME-LEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-NAME-LEN».fns_eq]
theorem «UPDATE-FN2-CNS-NAME-LEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-NAME-LEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-NAME-LEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-NAME-LEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-NAME-LEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-NAME-LEN$AI».fns_eq]
theorem «FN2-CNS-SET-NAME-LEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-NAME-LEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-NAME-LEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NAME-LEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-NAME-LEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-NAME-LEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NAME-LEN».fns_eq]
theorem «FN2-CNS-XSTEP$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-XSTEP$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-XSTEP$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-XSTEP$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-XSTEP$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-XSTEP$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-XSTEP$AI».fns_eq]
theorem «FN2-CNS-XSTEP».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-XSTEP" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-XSTEP" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-XSTEP» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-XSTEP" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-XSTEP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-XSTEP».fns_eq]
theorem «UPDATE-FN2-CNS-XSTEP$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-XSTEP$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-XSTEP$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-XSTEP$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-XSTEP$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-XSTEP$AI».fns_eq]
theorem «FN2-CNS-SET-XSTEP».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-XSTEP" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-XSTEP" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XSTEP» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-XSTEP" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-XSTEP" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XSTEP».fns_eq]
theorem «FN2-CNS-XHEAD$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-XHEAD$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-XHEAD$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-XHEAD$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-XHEAD$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-XHEAD$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-XHEAD$AI».fns_eq]
theorem «FN2-CNS-XHEAD».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-XHEAD" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-XHEAD" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-XHEAD» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-XHEAD" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-XHEAD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-XHEAD».fns_eq]
theorem «UPDATE-FN2-CNS-XHEAD$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-XHEAD$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-XHEAD$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-XHEAD$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-XHEAD$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-XHEAD$AI».fns_eq]
theorem «FN2-CNS-SET-XHEAD».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-XHEAD" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-XHEAD" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XHEAD» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-XHEAD" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-XHEAD" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XHEAD».fns_eq]
theorem «FN2-CNS-XGRANT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-XGRANT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-XGRANT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-XGRANT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-XGRANT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-XGRANT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-XGRANT$AI».fns_eq]
theorem «FN2-CNS-XGRANT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-XGRANT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-XGRANT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-XGRANT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-XGRANT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-XGRANT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-XGRANT».fns_eq]
theorem «UPDATE-FN2-CNS-XGRANT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-XGRANT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-XGRANT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-XGRANT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-XGRANT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-XGRANT$AI».fns_eq]
theorem «FN2-CNS-SET-XGRANT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-XGRANT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-XGRANT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XGRANT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-XGRANT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-XGRANT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XGRANT».fns_eq]
theorem «FN2-CNS-IPOS$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-IPOS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-IPOS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-IPOS$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-IPOS$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-IPOS$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-IPOS$AI».fns_eq]
theorem «FN2-CNS-IPOS».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-IPOS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-IPOS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-IPOS» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-IPOS" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-IPOS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-IPOS».fns_eq]
theorem «UPDATE-FN2-CNS-IPOS$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-IPOS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-IPOS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-IPOS$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-IPOS$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-IPOS$AI».fns_eq]
theorem «FN2-CNS-SET-IPOS».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-IPOS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-IPOS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-IPOS» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-IPOS" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-IPOS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-IPOS».fns_eq]
theorem «FN2-CNS-IOFF$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-IOFF$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-IOFF$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-IOFF$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-IOFF$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-IOFF$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-IOFF$AI».fns_eq]
theorem «FN2-CNS-IOFF».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-IOFF" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-IOFF" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-IOFF» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-IOFF" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-IOFF" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-IOFF».fns_eq]
theorem «UPDATE-FN2-CNS-IOFF$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-IOFF$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-IOFF$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-IOFF$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-IOFF$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-IOFF$AI».fns_eq]
theorem «FN2-CNS-SET-IOFF».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-IOFF" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-IOFF" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-IOFF» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-IOFF" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-IOFF" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-IOFF».fns_eq]
theorem «FN2-CNS-ILEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ILEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ILEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ILEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ILEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ILEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ILEN$AI».fns_eq]
theorem «FN2-CNS-ILEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ILEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ILEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ILEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ILEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ILEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ILEN».fns_eq]
theorem «UPDATE-FN2-CNS-ILEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-ILEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-ILEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ILEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-ILEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ILEN$AI».fns_eq]
theorem «FN2-CNS-SET-ILEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-ILEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-ILEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ILEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-ILEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-ILEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ILEN».fns_eq]
theorem «FN2-CNS-NPOS$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-NPOS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-NPOS$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-NPOS$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-NPOS$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-NPOS$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-NPOS$AI».fns_eq]
theorem «FN2-CNS-NPOS».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-NPOS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-NPOS" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-NPOS» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-NPOS" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-NPOS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-NPOS».fns_eq]
theorem «UPDATE-FN2-CNS-NPOS$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-NPOS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-NPOS$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-NPOS$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-NPOS$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-NPOS$AI».fns_eq]
theorem «FN2-CNS-SET-NPOS».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-NPOS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-NPOS" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NPOS» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-NPOS" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-NPOS" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-NPOS».fns_eq]
theorem «FN2-CNS-ART$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ART$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ART$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ART$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ART$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ART$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ART$AI».fns_eq]
theorem «FN2-CNS-ART».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ART" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ART" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ART» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ART" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ART" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ART».fns_eq]
theorem «UPDATE-FN2-CNS-ART$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-ART$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-ART$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ART$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-ART$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ART$AI».fns_eq]
theorem «FN2-CNS-SET-ART».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-ART" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-ART" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ART» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-ART" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-ART" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ART».fns_eq]
theorem «FN2-CNS-ISTREAM$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ISTREAM$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ISTREAM$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ISTREAM$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ISTREAM$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ISTREAM$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ISTREAM$AI».fns_eq]
theorem «FN2-CNS-ISTREAM».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ISTREAM" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ISTREAM" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ISTREAM» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ISTREAM" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ISTREAM" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ISTREAM».fns_eq]
theorem «UPDATE-FN2-CNS-ISTREAM$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-ISTREAM$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-ISTREAM$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ISTREAM$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-ISTREAM$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ISTREAM$AI».fns_eq]
theorem «FN2-CNS-SET-ISTREAM».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-ISTREAM" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-ISTREAM" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ISTREAM» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-ISTREAM" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-ISTREAM" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ISTREAM».fns_eq]
theorem «FN2-CNS-ITYPE$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ITYPE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ITYPE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ITYPE$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ITYPE$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ITYPE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ITYPE$AI».fns_eq]
theorem «FN2-CNS-ITYPE».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ITYPE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ITYPE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ITYPE» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ITYPE" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ITYPE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ITYPE».fns_eq]
theorem «UPDATE-FN2-CNS-ITYPE$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-ITYPE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-ITYPE$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ITYPE$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-ITYPE$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ITYPE$AI».fns_eq]
theorem «FN2-CNS-SET-ITYPE».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-ITYPE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-ITYPE" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ITYPE» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-ITYPE" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-ITYPE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ITYPE».fns_eq]
theorem «FN2-CNS-ALEN$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ALEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ALEN$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ALEN$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ALEN$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ALEN$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ALEN$AI».fns_eq]
theorem «FN2-CNS-ALEN».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ALEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ALEN" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ALEN» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ALEN" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ALEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ALEN».fns_eq]
theorem «UPDATE-FN2-CNS-ALEN$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-ALEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-ALEN$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ALEN$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-ALEN$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-ALEN$AI».fns_eq]
theorem «FN2-CNS-SET-ALEN».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-ALEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-ALEN" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ALEN» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-ALEN" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-ALEN" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-ALEN».fns_eq]
theorem «FN2-CNS-LUNIT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LUNIT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LUNIT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LUNIT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LUNIT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LUNIT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LUNIT$AI».fns_eq]
theorem «FN2-CNS-LUNIT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LUNIT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LUNIT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LUNIT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LUNIT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LUNIT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LUNIT».fns_eq]
theorem «UPDATE-FN2-CNS-LUNIT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-LUNIT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-LUNIT$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LUNIT$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-LUNIT$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LUNIT$AI».fns_eq]
theorem «FN2-CNS-SET-LUNIT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-LUNIT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-LUNIT" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LUNIT» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-LUNIT" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-LUNIT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LUNIT».fns_eq]
theorem «FN2-CNS-LEPOCH$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LEPOCH$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LEPOCH$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LEPOCH$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LEPOCH$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LEPOCH$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LEPOCH$AI».fns_eq]
theorem «FN2-CNS-LEPOCH».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LEPOCH" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LEPOCH" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LEPOCH» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LEPOCH" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LEPOCH" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LEPOCH».fns_eq]
theorem «UPDATE-FN2-CNS-LEPOCH$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-LEPOCH$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-LEPOCH$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LEPOCH$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-LEPOCH$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LEPOCH$AI».fns_eq]
theorem «FN2-CNS-SET-LEPOCH».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-LEPOCH" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-LEPOCH" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LEPOCH» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-LEPOCH" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-LEPOCH" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LEPOCH».fns_eq]
theorem «FN2-CNS-LALLOC$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LALLOC$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LALLOC$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LALLOC$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LALLOC$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LALLOC$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LALLOC$AI».fns_eq]
theorem «FN2-CNS-LALLOC».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-LALLOC" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-LALLOC" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-LALLOC» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-LALLOC" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-LALLOC" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-LALLOC».fns_eq]
theorem «UPDATE-FN2-CNS-LALLOC$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-LALLOC$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-LALLOC$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LALLOC$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-LALLOC$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-LALLOC$AI».fns_eq]
theorem «FN2-CNS-SET-LALLOC».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-LALLOC" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-LALLOC" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LALLOC» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-LALLOC" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-LALLOC" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-LALLOC».fns_eq]
theorem «FN2-CNS-REVENT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-REVENT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-REVENT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-REVENT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-REVENT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-REVENT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-REVENT$AI».fns_eq]
theorem «FN2-CNS-REVENT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-REVENT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-REVENT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-REVENT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-REVENT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-REVENT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-REVENT».fns_eq]
theorem «FN2-CNS-ROUTCOME$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ROUTCOME$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ROUTCOME$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ROUTCOME$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ROUTCOME$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ROUTCOME$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ROUTCOME$AI».fns_eq]
theorem «FN2-CNS-ROUTCOME».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-ROUTCOME" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-ROUTCOME" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-ROUTCOME» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-ROUTCOME" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-ROUTCOME" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-ROUTCOME».fns_eq]
theorem «FN2-CNS-RCOUNT$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-RCOUNT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-RCOUNT$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-RCOUNT$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-RCOUNT$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-RCOUNT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-RCOUNT$AI».fns_eq]
theorem «FN2-CNS-RCOUNT».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-RCOUNT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-RCOUNT" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-RCOUNT» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-RCOUNT" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-RCOUNT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-RCOUNT».fns_eq]
theorem «FN2-CNS-RREADY$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-RREADY$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-RREADY$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-RREADY$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-RREADY$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-RREADY$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-RREADY$AI».fns_eq]
theorem «FN2-CNS-RREADY».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-RREADY" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-RREADY" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-RREADY» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-RREADY" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-RREADY" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-RREADY».fns_eq]
theorem «FN2-CNS-PENDING$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PENDING$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PENDING$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PENDING$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PENDING$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PENDING$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PENDING$AI».fns_eq]
theorem «FN2-CNS-PENDING».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-PENDING" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-PENDING" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-PENDING» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-PENDING" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-PENDING" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-PENDING».fns_eq]
theorem «UPDATE-FN2-CNS-PENDING$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-PENDING$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-PENDING$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PENDING$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-PENDING$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-PENDING$AI».fns_eq]
theorem «FN2-CNS-SET-PENDING».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-PENDING" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-PENDING" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PENDING» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-PENDING" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-PENDING" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-PENDING».fns_eq]
theorem «FN2-CNS-CURSOR$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CURSOR$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CURSOR$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CURSOR$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CURSOR$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CURSOR$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CURSOR$AI».fns_eq]
theorem «FN2-CNS-CURSOR».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-CURSOR" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-CURSOR" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-CURSOR» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-CURSOR" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-CURSOR" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-CURSOR».fns_eq]
theorem «UPDATE-FN2-CNS-CURSOR$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-CURSOR$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-CURSOR$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CURSOR$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-CURSOR$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-CURSOR$AI».fns_eq]
theorem «FN2-CNS-SET-CURSOR».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-CURSOR" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-CURSOR" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CURSOR» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-CURSOR" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-CURSOR" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-CURSOR».fns_eq]
theorem «FN2-CNS-XROW$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-XROW$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-XROW$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-XROW$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-XROW$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-XROW$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-XROW$AI».fns_eq]
theorem «FN2-CNS-XROW».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-XROW" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-XROW" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-XROW» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-XROW" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-XROW" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-XROW».fns_eq]
theorem «UPDATE-FN2-CNS-XROW$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-XROW$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-XROW$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-XROW$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-XROW$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-XROW$AI».fns_eq]
theorem «FN2-CNS-SET-XROW».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-XROW" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-XROW" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XROW» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-XROW" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-XROW" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-XROW».fns_eq]
theorem «FN2-CNS-STOPPED$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-STOPPED$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-STOPPED$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-STOPPED$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-STOPPED$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-STOPPED$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-STOPPED$AI».fns_eq]
theorem «FN2-CNS-STOPPED».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-STOPPED" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-STOPPED" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-STOPPED» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-STOPPED" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-STOPPED" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-STOPPED».fns_eq]
theorem «UPDATE-FN2-CNS-STOPPED$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "UPDATE-FN2-CNS-STOPPED$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-CNS-STOPPED$AI" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-STOPPED$AI» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "UPDATE-FN2-CNS-STOPPED$AI" [«I», «V», «FN2-CNS»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-CNS-STOPPED$AI».fns_eq]
theorem «FN2-CNS-SET-STOPPED».dispatched {err : String} («I» : Val) («V» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-SET-STOPPED" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-SET-STOPPED" [«I», «V», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-SET-STOPPED» «I» «V» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-SET-STOPPED" [«I», «V», «FN2-CNS»] (fn2_not_native "FN2-CNS-SET-STOPPED" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-SET-STOPPED».fns_eq]
theorem «FN2-CNS-NEXT-FREE$AI».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-NEXT-FREE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-NEXT-FREE$AI" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-NEXT-FREE$AI» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-NEXT-FREE$AI" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-NEXT-FREE$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-NEXT-FREE$AI».fns_eq]
theorem «FN2-CNS-NEXT-FREE».dispatched {err : String} («I» : Val) («FN2-CNS» : Val) :
    (match nativeCall "FN2-CNS-NEXT-FREE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => match fns "FN2-CNS-NEXT-FREE" [«I», «FN2-CNS»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-CNS-NEXT-FREE» «I» «FN2-CNS») := by
  simp only [nativeCall_none "FN2-CNS-NEXT-FREE" [«I», «FN2-CNS»] (fn2_not_native "FN2-CNS-NEXT-FREE" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-CNS-NEXT-FREE».fns_eq]
theorem «FN2-MACHINES-READY-PREV$AI».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-READY-PREV$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-READY-PREV$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-READY-PREV$AI» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-READY-PREV$AI" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-READY-PREV$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-READY-PREV$AI».fns_eq]
theorem «FN2-MACHINES-READY-PREV».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-READY-PREV" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-READY-PREV" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-READY-PREV» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-READY-PREV" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-READY-PREV" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-READY-PREV».fns_eq]
theorem «UPDATE-FN2-MACHINES-READY-PREV$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "UPDATE-FN2-MACHINES-READY-PREV$AI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-MACHINES-READY-PREV$AI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-READY-PREV$AI» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "UPDATE-FN2-MACHINES-READY-PREV$AI" [«I», «V», «FN2-MACHINES»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-READY-PREV$AI».fns_eq]
theorem «FN2-MACHINES-SET-READY-PREV».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-SET-READY-PREV" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-SET-READY-PREV" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-SET-READY-PREV» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-SET-READY-PREV" [«I», «V», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-SET-READY-PREV" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-SET-READY-PREV».fns_eq]
theorem «FN2-MACHINES-READY-NEXT$AI».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-READY-NEXT$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-READY-NEXT$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-READY-NEXT$AI» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-READY-NEXT$AI" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-READY-NEXT$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-READY-NEXT$AI».fns_eq]
theorem «FN2-MACHINES-READY-NEXT».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-READY-NEXT" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-READY-NEXT" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-READY-NEXT» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-READY-NEXT" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-READY-NEXT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-READY-NEXT».fns_eq]
theorem «UPDATE-FN2-MACHINES-READY-NEXT$AI».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "UPDATE-FN2-MACHINES-READY-NEXT$AI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "UPDATE-FN2-MACHINES-READY-NEXT$AI" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-READY-NEXT$AI» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "UPDATE-FN2-MACHINES-READY-NEXT$AI" [«I», «V», «FN2-MACHINES»] (by decide +kernel), fns, Fn2.Instances.LayerAWorld.«UPDATE-FN2-MACHINES-READY-NEXT$AI».fns_eq]
theorem «FN2-MACHINES-SET-READY-NEXT».dispatched {err : String} («I» : Val) («V» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-SET-READY-NEXT" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-SET-READY-NEXT" [«I», «V», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-SET-READY-NEXT» «I» «V» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-SET-READY-NEXT" [«I», «V», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-SET-READY-NEXT" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-SET-READY-NEXT».fns_eq]
theorem «FN2-MACHINES-WAIT-REASON$AI».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-WAIT-REASON$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-WAIT-REASON$AI" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-WAIT-REASON$AI» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-WAIT-REASON$AI" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-WAIT-REASON$AI" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-WAIT-REASON$AI».fns_eq]
theorem «FN2-MACHINES-WAIT-REASON».dispatched {err : String} («I» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-WAIT-REASON" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-WAIT-REASON" [«I», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-WAIT-REASON» «I» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-WAIT-REASON" [«I», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-WAIT-REASON" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-WAIT-REASON».fns_eq]
theorem «FN2-MACHINES-FREE-HEAD-OF».dispatched {err : String} («ORD» : Val) («FN2-MACHINES» : Val) :
    (match nativeCall "FN2-MACHINES-FREE-HEAD-OF" [«ORD», «FN2-MACHINES»] with | some x => Except.ok x | none => match fns "FN2-MACHINES-FREE-HEAD-OF" [«ORD», «FN2-MACHINES»] with | some x => Except.ok x | none => Except.error err) = .ok (Fn2.Instances.LayerAWorld.«FN2-MACHINES-FREE-HEAD-OF» «ORD» «FN2-MACHINES») := by
  simp only [nativeCall_none "FN2-MACHINES-FREE-HEAD-OF" [«ORD», «FN2-MACHINES»] (fn2_not_native "FN2-MACHINES-FREE-HEAD-OF" (by decide +kernel)), fns, Fn2.Instances.LayerAWorld.«FN2-MACHINES-FREE-HEAD-OF».fns_eq]
end Fn2.Instances.CoreWorld
