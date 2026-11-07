-- Generated body equations; the kernel checks every equation.
import Fn2.Instances.BridgeWorld
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace Fn2.Instances.BridgeWorld
open Fn2.ACL2
def «FN2-CORE-CONTROL».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (5)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CORE-CONTROL».body : Term := (.app "NTH" [(.quote (Val.int 5)), (.var "FN2-CORE")])
theorem «FN2-CORE-CONTROL».decoded : Translation.readTerm 512 «FN2-CORE-CONTROL».canonicalBody = some «FN2-CORE-CONTROL».body := by rfl
theorem «FN2-CORE-CONTROL».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-CORE-CONTROL».body 512 = .ok («FN2-CORE-CONTROL» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 5)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 5), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CORE-CONTROL».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-CORE-CONTROL».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-CORE-CONTROL» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-CORE-CONTROL».decoded]
  exact «FN2-CORE-CONTROL».export_body «FN2-CORE»

def «UPDATE-FN2-CONTROL-STOP».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [85, 80, 68, 65, 84, 69, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (4)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [86]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «UPDATE-FN2-CONTROL-STOP».body : Term := (.app "UPDATE-NTH" [(.quote (Val.int 4)), (.var "V"), (.var "FN2-CONTROL")])
theorem «UPDATE-FN2-CONTROL-STOP».decoded : Translation.readTerm 512 «UPDATE-FN2-CONTROL-STOP».canonicalBody = some «UPDATE-FN2-CONTROL-STOP».body := by rfl
theorem «UPDATE-FN2-CONTROL-STOP».export_body («V» : Val) («FN2-CONTROL» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("V", «V»), ("FN2-CONTROL", «FN2-CONTROL»)] «UPDATE-FN2-CONTROL-STOP».body 512 = .ok («UPDATE-FN2-CONTROL-STOP» «V» «FN2-CONTROL») := by
  change Translation.eval fns [("V", «V»), ("FN2-CONTROL", «FN2-CONTROL»)] (.app "UPDATE-NTH" [(.quote (Val.int 4)), (.var "V"), (.var "FN2-CONTROL")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 4), «V», «FN2-CONTROL»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
theorem «UPDATE-FN2-CONTROL-STOP».canonical_body («V» : Val) («FN2-CONTROL» : Val) :
    Translation.evalExport 512 «UPDATE-FN2-CONTROL-STOP».canonicalBody fns [("V", «V»), ("FN2-CONTROL", «FN2-CONTROL»)] = .ok («UPDATE-FN2-CONTROL-STOP» «V» «FN2-CONTROL») := by
  simp only [Translation.evalExport, «UPDATE-FN2-CONTROL-STOP».decoded]
  exact «UPDATE-FN2-CONTROL-STOP».export_body «V» «FN2-CONTROL»

def «UPDATE-FN2-CONTROL-STOP-REASON».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [85, 80, 68, 65, 84, 69, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (5)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [86]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «UPDATE-FN2-CONTROL-STOP-REASON».body : Term := (.app "UPDATE-NTH" [(.quote (Val.int 5)), (.var "V"), (.var "FN2-CONTROL")])
theorem «UPDATE-FN2-CONTROL-STOP-REASON».decoded : Translation.readTerm 512 «UPDATE-FN2-CONTROL-STOP-REASON».canonicalBody = some «UPDATE-FN2-CONTROL-STOP-REASON».body := by rfl
theorem «UPDATE-FN2-CONTROL-STOP-REASON».export_body («V» : Val) («FN2-CONTROL» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("V", «V»), ("FN2-CONTROL", «FN2-CONTROL»)] «UPDATE-FN2-CONTROL-STOP-REASON».body 512 = .ok («UPDATE-FN2-CONTROL-STOP-REASON» «V» «FN2-CONTROL») := by
  change Translation.eval fns [("V", «V»), ("FN2-CONTROL", «FN2-CONTROL»)] (.app "UPDATE-NTH" [(.quote (Val.int 5)), (.var "V"), (.var "FN2-CONTROL")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 5), «V», «FN2-CONTROL»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
theorem «UPDATE-FN2-CONTROL-STOP-REASON».canonical_body («V» : Val) («FN2-CONTROL» : Val) :
    Translation.evalExport 512 «UPDATE-FN2-CONTROL-STOP-REASON».canonicalBody fns [("V", «V»), ("FN2-CONTROL", «FN2-CONTROL»)] = .ok («UPDATE-FN2-CONTROL-STOP-REASON» «V» «FN2-CONTROL») := by
  simp only [Translation.evalExport, «UPDATE-FN2-CONTROL-STOP-REASON».decoded]
  exact «UPDATE-FN2-CONTROL-STOP-REASON».export_body «V» «FN2-CONTROL»

def «FN2-CONTROL-STOP».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (4)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CONTROL-STOP».body : Term := (.app "NTH" [(.quote (Val.int 4)), (.var "FN2-CONTROL")])
theorem «FN2-CONTROL-STOP».decoded : Translation.readTerm 512 «FN2-CONTROL-STOP».canonicalBody = some «FN2-CONTROL-STOP».body := by rfl
theorem «FN2-CONTROL-STOP».export_body («FN2-CONTROL» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CONTROL", «FN2-CONTROL»)] «FN2-CONTROL-STOP».body 512 = .ok («FN2-CONTROL-STOP» «FN2-CONTROL») := by
  change Translation.eval fns [("FN2-CONTROL", «FN2-CONTROL»)] (.app "NTH" [(.quote (Val.int 4)), (.var "FN2-CONTROL")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 4), «FN2-CONTROL»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CONTROL-STOP».canonical_body («FN2-CONTROL» : Val) :
    Translation.evalExport 512 «FN2-CONTROL-STOP».canonicalBody fns [("FN2-CONTROL", «FN2-CONTROL»)] = .ok («FN2-CONTROL-STOP» «FN2-CONTROL») := by
  simp only [Translation.evalExport, «FN2-CONTROL-STOP».decoded]
  exact «FN2-CONTROL-STOP».export_body «FN2-CONTROL»

def «=».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 85, 65, 76]) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.symbol [65, 67, 76, 50] [89]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «=».body : Term := (.app "EQUAL" [(.var "X"), (.var "Y")])
theorem «=».decoded : Translation.readTerm 512 «=».canonicalBody = some «=».body := by rfl
theorem «=».export_body («X» : Val) («Y» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("X", «X»), ("Y", «Y»)] «=».body 512 = .ok («=» «X» «Y») := by
  change Translation.eval fns [("X", «X»), ("Y", «Y»)] (.app "EQUAL" [(.var "X"), (.var "Y")]) 512 = _
  refine Translation.eval_app (vs := [«X», «Y»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «=».canonical_body («X» : Val) («Y» : Val) :
    Translation.evalExport 512 «=».canonicalBody fns [("X", «X»), ("Y", «Y»)] = .ok («=» «X» «Y») := by
  simp only [Translation.evalExport, «=».decoded]
  exact «=».export_body «X» «Y»

def «FN2-CONTROL-RECORD-STOP».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [61]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76, 45, 83, 84, 79, 80]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [82, 69, 65, 83, 79, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [85, 80, 68, 65, 84, 69, 45, 70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76, 45, 83, 84, 79, 80, 45, 82, 69, 65, 83, 79, 78]) (.cons (.symbol [65, 67, 76, 50] [82, 69, 65, 83, 79, 78]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [85, 80, 68, 65, 84, 69, 45, 70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76, 45, 83, 84, 79, 80]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [82, 69, 65, 83, 79, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-CONTROL-RECORD-STOP».body : Term := (.app "IF" [(.app "=" [(.app "FN2-CONTROL-STOP" [(.var "FN2-CONTROL")]), (.quote (Val.int 1))]), (.var "FN2-CONTROL"), (.lam ["FN2-CONTROL", "REASON"] (.lam ["FN2-CONTROL"] (.var "FN2-CONTROL") [(.app "UPDATE-FN2-CONTROL-STOP-REASON" [(.var "REASON"), (.var "FN2-CONTROL")])]) [(.app "UPDATE-FN2-CONTROL-STOP" [(.quote (Val.int 1)), (.var "FN2-CONTROL")]), (.var "REASON")])])
theorem «FN2-CONTROL-RECORD-STOP».decoded : Translation.readTerm 512 «FN2-CONTROL-RECORD-STOP».canonicalBody = some «FN2-CONTROL-RECORD-STOP».body := by rfl
theorem «FN2-CONTROL-RECORD-STOP».export_body («REASON» : Val) («FN2-CONTROL» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("REASON", «REASON»), ("FN2-CONTROL", «FN2-CONTROL»)] «FN2-CONTROL-RECORD-STOP».body 512 = .ok («FN2-CONTROL-RECORD-STOP» «REASON» «FN2-CONTROL») := by
  change Translation.eval fns [("REASON", «REASON»), ("FN2-CONTROL", «FN2-CONTROL»)] (.app "IF" [(.app "=" [(.app "FN2-CONTROL-STOP" [(.var "FN2-CONTROL")]), (.quote (Val.int 1))]), (.var "FN2-CONTROL"), (.lam ["FN2-CONTROL", "REASON"] (.lam ["FN2-CONTROL"] (.var "FN2-CONTROL") [(.app "UPDATE-FN2-CONTROL-STOP-REASON" [(.var "REASON"), (.var "FN2-CONTROL")])]) [(.app "UPDATE-FN2-CONTROL-STOP" [(.quote (Val.int 1)), (.var "FN2-CONTROL")]), (.var "REASON")])]) 512 = _
  refine Translation.eval_if (vc := («=» («FN2-CONTROL-STOP» «FN2-CONTROL») (Val.int 1))) (va := «FN2-CONTROL») (vb := («UPDATE-FN2-CONTROL-STOP-REASON» «REASON» («UPDATE-FN2-CONTROL-STOP» (Val.int 1) «FN2-CONTROL»))) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [(«FN2-CONTROL-STOP» «FN2-CONTROL»), (Val.int 1)]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«FN2-CONTROL»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
  ·
    rfl
  ·
    refine Translation.eval_lam (vs := [(«UPDATE-FN2-CONTROL-STOP» (Val.int 1) «FN2-CONTROL»), «REASON»]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 1), «FN2-CONTROL»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
    ·
      refine Translation.eval_lam (vs := [(«UPDATE-FN2-CONTROL-STOP-REASON» «REASON» («UPDATE-FN2-CONTROL-STOP» (Val.int 1) «FN2-CONTROL»))]) ?_ ?_
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [«REASON», («UPDATE-FN2-CONTROL-STOP» (Val.int 1) «FN2-CONTROL»)]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          rfl
      ·
        rfl
theorem «FN2-CONTROL-RECORD-STOP».canonical_body («REASON» : Val) («FN2-CONTROL» : Val) :
    Translation.evalExport 512 «FN2-CONTROL-RECORD-STOP».canonicalBody fns [("REASON", «REASON»), ("FN2-CONTROL", «FN2-CONTROL»)] = .ok («FN2-CONTROL-RECORD-STOP» «REASON» «FN2-CONTROL») := by
  simp only [Translation.evalExport, «FN2-CONTROL-RECORD-STOP».decoded]
  exact «FN2-CONTROL-RECORD-STOP».export_body «REASON» «FN2-CONTROL»

def «THROW-NONEXEC-ERROR».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))
def «THROW-NONEXEC-ERROR».body : Term := (.quote Val.nil)
theorem «THROW-NONEXEC-ERROR».decoded : Translation.readTerm 512 «THROW-NONEXEC-ERROR».canonicalBody = some «THROW-NONEXEC-ERROR».body := by rfl
theorem «THROW-NONEXEC-ERROR».export_body («FN» : Val) («ACTUALS» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN", «FN»), ("ACTUALS", «ACTUALS»)] «THROW-NONEXEC-ERROR».body 512 = .ok («THROW-NONEXEC-ERROR» «FN» «ACTUALS») := by
  change Translation.eval fns [("FN", «FN»), ("ACTUALS", «ACTUALS»)] (.quote Val.nil) 512 = _
  rfl
theorem «THROW-NONEXEC-ERROR».canonical_body («FN» : Val) («ACTUALS» : Val) :
    Translation.evalExport 512 «THROW-NONEXEC-ERROR».canonicalBody fns [("FN", «FN»), ("ACTUALS", «ACTUALS»)] = .ok («THROW-NONEXEC-ERROR» «FN» «ACTUALS») := by
  simp only [Translation.evalExport, «THROW-NONEXEC-ERROR».decoded]
  exact «THROW-NONEXEC-ERROR».export_body «FN» «ACTUALS»

def «UPDATE-FN2-CORE-CONTROL».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [82, 69, 84, 85, 82, 78, 45, 76, 65, 83, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [80, 82, 79, 71, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [65, 67, 76, 50] [84, 72, 82, 79, 87, 45, 78, 79, 78, 69, 88, 69, 67, 45, 69, 82, 82, 79, 82]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [78, 79, 78, 45, 69, 88, 69, 67]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.cons (.symbol [65, 67, 76, 50] [85, 80, 68, 65, 84, 69, 45, 78, 84, 72]) (.cons (.integer (5)) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [85, 80, 68, 65, 84, 69, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (5)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «UPDATE-FN2-CORE-CONTROL».body : Term := (.app "RETURN-LAST" [(.quote (Val.sym "PROGN")), (.app "THROW-NONEXEC-ERROR" [(.quote (Val.sym ":NON-EXEC")), (.quote (Val.ofList [(Val.sym "UPDATE-NTH"), (Val.int 5), (Val.sym "FN2-CONTROL"), (Val.sym "FN2-CORE")]))]), (.app "UPDATE-NTH" [(.quote (Val.int 5)), (.var "FN2-CONTROL"), (.var "FN2-CORE")])])
theorem «UPDATE-FN2-CORE-CONTROL».decoded : Translation.readTerm 512 «UPDATE-FN2-CORE-CONTROL».canonicalBody = some «UPDATE-FN2-CORE-CONTROL».body := by rfl
theorem «UPDATE-FN2-CORE-CONTROL».export_body («FN2-CONTROL» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CONTROL", «FN2-CONTROL»), ("FN2-CORE", «FN2-CORE»)] «UPDATE-FN2-CORE-CONTROL».body 512 = .ok («UPDATE-FN2-CORE-CONTROL» «FN2-CONTROL» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CONTROL", «FN2-CONTROL»), ("FN2-CORE", «FN2-CORE»)] (.app "RETURN-LAST" [(.quote (Val.sym "PROGN")), (.app "THROW-NONEXEC-ERROR" [(.quote (Val.sym ":NON-EXEC")), (.quote (Val.ofList [(Val.sym "UPDATE-NTH"), (Val.int 5), (Val.sym "FN2-CONTROL"), (Val.sym "FN2-CORE")]))]), (.app "UPDATE-NTH" [(.quote (Val.int 5)), (.var "FN2-CONTROL"), (.var "FN2-CORE")])]) 512 = _
  change Translation.eval _ _ (.app "UPDATE-NTH" [(.quote (Val.int 5)), (.var "FN2-CONTROL"), (.var "FN2-CORE")]) _ = _
  refine Translation.eval_app (vs := [(Val.int 5), «FN2-CONTROL», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
theorem «UPDATE-FN2-CORE-CONTROL».canonical_body («FN2-CONTROL» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «UPDATE-FN2-CORE-CONTROL».canonicalBody fns [("FN2-CONTROL", «FN2-CONTROL»), ("FN2-CORE", «FN2-CORE»)] = .ok («UPDATE-FN2-CORE-CONTROL» «FN2-CONTROL» «FN2-CORE») := by
  simp only [Translation.evalExport, «UPDATE-FN2-CORE-CONTROL».decoded]
  exact «UPDATE-FN2-CORE-CONTROL».export_body «FN2-CONTROL» «FN2-CORE»

def «FN2-CORE-STOP».canonicalBody : Translation.Object := (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [82, 69, 65, 83, 79, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [85, 80, 68, 65, 84, 69, 45, 70, 78, 50, 45, 67, 79, 82, 69, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76, 45, 82, 69, 67, 79, 82, 68, 45, 83, 84, 79, 80]) (.cons (.symbol [65, 67, 76, 50] [82, 69, 65, 83, 79, 78]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [82, 69, 65, 83, 79, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-CORE-STOP».body : Term := (.lam ["FN2-CONTROL", "FN2-CORE", "REASON"] (.lam ["FN2-CONTROL", "FN2-CORE"] (.lam ["FN2-CORE"] (.var "FN2-CORE") [(.app "UPDATE-FN2-CORE-CONTROL" [(.var "FN2-CONTROL"), (.var "FN2-CORE")])]) [(.app "FN2-CONTROL-RECORD-STOP" [(.var "REASON"), (.var "FN2-CONTROL")]), (.var "FN2-CORE")]) [(.app "FN2-CORE-CONTROL" [(.var "FN2-CORE")]), (.var "FN2-CORE"), (.var "REASON")])
theorem «FN2-CORE-STOP».decoded : Translation.readTerm 512 «FN2-CORE-STOP».canonicalBody = some «FN2-CORE-STOP».body := by rfl
theorem «FN2-CORE-STOP».export_body («REASON» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("REASON", «REASON»), ("FN2-CORE", «FN2-CORE»)] «FN2-CORE-STOP».body 512 = .ok («FN2-CORE-STOP» «REASON» «FN2-CORE») := by
  change Translation.eval fns [("REASON", «REASON»), ("FN2-CORE", «FN2-CORE»)] (.lam ["FN2-CONTROL", "FN2-CORE", "REASON"] (.lam ["FN2-CONTROL", "FN2-CORE"] (.lam ["FN2-CORE"] (.var "FN2-CORE") [(.app "UPDATE-FN2-CORE-CONTROL" [(.var "FN2-CONTROL"), (.var "FN2-CORE")])]) [(.app "FN2-CONTROL-RECORD-STOP" [(.var "REASON"), (.var "FN2-CONTROL")]), (.var "FN2-CORE")]) [(.app "FN2-CORE-CONTROL" [(.var "FN2-CORE")]), (.var "FN2-CORE"), (.var "REASON")]) 512 = _
  refine Translation.eval_lam (vs := [(«FN2-CORE-CONTROL» «FN2-CORE»), «FN2-CORE», «REASON»]) ?_ ?_
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
  ·
    refine Translation.eval_lam (vs := [(«FN2-CONTROL-RECORD-STOP» «REASON» («FN2-CORE-CONTROL» «FN2-CORE»)), «FN2-CORE»]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«REASON», («FN2-CORE-CONTROL» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
    ·
      refine Translation.eval_lam (vs := [(«UPDATE-FN2-CORE-CONTROL» («FN2-CONTROL-RECORD-STOP» «REASON» («FN2-CORE-CONTROL» «FN2-CORE»)) «FN2-CORE»)]) ?_ ?_
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [(«FN2-CONTROL-RECORD-STOP» «REASON» («FN2-CORE-CONTROL» «FN2-CORE»)), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          rfl
      ·
        rfl
theorem «FN2-CORE-STOP».canonical_body («REASON» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-CORE-STOP».canonicalBody fns [("REASON", «REASON»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-CORE-STOP» «REASON» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-CORE-STOP».decoded]
  exact «FN2-CORE-STOP».export_body «REASON» «FN2-CORE»

def «FN2-CORE-MACHINES».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (3)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CORE-MACHINES».body : Term := (.app "NTH" [(.quote (Val.int 3)), (.var "FN2-CORE")])
theorem «FN2-CORE-MACHINES».decoded : Translation.readTerm 512 «FN2-CORE-MACHINES».canonicalBody = some «FN2-CORE-MACHINES».body := by rfl
theorem «FN2-CORE-MACHINES».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-CORE-MACHINES».body 512 = .ok («FN2-CORE-MACHINES» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 3)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 3), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CORE-MACHINES».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-CORE-MACHINES».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-CORE-MACHINES» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-CORE-MACHINES».decoded]
  exact «FN2-CORE-MACHINES».export_body «FN2-CORE»

def «FN2-ECHO-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (7)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 7)), (.var "FN2-CORE")])
theorem «FN2-ECHO-TABLE».decoded : Translation.readTerm 512 «FN2-ECHO-TABLE».canonicalBody = some «FN2-ECHO-TABLE».body := by rfl
theorem «FN2-ECHO-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-ECHO-TABLE».body 512 = .ok («FN2-ECHO-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 7)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 7), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-ECHO-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-ECHO-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-ECHO-TABLE».decoded]
  exact «FN2-ECHO-TABLE».export_body «FN2-CORE»

def «FN2-MACHINES-SLOT$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-SLOT$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 1)), (.var "FN2-MACHINES")])])
theorem «FN2-MACHINES-SLOT$AI».decoded : Translation.readTerm 512 «FN2-MACHINES-SLOT$AI».canonicalBody = some «FN2-MACHINES-SLOT$AI».body := by rfl
theorem «FN2-MACHINES-SLOT$AI».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-SLOT$AI».body 512 = .ok («FN2-MACHINES-SLOT$AI» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 1)), (.var "FN2-MACHINES")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 1) «FN2-MACHINES»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 1), «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-MACHINES-SLOT$AI».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-SLOT$AI».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-SLOT$AI» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-SLOT$AI».decoded]
  exact «FN2-MACHINES-SLOT$AI».export_body «I» «FN2-MACHINES»

def «FN2-MACHINES-SLOT».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 83, 76, 79, 84, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-SLOT».body : Term := (.app "FN2-MACHINES-SLOT$AI" [(.var "I"), (.var "FN2-MACHINES")])
theorem «FN2-MACHINES-SLOT».decoded : Translation.readTerm 512 «FN2-MACHINES-SLOT».canonicalBody = some «FN2-MACHINES-SLOT».body := by rfl
theorem «FN2-MACHINES-SLOT».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-SLOT».body 512 = .ok («FN2-MACHINES-SLOT» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "FN2-MACHINES-SLOT$AI" [(.var "I"), (.var "FN2-MACHINES")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-MACHINES-SLOT».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-SLOT».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-SLOT» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-SLOT».decoded]
  exact «FN2-MACHINES-SLOT».export_body «I» «FN2-MACHINES»

def «FN2-ECHO-RUN-FREE-CHILDREN».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-RUN-FREE-CHILDREN».body : Term := (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote (Val.int 1)), (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote Val.nil), (.quote Val.nil)])])])])
theorem «FN2-ECHO-RUN-FREE-CHILDREN».decoded : Translation.readTerm 512 «FN2-ECHO-RUN-FREE-CHILDREN».canonicalBody = some «FN2-ECHO-RUN-FREE-CHILDREN».body := by rfl
theorem «FN2-ECHO-RUN-FREE-CHILDREN».export_body («ID» : Val) («SLOT» : Val) («KIND» : Val) («ORDINAL» : Val) («BUDGET» : Val) («FN2-ECHO» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("SLOT", «SLOT»), ("KIND", «KIND»), ("ORDINAL", «ORDINAL»), ("BUDGET", «BUDGET»), ("FN2-ECHO", «FN2-ECHO»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-ECHO-RUN-FREE-CHILDREN».body 512 = .ok («FN2-ECHO-RUN-FREE-CHILDREN» «ID» «SLOT» «KIND» «ORDINAL» «BUDGET» «FN2-ECHO» «FN2-MACHINES») := by
  change Translation.eval fns [("ID", «ID»), ("SLOT", «SLOT»), ("KIND", «KIND»), ("ORDINAL", «ORDINAL»), ("BUDGET", «BUDGET»), ("FN2-ECHO", «FN2-ECHO»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote (Val.int 1)), (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote Val.nil), (.quote Val.nil)])])])]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 0), (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil Val.nil)))]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 1), (Val.cons (Val.int 0) (Val.cons Val.nil Val.nil))]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [(Val.int 0), (Val.cons Val.nil Val.nil)]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    refine Translation.eval_app (vs := [Val.nil, Val.nil]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          rfl
                  ·
                    rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-RUN-FREE-CHILDREN».canonical_body («ID» : Val) («SLOT» : Val) («KIND» : Val) («ORDINAL» : Val) («BUDGET» : Val) («FN2-ECHO» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-ECHO-RUN-FREE-CHILDREN».canonicalBody fns [("ID", «ID»), ("SLOT", «SLOT»), ("KIND", «KIND»), ("ORDINAL", «ORDINAL»), ("BUDGET", «BUDGET»), ("FN2-ECHO", «FN2-ECHO»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-ECHO-RUN-FREE-CHILDREN» «ID» «SLOT» «KIND» «ORDINAL» «BUDGET» «FN2-ECHO» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-ECHO-RUN-FREE-CHILDREN».decoded]
  exact «FN2-ECHO-RUN-FREE-CHILDREN».export_body «ID» «SLOT» «KIND» «ORDINAL» «BUDGET» «FN2-ECHO» «FN2-MACHINES»

def «FN2-MACHINES-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (5)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 5)), (.var "FN2-MACHINES")])
theorem «FN2-MACHINES-ROWS».decoded : Translation.readTerm 512 «FN2-MACHINES-ROWS».canonicalBody = some «FN2-MACHINES-ROWS».body := by rfl
theorem «FN2-MACHINES-ROWS».export_body («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-ROWS».body 512 = .ok («FN2-MACHINES-ROWS» «FN2-MACHINES») := by
  change Translation.eval fns [("FN2-MACHINES", «FN2-MACHINES»)] (.app "NTH" [(.quote (Val.int 5)), (.var "FN2-MACHINES")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 5), «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-MACHINES-ROWS».canonical_body («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-ROWS».canonicalBody fns [("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-ROWS» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-ROWS».decoded]
  exact «FN2-MACHINES-ROWS».export_body «FN2-MACHINES»

def «FN2-ECHO-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (16)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 16)), (.var "FN2-ECHO")])
theorem «FN2-ECHO-ROWS».decoded : Translation.readTerm 512 «FN2-ECHO-ROWS».canonicalBody = some «FN2-ECHO-ROWS».body := by rfl
theorem «FN2-ECHO-ROWS».export_body («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-ROWS».body 512 = .ok («FN2-ECHO-ROWS» «FN2-ECHO») := by
  change Translation.eval fns [("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.quote (Val.int 16)), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 16), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-ROWS».canonical_body («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-ROWS».canonicalBody fns [("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-ROWS» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-ROWS».decoded]
  exact «FN2-ECHO-ROWS».export_body «FN2-ECHO»

def «NOT».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.symbol [65, 67, 76, 50] [80]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «NOT».body : Term := (.app "IF" [(.var "P"), (.quote Val.nil), (.quote Val.t)])
theorem «NOT».decoded : Translation.readTerm 512 «NOT».canonicalBody = some «NOT».body := by rfl
theorem «NOT».export_body («P» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("P", «P»)] «NOT».body 512 = .ok («NOT» «P») := by
  change Translation.eval fns [("P", «P»)] (.app "IF" [(.var "P"), (.quote Val.nil), (.quote Val.t)]) 512 = _
  refine Translation.eval_if (vc := «P») (va := Val.nil) (vb := Val.t) ?_ ?_ ?_
  ·
    rfl
  ·
    rfl
  ·
    rfl
theorem «NOT».canonical_body («P» : Val) :
    Translation.evalExport 512 «NOT».canonicalBody fns [("P", «P»)] = .ok («NOT» «P») := by
  simp only [Translation.evalExport, «NOT».decoded]
  exact «NOT».export_body «P»

def «NATP».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 78, 84, 69, 71, 69, 82, 80]) (.cons (.symbol [65, 67, 76, 50] [88]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «NATP».body : Term := (.app "IF" [(.app "INTEGERP" [(.var "X")]), (.app "NOT" [(.app "<" [(.var "X"), (.quote (Val.int 0))])]), (.quote Val.nil)])
theorem «NATP».decoded : Translation.readTerm 512 «NATP».canonicalBody = some «NATP».body := by rfl
theorem «NATP».export_body («X» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("X", «X»)] «NATP».body 512 = .ok («NATP» «X») := by
  change Translation.eval fns [("X", «X»)] (.app "IF" [(.app "INTEGERP" [(.var "X")]), (.app "NOT" [(.app "<" [(.var "X"), (.quote (Val.int 0))])]), (.quote Val.nil)]) 512 = _
  refine Translation.eval_if (vc := (Prim.integerp «X»)) (va := («NOT» (Prim.lt «X» (Val.int 0)))) (vb := Val.nil) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [«X»]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
  ·
    refine Translation.eval_app (vs := [(Prim.lt «X» (Val.int 0))]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«X», (Val.int 0)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
  ·
    rfl
theorem «NATP».canonical_body («X» : Val) :
    Translation.evalExport 512 «NATP».canonicalBody fns [("X", «X»)] = .ok («NATP» «X») := by
  simp only [Translation.evalExport, «NATP».decoded]
  exact «NATP».export_body «X»

def «HARD-ERROR».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))
def «HARD-ERROR».body : Term := (.quote Val.nil)
theorem «HARD-ERROR».decoded : Translation.readTerm 512 «HARD-ERROR».canonicalBody = some «HARD-ERROR».body := by rfl
theorem «HARD-ERROR».export_body («CTX» : Val) («STR» : Val) («ALIST» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("CTX", «CTX»), ("STR", «STR»), ("ALIST", «ALIST»)] «HARD-ERROR».body 512 = .ok («HARD-ERROR» «CTX» «STR» «ALIST») := by
  change Translation.eval fns [("CTX", «CTX»), ("STR", «STR»), ("ALIST", «ALIST»)] (.quote Val.nil) 512 = _
  rfl
theorem «HARD-ERROR».canonical_body («CTX» : Val) («STR» : Val) («ALIST» : Val) :
    Translation.evalExport 512 «HARD-ERROR».canonicalBody fns [("CTX", «CTX»), ("STR", «STR»), ("ALIST", «ALIST»)] = .ok («HARD-ERROR» «CTX» «STR» «ALIST») := by
  simp only [Translation.evalExport, «HARD-ERROR».decoded]
  exact «HARD-ERROR».export_body «CTX» «STR» «ALIST»

def «FN2-MACHINE-IDP».canonicalBody : Translation.Object := (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [89, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [89, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINE-IDP».body : Term := (.lam ["FN2-MACHINES", "ID"] (.lam ["YES"] (.var "YES") [(.app "IF" [(.app "NATP" [(.var "ID")]), (.app "<" [(.var "ID"), (.app "FN2-MACHINES-ROWS" [(.var "FN2-MACHINES")])]), (.quote Val.nil)])]) [(.app "FN2-CORE-MACHINES" [(.var "FN2-CORE")]), (.var "ID")])
theorem «FN2-MACHINE-IDP».decoded : Translation.readTerm 512 «FN2-MACHINE-IDP».canonicalBody = some «FN2-MACHINE-IDP».body := by rfl
theorem «FN2-MACHINE-IDP».export_body («ID» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] «FN2-MACHINE-IDP».body 512 = .ok («FN2-MACHINE-IDP» «ID» «FN2-CORE») := by
  change Translation.eval fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] (.lam ["FN2-MACHINES", "ID"] (.lam ["YES"] (.var "YES") [(.app "IF" [(.app "NATP" [(.var "ID")]), (.app "<" [(.var "ID"), (.app "FN2-MACHINES-ROWS" [(.var "FN2-MACHINES")])]), (.quote Val.nil)])]) [(.app "FN2-CORE-MACHINES" [(.var "FN2-CORE")]), (.var "ID")]) 512 = _
  refine Translation.eval_lam (vs := [(«FN2-CORE-MACHINES» «FN2-CORE»), «ID»]) ?_ ?_
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
  ·
    refine Translation.eval_lam (vs := [(if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_if (vc := («NATP» «ID»)) (va := (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
        ·
          refine Translation.eval_app (vs := [«ID»]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
        ·
          refine Translation.eval_app (vs := [«ID», («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                refine Translation.eval_app (vs := [(«FN2-CORE-MACHINES» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
              ·
                rfl
        ·
          rfl
      ·
        rfl
    ·
      rfl
theorem «FN2-MACHINE-IDP».canonical_body («ID» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-MACHINE-IDP».canonicalBody fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-MACHINE-IDP» «ID» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-MACHINE-IDP».decoded]
  exact «FN2-MACHINE-IDP».export_body «ID» «FN2-CORE»

def «FN2-MACHINE-SLOT-READ-CODE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 73, 68, 80]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-MACHINE-SLOT-READ-CODE».body : Term := (.app "IF" [(.app "FN2-MACHINE-IDP" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])
theorem «FN2-MACHINE-SLOT-READ-CODE».decoded : Translation.readTerm 512 «FN2-MACHINE-SLOT-READ-CODE».canonicalBody = some «FN2-MACHINE-SLOT-READ-CODE».body := by rfl
theorem «FN2-MACHINE-SLOT-READ-CODE».export_body («ID» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] «FN2-MACHINE-SLOT-READ-CODE».body 512 = .ok («FN2-MACHINE-SLOT-READ-CODE» «ID» «FN2-CORE») := by
  change Translation.eval fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] (.app "IF" [(.app "FN2-MACHINE-IDP" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))]) 512 = _
  refine Translation.eval_if (vc := («FN2-MACHINE-IDP» «ID» «FN2-CORE»)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
  ·
    rfl
  ·
    rfl
theorem «FN2-MACHINE-SLOT-READ-CODE».canonical_body («ID» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-MACHINE-SLOT-READ-CODE».canonicalBody fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-MACHINE-SLOT-READ-CODE» «ID» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-MACHINE-SLOT-READ-CODE».decoded]
  exact «FN2-MACHINE-SLOT-READ-CODE».export_body «ID» «FN2-CORE»

def «EQ».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 85, 65, 76]) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.symbol [65, 67, 76, 50] [89]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «EQ».body : Term := (.app "EQUAL" [(.var "X"), (.var "Y")])
theorem «EQ».decoded : Translation.readTerm 512 «EQ».canonicalBody = some «EQ».body := by rfl
theorem «EQ».export_body («X» : Val) («Y» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("X", «X»), ("Y", «Y»)] «EQ».body 512 = .ok («EQ» «X» «Y») := by
  change Translation.eval fns [("X", «X»), ("Y", «Y»)] (.app "EQUAL" [(.var "X"), (.var "Y")]) 512 = _
  refine Translation.eval_app (vs := [«X», «Y»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «EQ».canonical_body («X» : Val) («Y» : Val) :
    Translation.evalExport 512 «EQ».canonicalBody fns [("X", «X»), ("Y", «Y»)] = .ok («EQ» «X» «Y») := by
  simp only [Translation.evalExport, «EQ».decoded]
  exact «EQ».export_body «X» «Y»

def «FN2-MACHINE-SLOT».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 83, 76, 79, 84, 45, 82, 69, 65, 68, 45, 67, 79, 68, 69]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 83, 76, 79, 84]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [82, 69, 84, 85, 82, 78, 45, 76, 65, 83, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [80, 82, 79, 71, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [65, 67, 76, 50] [72, 65, 82, 68, 45, 69, 82, 82, 79, 82]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.string [73, 110, 118, 97, 108, 105, 100, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 109, 97, 99, 104, 105, 110, 101, 32, 114, 101, 97, 100, 46]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-MACHINE-SLOT».body : Term := (.app "IF" [(.app "EQ" [(.app "FN2-MACHINE-SLOT-READ-CODE" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK"))]), (.lam ["FN2-MACHINES", "ID"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "FN2-MACHINES-SLOT" [(.var "ID"), (.var "FN2-MACHINES")])]) [(.app "FN2-CORE-MACHINES" [(.var "FN2-CORE")]), (.var "ID")]), (.app "RETURN-LAST" [(.quote (Val.sym "PROGN")), (.app "HARD-ERROR" [(.quote (Val.sym "FN2-MACHINE-SLOT")), (.quote (Val.str "Invalid internal machine read.")), (.quote Val.nil)]), (.quote (Val.int 0))])])
theorem «FN2-MACHINE-SLOT».decoded : Translation.readTerm 512 «FN2-MACHINE-SLOT».canonicalBody = some «FN2-MACHINE-SLOT».body := by rfl
theorem «FN2-MACHINE-SLOT».export_body («ID» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] «FN2-MACHINE-SLOT».body 512 = .ok («FN2-MACHINE-SLOT» «ID» «FN2-CORE») := by
  change Translation.eval fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] (.app "IF" [(.app "EQ" [(.app "FN2-MACHINE-SLOT-READ-CODE" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK"))]), (.lam ["FN2-MACHINES", "ID"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "FN2-MACHINES-SLOT" [(.var "ID"), (.var "FN2-MACHINES")])]) [(.app "FN2-CORE-MACHINES" [(.var "FN2-CORE")]), (.var "ID")]), (.app "RETURN-LAST" [(.quote (Val.sym "PROGN")), (.app "HARD-ERROR" [(.quote (Val.sym "FN2-MACHINE-SLOT")), (.quote (Val.str "Invalid internal machine read.")), (.quote Val.nil)]), (.quote (Val.int 0))])]) 512 = _
  refine Translation.eval_if (vc := («EQ» («FN2-MACHINE-SLOT-READ-CODE» «ID» «FN2-CORE») (Val.sym ":OK"))) (va := («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»))) (vb := (Val.int 0)) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT-READ-CODE» «ID» «FN2-CORE»), (Val.sym ":OK")]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
  ·
    refine Translation.eval_lam (vs := [(«FN2-CORE-MACHINES» «FN2-CORE»), «ID»]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
    ·
      refine Translation.eval_lam (vs := [(«FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»))]) ?_ ?_
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [«ID», («FN2-CORE-MACHINES» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          rfl
      ·
        rfl
  ·
    change Translation.eval _ _ (.quote (Val.int 0)) _ = _
    rfl
theorem «FN2-MACHINE-SLOT».canonical_body («ID» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-MACHINE-SLOT».canonicalBody fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-MACHINE-SLOT» «ID» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-MACHINE-SLOT».decoded]
  exact «FN2-MACHINE-SLOT».export_body «ID» «FN2-CORE»

def «FN2-MACHINES-KIND$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-KIND$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 0)), (.var "FN2-MACHINES")])])
theorem «FN2-MACHINES-KIND$AI».decoded : Translation.readTerm 512 «FN2-MACHINES-KIND$AI».canonicalBody = some «FN2-MACHINES-KIND$AI».body := by rfl
theorem «FN2-MACHINES-KIND$AI».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-KIND$AI».body 512 = .ok («FN2-MACHINES-KIND$AI» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 0)), (.var "FN2-MACHINES")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 0) «FN2-MACHINES»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 0), «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-MACHINES-KIND$AI».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-KIND$AI».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-KIND$AI» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-KIND$AI».decoded]
  exact «FN2-MACHINES-KIND$AI».export_body «I» «FN2-MACHINES»

def «FN2-MACHINES-KIND».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 75, 73, 78, 68, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-KIND».body : Term := (.app "FN2-MACHINES-KIND$AI" [(.var "I"), (.var "FN2-MACHINES")])
theorem «FN2-MACHINES-KIND».decoded : Translation.readTerm 512 «FN2-MACHINES-KIND».canonicalBody = some «FN2-MACHINES-KIND».body := by rfl
theorem «FN2-MACHINES-KIND».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-KIND».body 512 = .ok («FN2-MACHINES-KIND» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "FN2-MACHINES-KIND$AI" [(.var "I"), (.var "FN2-MACHINES")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-MACHINES-KIND».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-KIND».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-KIND» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-KIND».decoded]
  exact «FN2-MACHINES-KIND».export_body «I» «FN2-MACHINES»

def «FN2-MACHINE-KIND-READ-CODE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 73, 68, 80]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-MACHINE-KIND-READ-CODE».body : Term := (.app "IF" [(.app "FN2-MACHINE-IDP" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])
theorem «FN2-MACHINE-KIND-READ-CODE».decoded : Translation.readTerm 512 «FN2-MACHINE-KIND-READ-CODE».canonicalBody = some «FN2-MACHINE-KIND-READ-CODE».body := by rfl
theorem «FN2-MACHINE-KIND-READ-CODE».export_body («ID» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] «FN2-MACHINE-KIND-READ-CODE».body 512 = .ok («FN2-MACHINE-KIND-READ-CODE» «ID» «FN2-CORE») := by
  change Translation.eval fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] (.app "IF" [(.app "FN2-MACHINE-IDP" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))]) 512 = _
  refine Translation.eval_if (vc := («FN2-MACHINE-IDP» «ID» «FN2-CORE»)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
  ·
    rfl
  ·
    rfl
theorem «FN2-MACHINE-KIND-READ-CODE».canonical_body («ID» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-MACHINE-KIND-READ-CODE».canonicalBody fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-MACHINE-KIND-READ-CODE» «ID» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-MACHINE-KIND-READ-CODE».decoded]
  exact «FN2-MACHINE-KIND-READ-CODE».export_body «ID» «FN2-CORE»

def «FN2-MACHINE-KIND».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 75, 73, 78, 68, 45, 82, 69, 65, 68, 45, 67, 79, 68, 69]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 75, 73, 78, 68]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [82, 69, 84, 85, 82, 78, 45, 76, 65, 83, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [80, 82, 79, 71, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [65, 67, 76, 50] [72, 65, 82, 68, 45, 69, 82, 82, 79, 82]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 75, 73, 78, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.string [73, 110, 118, 97, 108, 105, 100, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 109, 97, 99, 104, 105, 110, 101, 32, 114, 101, 97, 100, 46]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-MACHINE-KIND».body : Term := (.app "IF" [(.app "EQ" [(.app "FN2-MACHINE-KIND-READ-CODE" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK"))]), (.lam ["FN2-MACHINES", "ID"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "FN2-MACHINES-KIND" [(.var "ID"), (.var "FN2-MACHINES")])]) [(.app "FN2-CORE-MACHINES" [(.var "FN2-CORE")]), (.var "ID")]), (.app "RETURN-LAST" [(.quote (Val.sym "PROGN")), (.app "HARD-ERROR" [(.quote (Val.sym "FN2-MACHINE-KIND")), (.quote (Val.str "Invalid internal machine read.")), (.quote Val.nil)]), (.quote (Val.int 0))])])
theorem «FN2-MACHINE-KIND».decoded : Translation.readTerm 512 «FN2-MACHINE-KIND».canonicalBody = some «FN2-MACHINE-KIND».body := by rfl
theorem «FN2-MACHINE-KIND».export_body («ID» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] «FN2-MACHINE-KIND».body 512 = .ok («FN2-MACHINE-KIND» «ID» «FN2-CORE») := by
  change Translation.eval fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] (.app "IF" [(.app "EQ" [(.app "FN2-MACHINE-KIND-READ-CODE" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK"))]), (.lam ["FN2-MACHINES", "ID"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "FN2-MACHINES-KIND" [(.var "ID"), (.var "FN2-MACHINES")])]) [(.app "FN2-CORE-MACHINES" [(.var "FN2-CORE")]), (.var "ID")]), (.app "RETURN-LAST" [(.quote (Val.sym "PROGN")), (.app "HARD-ERROR" [(.quote (Val.sym "FN2-MACHINE-KIND")), (.quote (Val.str "Invalid internal machine read.")), (.quote Val.nil)]), (.quote (Val.int 0))])]) 512 = _
  refine Translation.eval_if (vc := («EQ» («FN2-MACHINE-KIND-READ-CODE» «ID» «FN2-CORE») (Val.sym ":OK"))) (va := («FN2-MACHINES-KIND» «ID» («FN2-CORE-MACHINES» «FN2-CORE»))) (vb := (Val.int 0)) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND-READ-CODE» «ID» «FN2-CORE»), (Val.sym ":OK")]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
  ·
    refine Translation.eval_lam (vs := [(«FN2-CORE-MACHINES» «FN2-CORE»), «ID»]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
    ·
      refine Translation.eval_lam (vs := [(«FN2-MACHINES-KIND» «ID» («FN2-CORE-MACHINES» «FN2-CORE»))]) ?_ ?_
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [«ID», («FN2-CORE-MACHINES» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          rfl
      ·
        rfl
  ·
    change Translation.eval _ _ (.quote (Val.int 0)) _ = _
    rfl
theorem «FN2-MACHINE-KIND».canonical_body («ID» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-MACHINE-KIND».canonicalBody fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-MACHINE-KIND» «ID» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-MACHINE-KIND».decoded]
  exact «FN2-MACHINE-KIND».export_body «ID» «FN2-CORE»

def «FN2-BOOT-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (19)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-BOOT-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 19)), (.var "FN2-CORE")])
theorem «FN2-BOOT-TABLE».decoded : Translation.readTerm 512 «FN2-BOOT-TABLE».canonicalBody = some «FN2-BOOT-TABLE».body := by rfl
theorem «FN2-BOOT-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-BOOT-TABLE».body 512 = .ok («FN2-BOOT-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 19)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 19), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-BOOT-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-BOOT-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-BOOT-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-BOOT-TABLE».decoded]
  exact «FN2-BOOT-TABLE».export_body «FN2-CORE»

def «FN2-BOOT-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (26)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 66, 79, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-BOOT-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 26)), (.var "FN2-BOOT")])
theorem «FN2-BOOT-ROWS».decoded : Translation.readTerm 512 «FN2-BOOT-ROWS».canonicalBody = some «FN2-BOOT-ROWS».body := by rfl
theorem «FN2-BOOT-ROWS».export_body («FN2-BOOT» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-BOOT", «FN2-BOOT»)] «FN2-BOOT-ROWS».body 512 = .ok («FN2-BOOT-ROWS» «FN2-BOOT») := by
  change Translation.eval fns [("FN2-BOOT", «FN2-BOOT»)] (.app "NTH" [(.quote (Val.int 26)), (.var "FN2-BOOT")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 26), «FN2-BOOT»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-BOOT-ROWS».canonical_body («FN2-BOOT» : Val) :
    Translation.evalExport 512 «FN2-BOOT-ROWS».canonicalBody fns [("FN2-BOOT", «FN2-BOOT»)] = .ok («FN2-BOOT-ROWS» «FN2-BOOT») := by
  simp only [Translation.evalExport, «FN2-BOOT-ROWS».decoded]
  exact «FN2-BOOT-ROWS».export_body «FN2-BOOT»

def «FN2-AUTH-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (18)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-AUTH-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 18)), (.var "FN2-CORE")])
theorem «FN2-AUTH-TABLE».decoded : Translation.readTerm 512 «FN2-AUTH-TABLE».canonicalBody = some «FN2-AUTH-TABLE».body := by rfl
theorem «FN2-AUTH-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-AUTH-TABLE».body 512 = .ok («FN2-AUTH-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 18)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 18), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-AUTH-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-AUTH-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-AUTH-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-AUTH-TABLE».decoded]
  exact «FN2-AUTH-TABLE».export_body «FN2-CORE»

def «FN2-AUTH-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (46)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 65, 85, 84, 72]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-AUTH-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 46)), (.var "FN2-AUTH")])
theorem «FN2-AUTH-ROWS».decoded : Translation.readTerm 512 «FN2-AUTH-ROWS».canonicalBody = some «FN2-AUTH-ROWS».body := by rfl
theorem «FN2-AUTH-ROWS».export_body («FN2-AUTH» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-AUTH", «FN2-AUTH»)] «FN2-AUTH-ROWS».body 512 = .ok («FN2-AUTH-ROWS» «FN2-AUTH») := by
  change Translation.eval fns [("FN2-AUTH", «FN2-AUTH»)] (.app "NTH" [(.quote (Val.int 46)), (.var "FN2-AUTH")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 46), «FN2-AUTH»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-AUTH-ROWS».canonical_body («FN2-AUTH» : Val) :
    Translation.evalExport 512 «FN2-AUTH-ROWS».canonicalBody fns [("FN2-AUTH", «FN2-AUTH»)] = .ok («FN2-AUTH-ROWS» «FN2-AUTH») := by
  simp only [Translation.evalExport, «FN2-AUTH-ROWS».decoded]
  exact «FN2-AUTH-ROWS».export_body «FN2-AUTH»

def «FN2-CNS-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (17)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CNS-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 17)), (.var "FN2-CORE")])
theorem «FN2-CNS-TABLE».decoded : Translation.readTerm 512 «FN2-CNS-TABLE».canonicalBody = some «FN2-CNS-TABLE».body := by rfl
theorem «FN2-CNS-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-CNS-TABLE».body 512 = .ok («FN2-CNS-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 17)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 17), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CNS-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-CNS-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-CNS-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-CNS-TABLE».decoded]
  exact «FN2-CNS-TABLE».export_body «FN2-CORE»

def «FN2-CNS-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (67)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 78, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CNS-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 67)), (.var "FN2-CNS")])
theorem «FN2-CNS-ROWS».decoded : Translation.readTerm 512 «FN2-CNS-ROWS».canonicalBody = some «FN2-CNS-ROWS».body := by rfl
theorem «FN2-CNS-ROWS».export_body («FN2-CNS» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CNS", «FN2-CNS»)] «FN2-CNS-ROWS».body 512 = .ok («FN2-CNS-ROWS» «FN2-CNS») := by
  change Translation.eval fns [("FN2-CNS", «FN2-CNS»)] (.app "NTH" [(.quote (Val.int 67)), (.var "FN2-CNS")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 67), «FN2-CNS»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CNS-ROWS».canonical_body («FN2-CNS» : Val) :
    Translation.evalExport 512 «FN2-CNS-ROWS».canonicalBody fns [("FN2-CNS", «FN2-CNS»)] = .ok («FN2-CNS-ROWS» «FN2-CNS») := by
  simp only [Translation.evalExport, «FN2-CNS-ROWS».decoded]
  exact «FN2-CNS-ROWS».export_body «FN2-CNS»

def «FN2-CTL-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (16)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CTL-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 16)), (.var "FN2-CORE")])
theorem «FN2-CTL-TABLE».decoded : Translation.readTerm 512 «FN2-CTL-TABLE».canonicalBody = some «FN2-CTL-TABLE».body := by rfl
theorem «FN2-CTL-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-CTL-TABLE».body 512 = .ok («FN2-CTL-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 16)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 16), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CTL-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-CTL-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-CTL-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-CTL-TABLE».decoded]
  exact «FN2-CTL-TABLE».export_body «FN2-CORE»

def «FN2-CTL-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (34)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 84, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CTL-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 34)), (.var "FN2-CTL")])
theorem «FN2-CTL-ROWS».decoded : Translation.readTerm 512 «FN2-CTL-ROWS».canonicalBody = some «FN2-CTL-ROWS».body := by rfl
theorem «FN2-CTL-ROWS».export_body («FN2-CTL» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CTL", «FN2-CTL»)] «FN2-CTL-ROWS».body 512 = .ok («FN2-CTL-ROWS» «FN2-CTL») := by
  change Translation.eval fns [("FN2-CTL", «FN2-CTL»)] (.app "NTH" [(.quote (Val.int 34)), (.var "FN2-CTL")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 34), «FN2-CTL»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CTL-ROWS».canonical_body («FN2-CTL» : Val) :
    Translation.evalExport 512 «FN2-CTL-ROWS».canonicalBody fns [("FN2-CTL", «FN2-CTL»)] = .ok («FN2-CTL-ROWS» «FN2-CTL») := by
  simp only [Translation.evalExport, «FN2-CTL-ROWS».decoded]
  exact «FN2-CTL-ROWS».export_body «FN2-CTL»

def «FN2-CURSOR-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (15)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CURSOR-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 15)), (.var "FN2-CORE")])
theorem «FN2-CURSOR-TABLE».decoded : Translation.readTerm 512 «FN2-CURSOR-TABLE».canonicalBody = some «FN2-CURSOR-TABLE».body := by rfl
theorem «FN2-CURSOR-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-CURSOR-TABLE».body 512 = .ok («FN2-CURSOR-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 15)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 15), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CURSOR-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-CURSOR-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-CURSOR-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-CURSOR-TABLE».decoded]
  exact «FN2-CURSOR-TABLE».export_body «FN2-CORE»

def «FN2-CURSOR-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (85)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 85, 82, 83, 79, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CURSOR-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 85)), (.var "FN2-CURSOR")])
theorem «FN2-CURSOR-ROWS».decoded : Translation.readTerm 512 «FN2-CURSOR-ROWS».canonicalBody = some «FN2-CURSOR-ROWS».body := by rfl
theorem «FN2-CURSOR-ROWS».export_body («FN2-CURSOR» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CURSOR", «FN2-CURSOR»)] «FN2-CURSOR-ROWS».body 512 = .ok («FN2-CURSOR-ROWS» «FN2-CURSOR») := by
  change Translation.eval fns [("FN2-CURSOR", «FN2-CURSOR»)] (.app "NTH" [(.quote (Val.int 85)), (.var "FN2-CURSOR")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 85), «FN2-CURSOR»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CURSOR-ROWS».canonical_body («FN2-CURSOR» : Val) :
    Translation.evalExport 512 «FN2-CURSOR-ROWS».canonicalBody fns [("FN2-CURSOR", «FN2-CURSOR»)] = .ok («FN2-CURSOR-ROWS» «FN2-CURSOR») := by
  simp only [Translation.evalExport, «FN2-CURSOR-ROWS».decoded]
  exact «FN2-CURSOR-ROWS».export_body «FN2-CURSOR»

def «FN2-TXN-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (14)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-TXN-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 14)), (.var "FN2-CORE")])
theorem «FN2-TXN-TABLE».decoded : Translation.readTerm 512 «FN2-TXN-TABLE».canonicalBody = some «FN2-TXN-TABLE».body := by rfl
theorem «FN2-TXN-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-TXN-TABLE».body 512 = .ok («FN2-TXN-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 14)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 14), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-TXN-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-TXN-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-TXN-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-TXN-TABLE».decoded]
  exact «FN2-TXN-TABLE».export_body «FN2-CORE»

def «FN2-TXN-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (30)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 84, 88, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-TXN-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 30)), (.var "FN2-TXN")])
theorem «FN2-TXN-ROWS».decoded : Translation.readTerm 512 «FN2-TXN-ROWS».canonicalBody = some «FN2-TXN-ROWS».body := by rfl
theorem «FN2-TXN-ROWS».export_body («FN2-TXN» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-TXN", «FN2-TXN»)] «FN2-TXN-ROWS».body 512 = .ok («FN2-TXN-ROWS» «FN2-TXN») := by
  change Translation.eval fns [("FN2-TXN", «FN2-TXN»)] (.app "NTH" [(.quote (Val.int 30)), (.var "FN2-TXN")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 30), «FN2-TXN»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-TXN-ROWS».canonical_body («FN2-TXN» : Val) :
    Translation.evalExport 512 «FN2-TXN-ROWS».canonicalBody fns [("FN2-TXN", «FN2-TXN»)] = .ok («FN2-TXN-ROWS» «FN2-TXN») := by
  simp only [Translation.evalExport, «FN2-TXN-ROWS».decoded]
  exact «FN2-TXN-ROWS».export_body «FN2-TXN»

def «FN2-UPLOAD-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (13)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-UPLOAD-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 13)), (.var "FN2-CORE")])
theorem «FN2-UPLOAD-TABLE».decoded : Translation.readTerm 512 «FN2-UPLOAD-TABLE».canonicalBody = some «FN2-UPLOAD-TABLE».body := by rfl
theorem «FN2-UPLOAD-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-UPLOAD-TABLE».body 512 = .ok («FN2-UPLOAD-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 13)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 13), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-UPLOAD-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-UPLOAD-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-UPLOAD-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-UPLOAD-TABLE».decoded]
  exact «FN2-UPLOAD-TABLE».export_body «FN2-CORE»

def «FN2-UPLOAD-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (56)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 85, 80, 76, 79, 65, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-UPLOAD-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 56)), (.var "FN2-UPLOAD")])
theorem «FN2-UPLOAD-ROWS».decoded : Translation.readTerm 512 «FN2-UPLOAD-ROWS».canonicalBody = some «FN2-UPLOAD-ROWS».body := by rfl
theorem «FN2-UPLOAD-ROWS».export_body («FN2-UPLOAD» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-UPLOAD", «FN2-UPLOAD»)] «FN2-UPLOAD-ROWS».body 512 = .ok («FN2-UPLOAD-ROWS» «FN2-UPLOAD») := by
  change Translation.eval fns [("FN2-UPLOAD", «FN2-UPLOAD»)] (.app "NTH" [(.quote (Val.int 56)), (.var "FN2-UPLOAD")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 56), «FN2-UPLOAD»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-UPLOAD-ROWS».canonical_body («FN2-UPLOAD» : Val) :
    Translation.evalExport 512 «FN2-UPLOAD-ROWS».canonicalBody fns [("FN2-UPLOAD", «FN2-UPLOAD»)] = .ok («FN2-UPLOAD-ROWS» «FN2-UPLOAD») := by
  simp only [Translation.evalExport, «FN2-UPLOAD-ROWS».decoded]
  exact «FN2-UPLOAD-ROWS».export_body «FN2-UPLOAD»

def «FN2-CONN-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (12)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CONN-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 12)), (.var "FN2-CORE")])
theorem «FN2-CONN-TABLE».decoded : Translation.readTerm 512 «FN2-CONN-TABLE».canonicalBody = some «FN2-CONN-TABLE».body := by rfl
theorem «FN2-CONN-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-CONN-TABLE».body 512 = .ok («FN2-CONN-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 12)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 12), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CONN-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-CONN-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-CONN-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-CONN-TABLE».decoded]
  exact «FN2-CONN-TABLE».export_body «FN2-CORE»

def «FN2-CONN-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (50)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-CONN-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 50)), (.var "FN2-CONN")])
theorem «FN2-CONN-ROWS».decoded : Translation.readTerm 512 «FN2-CONN-ROWS».canonicalBody = some «FN2-CONN-ROWS».body := by rfl
theorem «FN2-CONN-ROWS».export_body («FN2-CONN» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CONN", «FN2-CONN»)] «FN2-CONN-ROWS».body 512 = .ok («FN2-CONN-ROWS» «FN2-CONN») := by
  change Translation.eval fns [("FN2-CONN", «FN2-CONN»)] (.app "NTH" [(.quote (Val.int 50)), (.var "FN2-CONN")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 50), «FN2-CONN»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-CONN-ROWS».canonical_body («FN2-CONN» : Val) :
    Translation.evalExport 512 «FN2-CONN-ROWS».canonicalBody fns [("FN2-CONN", «FN2-CONN»)] = .ok («FN2-CONN-ROWS» «FN2-CONN») := by
  simp only [Translation.evalExport, «FN2-CONN-ROWS».decoded]
  exact «FN2-CONN-ROWS».export_body «FN2-CONN»

def «FN2-SEALER-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (11)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-SEALER-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 11)), (.var "FN2-CORE")])
theorem «FN2-SEALER-TABLE».decoded : Translation.readTerm 512 «FN2-SEALER-TABLE».canonicalBody = some «FN2-SEALER-TABLE».body := by rfl
theorem «FN2-SEALER-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-SEALER-TABLE».body 512 = .ok («FN2-SEALER-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 11)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 11), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-SEALER-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-SEALER-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-SEALER-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-SEALER-TABLE».decoded]
  exact «FN2-SEALER-TABLE».export_body «FN2-CORE»

def «FN2-SEALER-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (6)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 69, 65, 76, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-SEALER-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 6)), (.var "FN2-SEALER")])
theorem «FN2-SEALER-ROWS».decoded : Translation.readTerm 512 «FN2-SEALER-ROWS».canonicalBody = some «FN2-SEALER-ROWS».body := by rfl
theorem «FN2-SEALER-ROWS».export_body («FN2-SEALER» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-SEALER", «FN2-SEALER»)] «FN2-SEALER-ROWS».body 512 = .ok («FN2-SEALER-ROWS» «FN2-SEALER») := by
  change Translation.eval fns [("FN2-SEALER", «FN2-SEALER»)] (.app "NTH" [(.quote (Val.int 6)), (.var "FN2-SEALER")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 6), «FN2-SEALER»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-SEALER-ROWS».canonical_body («FN2-SEALER» : Val) :
    Translation.evalExport 512 «FN2-SEALER-ROWS».canonicalBody fns [("FN2-SEALER", «FN2-SEALER»)] = .ok («FN2-SEALER-ROWS» «FN2-SEALER») := by
  simp only [Translation.evalExport, «FN2-SEALER-ROWS».decoded]
  exact «FN2-SEALER-ROWS».export_body «FN2-SEALER»

def «FN2-RECOVERY-MACHINE-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (10)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-RECOVERY-MACHINE-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 10)), (.var "FN2-CORE")])
theorem «FN2-RECOVERY-MACHINE-TABLE».decoded : Translation.readTerm 512 «FN2-RECOVERY-MACHINE-TABLE».canonicalBody = some «FN2-RECOVERY-MACHINE-TABLE».body := by rfl
theorem «FN2-RECOVERY-MACHINE-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-RECOVERY-MACHINE-TABLE».body 512 = .ok («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 10)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 10), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-RECOVERY-MACHINE-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-RECOVERY-MACHINE-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-RECOVERY-MACHINE-TABLE».decoded]
  exact «FN2-RECOVERY-MACHINE-TABLE».export_body «FN2-CORE»

def «FN2-RECOVERY-MACHINE-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (42)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 82, 69, 67, 79, 86, 69, 82, 89, 45, 77, 65, 67, 72, 73, 78, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-RECOVERY-MACHINE-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 42)), (.var "FN2-RECOVERY-MACHINE")])
theorem «FN2-RECOVERY-MACHINE-ROWS».decoded : Translation.readTerm 512 «FN2-RECOVERY-MACHINE-ROWS».canonicalBody = some «FN2-RECOVERY-MACHINE-ROWS».body := by rfl
theorem «FN2-RECOVERY-MACHINE-ROWS».export_body («FN2-RECOVERY-MACHINE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-RECOVERY-MACHINE", «FN2-RECOVERY-MACHINE»)] «FN2-RECOVERY-MACHINE-ROWS».body 512 = .ok («FN2-RECOVERY-MACHINE-ROWS» «FN2-RECOVERY-MACHINE») := by
  change Translation.eval fns [("FN2-RECOVERY-MACHINE", «FN2-RECOVERY-MACHINE»)] (.app "NTH" [(.quote (Val.int 42)), (.var "FN2-RECOVERY-MACHINE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 42), «FN2-RECOVERY-MACHINE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-RECOVERY-MACHINE-ROWS».canonical_body («FN2-RECOVERY-MACHINE» : Val) :
    Translation.evalExport 512 «FN2-RECOVERY-MACHINE-ROWS».canonicalBody fns [("FN2-RECOVERY-MACHINE", «FN2-RECOVERY-MACHINE»)] = .ok («FN2-RECOVERY-MACHINE-ROWS» «FN2-RECOVERY-MACHINE») := by
  simp only [Translation.evalExport, «FN2-RECOVERY-MACHINE-ROWS».decoded]
  exact «FN2-RECOVERY-MACHINE-ROWS».export_body «FN2-RECOVERY-MACHINE»

def «FN2-COMMIT-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (9)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-COMMIT-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 9)), (.var "FN2-CORE")])
theorem «FN2-COMMIT-TABLE».decoded : Translation.readTerm 512 «FN2-COMMIT-TABLE».canonicalBody = some «FN2-COMMIT-TABLE».body := by rfl
theorem «FN2-COMMIT-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-COMMIT-TABLE».body 512 = .ok («FN2-COMMIT-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 9)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 9), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-COMMIT-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-COMMIT-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-COMMIT-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-COMMIT-TABLE».decoded]
  exact «FN2-COMMIT-TABLE».export_body «FN2-CORE»

def «FN2-COMMIT-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (33)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 77, 77, 73, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-COMMIT-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 33)), (.var "FN2-COMMIT")])
theorem «FN2-COMMIT-ROWS».decoded : Translation.readTerm 512 «FN2-COMMIT-ROWS».canonicalBody = some «FN2-COMMIT-ROWS».body := by rfl
theorem «FN2-COMMIT-ROWS».export_body («FN2-COMMIT» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-COMMIT", «FN2-COMMIT»)] «FN2-COMMIT-ROWS».body 512 = .ok («FN2-COMMIT-ROWS» «FN2-COMMIT») := by
  change Translation.eval fns [("FN2-COMMIT", «FN2-COMMIT»)] (.app "NTH" [(.quote (Val.int 33)), (.var "FN2-COMMIT")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 33), «FN2-COMMIT»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-COMMIT-ROWS».canonical_body («FN2-COMMIT» : Val) :
    Translation.evalExport 512 «FN2-COMMIT-ROWS».canonicalBody fns [("FN2-COMMIT", «FN2-COMMIT»)] = .ok («FN2-COMMIT-ROWS» «FN2-COMMIT») := by
  simp only [Translation.evalExport, «FN2-COMMIT-ROWS».decoded]
  exact «FN2-COMMIT-ROWS».export_body «FN2-COMMIT»

def «FN2-SCRIBE-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (8)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-SCRIBE-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 8)), (.var "FN2-CORE")])
theorem «FN2-SCRIBE-TABLE».decoded : Translation.readTerm 512 «FN2-SCRIBE-TABLE».canonicalBody = some «FN2-SCRIBE-TABLE».body := by rfl
theorem «FN2-SCRIBE-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-SCRIBE-TABLE».body 512 = .ok («FN2-SCRIBE-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 8)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 8), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-SCRIBE-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-SCRIBE-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-SCRIBE-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-SCRIBE-TABLE».decoded]
  exact «FN2-SCRIBE-TABLE».export_body «FN2-CORE»

def «FN2-SCRIBE-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (21)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 67, 82, 73, 66, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-SCRIBE-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 21)), (.var "FN2-SCRIBE")])
theorem «FN2-SCRIBE-ROWS».decoded : Translation.readTerm 512 «FN2-SCRIBE-ROWS».canonicalBody = some «FN2-SCRIBE-ROWS».body := by rfl
theorem «FN2-SCRIBE-ROWS».export_body («FN2-SCRIBE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-SCRIBE", «FN2-SCRIBE»)] «FN2-SCRIBE-ROWS».body 512 = .ok («FN2-SCRIBE-ROWS» «FN2-SCRIBE») := by
  change Translation.eval fns [("FN2-SCRIBE", «FN2-SCRIBE»)] (.app "NTH" [(.quote (Val.int 21)), (.var "FN2-SCRIBE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 21), «FN2-SCRIBE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-SCRIBE-ROWS».canonical_body («FN2-SCRIBE» : Val) :
    Translation.evalExport 512 «FN2-SCRIBE-ROWS».canonicalBody fns [("FN2-SCRIBE", «FN2-SCRIBE»)] = .ok («FN2-SCRIBE-ROWS» «FN2-SCRIBE») := by
  simp only [Translation.evalExport, «FN2-SCRIBE-ROWS».decoded]
  exact «FN2-SCRIBE-ROWS».export_body «FN2-SCRIBE»

def «FN2-LISTENER-TABLE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (6)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-LISTENER-TABLE».body : Term := (.app "NTH" [(.quote (Val.int 6)), (.var "FN2-CORE")])
theorem «FN2-LISTENER-TABLE».decoded : Translation.readTerm 512 «FN2-LISTENER-TABLE».canonicalBody = some «FN2-LISTENER-TABLE».body := by rfl
theorem «FN2-LISTENER-TABLE».export_body («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-CORE", «FN2-CORE»)] «FN2-LISTENER-TABLE».body 512 = .ok («FN2-LISTENER-TABLE» «FN2-CORE») := by
  change Translation.eval fns [("FN2-CORE", «FN2-CORE»)] (.app "NTH" [(.quote (Val.int 6)), (.var "FN2-CORE")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 6), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-LISTENER-TABLE».canonical_body («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-LISTENER-TABLE».canonicalBody fns [("FN2-CORE", «FN2-CORE»)] = .ok («FN2-LISTENER-TABLE» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-LISTENER-TABLE».decoded]
  exact «FN2-LISTENER-TABLE».export_body «FN2-CORE»

def «FN2-LISTENER-ROWS».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (19)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 76, 73, 83, 84, 69, 78, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-LISTENER-ROWS».body : Term := (.app "NTH" [(.quote (Val.int 19)), (.var "FN2-LISTENER")])
theorem «FN2-LISTENER-ROWS».decoded : Translation.readTerm 512 «FN2-LISTENER-ROWS».canonicalBody = some «FN2-LISTENER-ROWS».body := by rfl
theorem «FN2-LISTENER-ROWS».export_body («FN2-LISTENER» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("FN2-LISTENER", «FN2-LISTENER»)] «FN2-LISTENER-ROWS».body 512 = .ok («FN2-LISTENER-ROWS» «FN2-LISTENER») := by
  change Translation.eval fns [("FN2-LISTENER", «FN2-LISTENER»)] (.app "NTH" [(.quote (Val.int 19)), (.var "FN2-LISTENER")]) 512 = _
  refine Translation.eval_app (vs := [(Val.int 19), «FN2-LISTENER»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-LISTENER-ROWS».canonical_body («FN2-LISTENER» : Val) :
    Translation.evalExport 512 «FN2-LISTENER-ROWS».canonicalBody fns [("FN2-LISTENER", «FN2-LISTENER»)] = .ok («FN2-LISTENER-ROWS» «FN2-LISTENER») := by
  simp only [Translation.evalExport, «FN2-LISTENER-ROWS».decoded]
  exact «FN2-LISTENER-ROWS».export_body «FN2-LISTENER»

def «EQL».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 85, 65, 76]) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.symbol [65, 67, 76, 50] [89]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «EQL».body : Term := (.app "EQUAL" [(.var "X"), (.var "Y")])
theorem «EQL».decoded : Translation.readTerm 512 «EQL».canonicalBody = some «EQL».body := by rfl
theorem «EQL».export_body («X» : Val) («Y» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("X", «X»), ("Y", «Y»)] «EQL».body 512 = .ok («EQL» «X» «Y») := by
  change Translation.eval fns [("X", «X»), ("Y", «Y»)] (.app "EQUAL" [(.var "X"), (.var "Y")]) 512 = _
  refine Translation.eval_app (vs := [«X», «Y»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «EQL».canonical_body («X» : Val) («Y» : Val) :
    Translation.evalExport 512 «EQL».canonicalBody fns [("X", «X»), ("Y", «Y»)] = .ok («EQL» «X» «Y») := by
  simp only [Translation.evalExport, «EQL».decoded]
  exact «EQL».export_body «X» «Y»

def «FN2-MACHINE-PHASE-READ-CODE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 73, 68, 80]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 76, 73, 83, 84, 69, 78, 69, 82]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 76, 73, 83, 84, 69, 78, 69, 82, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 76, 73, 83, 84, 69, 78, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 76, 73, 83, 84, 69, 78, 69, 82, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (2)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 67, 82, 73, 66, 69]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 67, 82, 73, 66, 69, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 67, 82, 73, 66, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 67, 82, 73, 66, 69, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (3)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 77, 77, 73, 84]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 77, 77, 73, 84, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 77, 77, 73, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 77, 77, 73, 84, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (4)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 82, 69, 67, 79, 86, 69, 82, 89, 45, 77, 65, 67, 72, 73, 78, 69]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 82, 69, 67, 79, 86, 69, 82, 89, 45, 77, 65, 67, 72, 73, 78, 69, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 82, 69, 67, 79, 86, 69, 82, 89, 45, 77, 65, 67, 72, 73, 78, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 82, 69, 67, 79, 86, 69, 82, 89, 45, 77, 65, 67, 72, 73, 78, 69, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (5)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 69, 65, 76, 69, 82]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 69, 65, 76, 69, 82, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 69, 65, 76, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 83, 69, 65, 76, 69, 82, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (6)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 78]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 78, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 78, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (7)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 85, 80, 76, 79, 65, 68]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 85, 80, 76, 79, 65, 68, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 85, 80, 76, 79, 65, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 85, 80, 76, 79, 65, 68, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (8)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 84, 88, 78]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 84, 88, 78, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 84, 88, 78]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 84, 88, 78, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (9)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 85, 82, 83, 79, 82]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 85, 82, 83, 79, 82, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 85, 82, 83, 79, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 85, 82, 83, 79, 82, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (10)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 84, 76]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 84, 76, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 84, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 84, 76, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (11)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 78, 83, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 78, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 78, 83, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (12)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 65, 85, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 65, 85, 84, 72, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 65, 85, 84, 72]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 65, 85, 84, 72, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 76]) (.cons (.symbol [65, 67, 76, 50] [67, 65, 83, 69, 45, 68, 79, 45, 78, 79, 84, 45, 85, 83, 69, 45, 69, 76, 83, 69, 87, 72, 69, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (13)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 66, 79, 79, 84]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.symbol [65, 67, 76, 50] [65, 78, 83, 87, 69, 82]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 66, 79, 79, 84, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 66, 79, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [66, 79, 85, 78, 68, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 66, 79, 79, 84, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [75, 73, 78, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 75, 73, 78, 68]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 83, 76, 79, 84]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-MACHINE-PHASE-READ-CODE».body : Term := (.app "IF" [(.app "NOT" [(.app "FN2-MACHINE-IDP" [(.var "ID"), (.var "FN2-CORE")])]), (.quote (Val.sym ":BOUNDS")), (.lam ["SLOT", "FN2-CORE", "ID"] (.lam ["CASE-DO-NOT-USE-ELSEWHERE", "SLOT", "FN2-CORE"] (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 0))]), (.lam ["FN2-LISTENER", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-LISTENER-ROWS" [(.var "FN2-LISTENER")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-LISTENER-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 1))]), (.lam ["FN2-ECHO", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-ECHO-ROWS" [(.var "FN2-ECHO")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-ECHO-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 2))]), (.lam ["FN2-SCRIBE", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-SCRIBE-ROWS" [(.var "FN2-SCRIBE")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-SCRIBE-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 3))]), (.lam ["FN2-COMMIT", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-COMMIT-ROWS" [(.var "FN2-COMMIT")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-COMMIT-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 4))]), (.lam ["FN2-RECOVERY-MACHINE", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-RECOVERY-MACHINE-ROWS" [(.var "FN2-RECOVERY-MACHINE")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-RECOVERY-MACHINE-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 5))]), (.lam ["FN2-SEALER", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-SEALER-ROWS" [(.var "FN2-SEALER")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-SEALER-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 6))]), (.lam ["FN2-CONN", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-CONN-ROWS" [(.var "FN2-CONN")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-CONN-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 7))]), (.lam ["FN2-UPLOAD", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-UPLOAD-ROWS" [(.var "FN2-UPLOAD")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-UPLOAD-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 8))]), (.lam ["FN2-TXN", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-TXN-ROWS" [(.var "FN2-TXN")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-TXN-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 9))]), (.lam ["FN2-CURSOR", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-CURSOR-ROWS" [(.var "FN2-CURSOR")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-CURSOR-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 10))]), (.lam ["FN2-CTL", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-CTL-ROWS" [(.var "FN2-CTL")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-CTL-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 11))]), (.lam ["FN2-CNS", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-CNS-ROWS" [(.var "FN2-CNS")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-CNS-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 12))]), (.lam ["FN2-AUTH", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-AUTH-ROWS" [(.var "FN2-AUTH")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-AUTH-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 13))]), (.lam ["FN2-BOOT", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-BOOT-ROWS" [(.var "FN2-BOOT")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-BOOT-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.quote (Val.sym ":KIND"))])])])])])])])])])])])])])]) [(.app "FN2-MACHINE-KIND" [(.var "ID"), (.var "FN2-CORE")]), (.var "SLOT"), (.var "FN2-CORE")]) [(.app "FN2-MACHINE-SLOT" [(.var "ID"), (.var "FN2-CORE")]), (.var "FN2-CORE"), (.var "ID")])])
theorem «FN2-MACHINE-PHASE-READ-CODE».decoded : Translation.readTerm 512 «FN2-MACHINE-PHASE-READ-CODE».canonicalBody = some «FN2-MACHINE-PHASE-READ-CODE».body := by rfl
theorem «FN2-MACHINE-PHASE-READ-CODE».export_body («ID» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] «FN2-MACHINE-PHASE-READ-CODE».body 512 = .ok («FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE») := by
  change Translation.eval fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] (.app "IF" [(.app "NOT" [(.app "FN2-MACHINE-IDP" [(.var "ID"), (.var "FN2-CORE")])]), (.quote (Val.sym ":BOUNDS")), (.lam ["SLOT", "FN2-CORE", "ID"] (.lam ["CASE-DO-NOT-USE-ELSEWHERE", "SLOT", "FN2-CORE"] (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 0))]), (.lam ["FN2-LISTENER", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-LISTENER-ROWS" [(.var "FN2-LISTENER")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-LISTENER-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 1))]), (.lam ["FN2-ECHO", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-ECHO-ROWS" [(.var "FN2-ECHO")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-ECHO-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 2))]), (.lam ["FN2-SCRIBE", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-SCRIBE-ROWS" [(.var "FN2-SCRIBE")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-SCRIBE-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 3))]), (.lam ["FN2-COMMIT", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-COMMIT-ROWS" [(.var "FN2-COMMIT")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-COMMIT-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 4))]), (.lam ["FN2-RECOVERY-MACHINE", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-RECOVERY-MACHINE-ROWS" [(.var "FN2-RECOVERY-MACHINE")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-RECOVERY-MACHINE-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 5))]), (.lam ["FN2-SEALER", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-SEALER-ROWS" [(.var "FN2-SEALER")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-SEALER-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 6))]), (.lam ["FN2-CONN", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-CONN-ROWS" [(.var "FN2-CONN")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-CONN-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 7))]), (.lam ["FN2-UPLOAD", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-UPLOAD-ROWS" [(.var "FN2-UPLOAD")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-UPLOAD-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 8))]), (.lam ["FN2-TXN", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-TXN-ROWS" [(.var "FN2-TXN")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-TXN-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 9))]), (.lam ["FN2-CURSOR", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-CURSOR-ROWS" [(.var "FN2-CURSOR")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-CURSOR-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 10))]), (.lam ["FN2-CTL", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-CTL-ROWS" [(.var "FN2-CTL")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-CTL-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 11))]), (.lam ["FN2-CNS", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-CNS-ROWS" [(.var "FN2-CNS")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-CNS-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 12))]), (.lam ["FN2-AUTH", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-AUTH-ROWS" [(.var "FN2-AUTH")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-AUTH-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.app "IF" [(.app "EQL" [(.var "CASE-DO-NOT-USE-ELSEWHERE"), (.quote (Val.int 13))]), (.lam ["FN2-BOOT", "SLOT"] (.lam ["ANSWER"] (.var "ANSWER") [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "<" [(.var "SLOT"), (.app "FN2-BOOT-ROWS" [(.var "FN2-BOOT")])]), (.quote Val.nil)]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":BOUNDS"))])]) [(.app "FN2-BOOT-TABLE" [(.var "FN2-CORE")]), (.var "SLOT")]), (.quote (Val.sym ":KIND"))])])])])])])])])])])])])])]) [(.app "FN2-MACHINE-KIND" [(.var "ID"), (.var "FN2-CORE")]), (.var "SLOT"), (.var "FN2-CORE")]) [(.app "FN2-MACHINE-SLOT" [(.var "ID"), (.var "FN2-CORE")]), (.var "FN2-CORE"), (.var "ID")])]) 512 = _
  refine Translation.eval_if (vc := («NOT» («FN2-MACHINE-IDP» «ID» «FN2-CORE»))) (va := (Val.sym ":BOUNDS")) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 0))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-LISTENER-ROWS» («FN2-LISTENER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 1))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 2))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SCRIBE-ROWS» («FN2-SCRIBE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 3))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 4))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 5))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 6))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND")))))))))))))))) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [(«FN2-MACHINE-IDP» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
  ·
    rfl
  ·
    refine Translation.eval_lam (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), «FN2-CORE», «ID»]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            rfl
    ·
      refine Translation.eval_lam (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»), «FN2-CORE»]) ?_ ?_
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 0))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-LISTENER-ROWS» («FN2-LISTENER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 1))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 2))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SCRIBE-ROWS» («FN2-SCRIBE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 3))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 4))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 5))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 6))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND"))))))))))))))) ?_ ?_ ?_
        ·
          refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 0)]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          refine Translation.eval_lam (vs := [(«FN2-LISTENER-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
          ·
            refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-LISTENER-ROWS» («FN2-LISTENER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-LISTENER-ROWS» («FN2-LISTENER-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                ·
                  refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-LISTENER-ROWS» («FN2-LISTENER-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                  ·
                    refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
                  ·
                    refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-LISTENER-ROWS» («FN2-LISTENER-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          refine Translation.eval_app (vs := [(«FN2-LISTENER-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              rfl
                        ·
                          rfl
                  ·
                    rfl
                ·
                  rfl
                ·
                  rfl
              ·
                rfl
            ·
              rfl
        ·
          refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 1))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 2))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SCRIBE-ROWS» («FN2-SCRIBE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 3))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 4))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 5))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 6))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND")))))))))))))) ?_ ?_ ?_
          ·
            refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 1)]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
          ·
            refine Translation.eval_lam (vs := [(«FN2-ECHO-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
            ·
              refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                  ·
                    refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                    ·
                      refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          rfl
                    ·
                      refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            refine Translation.eval_app (vs := [(«FN2-ECHO-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                rfl
                          ·
                            rfl
                    ·
                      rfl
                  ·
                    rfl
                  ·
                    rfl
                ·
                  rfl
              ·
                rfl
          ·
            refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 2))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SCRIBE-ROWS» («FN2-SCRIBE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 3))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 4))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 5))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 6))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND"))))))))))))) ?_ ?_ ?_
            ·
              refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 2)]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
            ·
              refine Translation.eval_lam (vs := [(«FN2-SCRIBE-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
              ·
                refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SCRIBE-ROWS» («FN2-SCRIBE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SCRIBE-ROWS» («FN2-SCRIBE-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                    ·
                      refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SCRIBE-ROWS» («FN2-SCRIBE-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            rfl
                      ·
                        refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-SCRIBE-ROWS» («FN2-SCRIBE-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              refine Translation.eval_app (vs := [(«FN2-SCRIBE-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  rfl
                            ·
                              rfl
                      ·
                        rfl
                    ·
                      rfl
                    ·
                      rfl
                  ·
                    rfl
                ·
                  rfl
            ·
              refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 3))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 4))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 5))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 6))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND")))))))))))) ?_ ?_ ?_
              ·
                refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 3)]) (by decide) (by decide) ?_ (by rfl)
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
              ·
                refine Translation.eval_lam (vs := [(«FN2-COMMIT-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
                ·
                  refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                      ·
                        refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                        ·
                          refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              rfl
                        ·
                          refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-COMMIT-ROWS» («FN2-COMMIT-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                refine Translation.eval_app (vs := [(«FN2-COMMIT-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    rfl
                                  ·
                                    rfl
                              ·
                                rfl
                        ·
                          rfl
                      ·
                        rfl
                      ·
                        rfl
                    ·
                      rfl
                  ·
                    rfl
              ·
                refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 4))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 5))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 6))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND"))))))))))) ?_ ?_ ?_
                ·
                  refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 4)]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
                ·
                  refine Translation.eval_lam (vs := [(«FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
                  ·
                    refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                        ·
                          refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                          ·
                            refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                rfl
                          ·
                            refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-RECOVERY-MACHINE-ROWS» («FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  refine Translation.eval_app (vs := [(«FN2-RECOVERY-MACHINE-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      rfl
                                    ·
                                      rfl
                                ·
                                  rfl
                          ·
                            rfl
                        ·
                          rfl
                        ·
                          rfl
                      ·
                        rfl
                    ·
                      rfl
                ·
                  refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 5))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 6))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND")))))))))) ?_ ?_ ?_
                  ·
                    refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 5)]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          rfl
                  ·
                    refine Translation.eval_lam (vs := [(«FN2-SEALER-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          rfl
                    ·
                      refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                          ·
                            refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                            ·
                              refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  rfl
                            ·
                              refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-SEALER-ROWS» («FN2-SEALER-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    refine Translation.eval_app (vs := [(«FN2-SEALER-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        rfl
                                  ·
                                    rfl
                            ·
                              rfl
                          ·
                            rfl
                          ·
                            rfl
                        ·
                          rfl
                      ·
                        rfl
                  ·
                    refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 6))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND"))))))))) ?_ ?_ ?_
                    ·
                      refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 6)]) (by decide) (by decide) ?_ (by rfl)
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            rfl
                    ·
                      refine Translation.eval_lam (vs := [(«FN2-CONN-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              rfl
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            rfl
                      ·
                        refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                            ·
                              refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                              ·
                                refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    rfl
                                  ·
                                    rfl
                              ·
                                refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-CONN-ROWS» («FN2-CONN-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    rfl
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      refine Translation.eval_app (vs := [(«FN2-CONN-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          rfl
                                        ·
                                          rfl
                                    ·
                                      rfl
                              ·
                                rfl
                            ·
                              rfl
                            ·
                              rfl
                          ·
                            rfl
                        ·
                          rfl
                    ·
                      refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 7))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND")))))))) ?_ ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 7)]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              rfl
                      ·
                        refine Translation.eval_lam (vs := [(«FN2-UPLOAD-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                rfl
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              rfl
                        ·
                          refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                              ·
                                refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                                ·
                                  refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      rfl
                                    ·
                                      rfl
                                ·
                                  refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-UPLOAD-ROWS» («FN2-UPLOAD-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      rfl
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        refine Translation.eval_app (vs := [(«FN2-UPLOAD-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                        ·
                                          refine Translation.eval_args_cons ?_ ?_
                                          ·
                                            rfl
                                          ·
                                            rfl
                                      ·
                                        rfl
                                ·
                                  rfl
                              ·
                                rfl
                              ·
                                rfl
                            ·
                              rfl
                          ·
                            rfl
                      ·
                        refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 8))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND"))))))) ?_ ?_ ?_
                        ·
                          refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 8)]) (by decide) (by decide) ?_ (by rfl)
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                rfl
                        ·
                          refine Translation.eval_lam (vs := [(«FN2-TXN-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  rfl
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                rfl
                          ·
                            refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                                ·
                                  refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                                  ·
                                    refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        rfl
                                  ·
                                    refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-TXN-ROWS» («FN2-TXN-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          refine Translation.eval_app (vs := [(«FN2-TXN-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                          ·
                                            refine Translation.eval_args_cons ?_ ?_
                                            ·
                                              rfl
                                            ·
                                              rfl
                                        ·
                                          rfl
                                  ·
                                    rfl
                                ·
                                  rfl
                                ·
                                  rfl
                              ·
                                rfl
                            ·
                              rfl
                        ·
                          refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 9))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND")))))) ?_ ?_ ?_
                          ·
                            refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 9)]) (by decide) (by decide) ?_ (by rfl)
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  rfl
                          ·
                            refine Translation.eval_lam (vs := [(«FN2-CURSOR-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    rfl
                                  ·
                                    rfl
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  rfl
                            ·
                              refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                                  ·
                                    refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                                    ·
                                      refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          rfl
                                        ·
                                          rfl
                                    ·
                                      refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-CURSOR-ROWS» («FN2-CURSOR-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          rfl
                                        ·
                                          refine Translation.eval_args_cons ?_ ?_
                                          ·
                                            refine Translation.eval_app (vs := [(«FN2-CURSOR-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                            ·
                                              refine Translation.eval_args_cons ?_ ?_
                                              ·
                                                rfl
                                              ·
                                                rfl
                                          ·
                                            rfl
                                    ·
                                      rfl
                                  ·
                                    rfl
                                  ·
                                    rfl
                                ·
                                  rfl
                              ·
                                rfl
                          ·
                            refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 10))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND"))))) ?_ ?_ ?_
                            ·
                              refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 10)]) (by decide) (by decide) ?_ (by rfl)
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    rfl
                                  ·
                                    rfl
                            ·
                              refine Translation.eval_lam (vs := [(«FN2-CTL-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      rfl
                                    ·
                                      rfl
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    rfl
                                  ·
                                    rfl
                              ·
                                refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                                    ·
                                      refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                                      ·
                                        refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                        ·
                                          refine Translation.eval_args_cons ?_ ?_
                                          ·
                                            rfl
                                          ·
                                            rfl
                                      ·
                                        refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-CTL-ROWS» («FN2-CTL-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                                        ·
                                          refine Translation.eval_args_cons ?_ ?_
                                          ·
                                            rfl
                                          ·
                                            refine Translation.eval_args_cons ?_ ?_
                                            ·
                                              refine Translation.eval_app (vs := [(«FN2-CTL-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                              ·
                                                refine Translation.eval_args_cons ?_ ?_
                                                ·
                                                  rfl
                                                ·
                                                  rfl
                                            ·
                                              rfl
                                      ·
                                        rfl
                                    ·
                                      rfl
                                    ·
                                      rfl
                                  ·
                                    rfl
                                ·
                                  rfl
                            ·
                              refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 11))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND")))) ?_ ?_ ?_
                              ·
                                refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 11)]) (by decide) (by decide) ?_ (by rfl)
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    rfl
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      rfl
                                    ·
                                      rfl
                              ·
                                refine Translation.eval_lam (vs := [(«FN2-CNS-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        rfl
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      rfl
                                    ·
                                      rfl
                                ·
                                  refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                                      ·
                                        refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                                        ·
                                          refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                          ·
                                            refine Translation.eval_args_cons ?_ ?_
                                            ·
                                              rfl
                                            ·
                                              rfl
                                        ·
                                          refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-CNS-ROWS» («FN2-CNS-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                                          ·
                                            refine Translation.eval_args_cons ?_ ?_
                                            ·
                                              rfl
                                            ·
                                              refine Translation.eval_args_cons ?_ ?_
                                              ·
                                                refine Translation.eval_app (vs := [(«FN2-CNS-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                                ·
                                                  refine Translation.eval_args_cons ?_ ?_
                                                  ·
                                                    rfl
                                                  ·
                                                    rfl
                                              ·
                                                rfl
                                        ·
                                          rfl
                                      ·
                                        rfl
                                      ·
                                        rfl
                                    ·
                                      rfl
                                  ·
                                    rfl
                              ·
                                refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 12))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (if ((«EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))).truthy then (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS")) else (Val.sym ":KIND"))) ?_ ?_ ?_
                                ·
                                  refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 12)]) (by decide) (by decide) ?_ (by rfl)
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      rfl
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        rfl
                                ·
                                  refine Translation.eval_lam (vs := [(«FN2-AUTH-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          rfl
                                        ·
                                          rfl
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        rfl
                                  ·
                                    refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                                        ·
                                          refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                                          ·
                                            refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                            ·
                                              refine Translation.eval_args_cons ?_ ?_
                                              ·
                                                rfl
                                              ·
                                                rfl
                                          ·
                                            refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-AUTH-ROWS» («FN2-AUTH-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                                            ·
                                              refine Translation.eval_args_cons ?_ ?_
                                              ·
                                                rfl
                                              ·
                                                refine Translation.eval_args_cons ?_ ?_
                                                ·
                                                  refine Translation.eval_app (vs := [(«FN2-AUTH-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                                  ·
                                                    refine Translation.eval_args_cons ?_ ?_
                                                    ·
                                                      rfl
                                                    ·
                                                      rfl
                                                ·
                                                  rfl
                                          ·
                                            rfl
                                        ·
                                          rfl
                                        ·
                                          rfl
                                      ·
                                        rfl
                                    ·
                                      rfl
                                ·
                                  refine Translation.eval_if (vc := («EQL» («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 13))) (va := (if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))) (vb := (Val.sym ":KIND")) ?_ ?_ ?_
                                  ·
                                    refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 13)]) (by decide) (by decide) ?_ (by rfl)
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          rfl
                                        ·
                                          rfl
                                  ·
                                    refine Translation.eval_lam (vs := [(«FN2-BOOT-TABLE» «FN2-CORE»), («FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) ?_ ?_
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
                                        ·
                                          refine Translation.eval_args_cons ?_ ?_
                                          ·
                                            rfl
                                          ·
                                            rfl
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          rfl
                                        ·
                                          rfl
                                    ·
                                      refine Translation.eval_lam (vs := [(if ((if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)).truthy then (Val.sym ":OK") else (Val.sym ":BOUNDS"))]) ?_ ?_
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          refine Translation.eval_if (vc := (if ((«NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))).truthy then (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))) else Val.nil)) (va := (Val.sym ":OK")) (vb := (Val.sym ":BOUNDS")) ?_ ?_ ?_
                                          ·
                                            refine Translation.eval_if (vc := («NATP» («FN2-MACHINE-SLOT» «ID» «FN2-CORE»))) (va := (Prim.lt («FN2-MACHINE-SLOT» «ID» «FN2-CORE») («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                                            ·
                                              refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                              ·
                                                refine Translation.eval_args_cons ?_ ?_
                                                ·
                                                  rfl
                                                ·
                                                  rfl
                                            ·
                                              refine Translation.eval_app (vs := [(«FN2-MACHINE-SLOT» «ID» «FN2-CORE»), («FN2-BOOT-ROWS» («FN2-BOOT-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                                              ·
                                                refine Translation.eval_args_cons ?_ ?_
                                                ·
                                                  rfl
                                                ·
                                                  refine Translation.eval_args_cons ?_ ?_
                                                  ·
                                                    refine Translation.eval_app (vs := [(«FN2-BOOT-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                                                    ·
                                                      refine Translation.eval_args_cons ?_ ?_
                                                      ·
                                                        rfl
                                                      ·
                                                        rfl
                                                  ·
                                                    rfl
                                            ·
                                              rfl
                                          ·
                                            rfl
                                          ·
                                            rfl
                                        ·
                                          rfl
                                      ·
                                        rfl
                                  ·
                                    rfl
theorem «FN2-MACHINE-PHASE-READ-CODE».canonical_body («ID» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-MACHINE-PHASE-READ-CODE».canonicalBody fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-MACHINE-PHASE-READ-CODE».decoded]
  exact «FN2-MACHINE-PHASE-READ-CODE».export_body «ID» «FN2-CORE»

def «FN2-ECHO-SNAPSHOT-READ-CODE».canonicalBody : Translation.Object := (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [67, 79, 68, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 79, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81]) (.cons (.symbol [65, 67, 76, 50] [67, 79, 68, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [67, 79, 68, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81, 85, 65, 76]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 75, 73, 78, 68]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [75, 73, 78, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 45, 80, 72, 65, 83, 69, 45, 82, 69, 65, 68, 45, 67, 79, 68, 69]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-ECHO-SNAPSHOT-READ-CODE».body : Term := (.lam ["CODE", "FN2-CORE", "ID"] (.app "IF" [(.app "NOT" [(.app "EQ" [(.var "CODE"), (.quote (Val.sym ":OK"))])]), (.var "CODE"), (.app "IF" [(.app "EQUAL" [(.app "FN2-MACHINE-KIND" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.int 1))]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":KIND"))])]) [(.app "FN2-MACHINE-PHASE-READ-CODE" [(.var "ID"), (.var "FN2-CORE")]), (.var "FN2-CORE"), (.var "ID")])
theorem «FN2-ECHO-SNAPSHOT-READ-CODE».decoded : Translation.readTerm 512 «FN2-ECHO-SNAPSHOT-READ-CODE».canonicalBody = some «FN2-ECHO-SNAPSHOT-READ-CODE».body := by rfl
theorem «FN2-ECHO-SNAPSHOT-READ-CODE».export_body («ID» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] «FN2-ECHO-SNAPSHOT-READ-CODE».body 512 = .ok («FN2-ECHO-SNAPSHOT-READ-CODE» «ID» «FN2-CORE») := by
  change Translation.eval fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] (.lam ["CODE", "FN2-CORE", "ID"] (.app "IF" [(.app "NOT" [(.app "EQ" [(.var "CODE"), (.quote (Val.sym ":OK"))])]), (.var "CODE"), (.app "IF" [(.app "EQUAL" [(.app "FN2-MACHINE-KIND" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.int 1))]), (.quote (Val.sym ":OK")), (.quote (Val.sym ":KIND"))])]) [(.app "FN2-MACHINE-PHASE-READ-CODE" [(.var "ID"), (.var "FN2-CORE")]), (.var "FN2-CORE"), (.var "ID")]) 512 = _
  refine Translation.eval_lam (vs := [(«FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE»), «FN2-CORE», «ID»]) ?_ ?_
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
  ·
    refine Translation.eval_if (vc := («NOT» («EQ» («FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE») (Val.sym ":OK")))) (va := («FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE»)) (vb := (if ((Prim.equal («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 1))).truthy then (Val.sym ":OK") else (Val.sym ":KIND"))) ?_ ?_ ?_
    ·
      refine Translation.eval_app (vs := [(«EQ» («FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE») (Val.sym ":OK"))]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [(«FN2-MACHINE-PHASE-READ-CODE» «ID» «FN2-CORE»), (Val.sym ":OK")]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
        ·
          rfl
    ·
      rfl
    ·
      refine Translation.eval_if (vc := (Prim.equal («FN2-MACHINE-KIND» «ID» «FN2-CORE») (Val.int 1))) (va := (Val.sym ":OK")) (vb := (Val.sym ":KIND")) ?_ ?_ ?_
      ·
        refine Translation.eval_app (vs := [(«FN2-MACHINE-KIND» «ID» «FN2-CORE»), (Val.int 1)]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-SNAPSHOT-READ-CODE».canonical_body («ID» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-ECHO-SNAPSHOT-READ-CODE».canonicalBody fns [("ID", «ID»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-ECHO-SNAPSHOT-READ-CODE» «ID» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-ECHO-SNAPSHOT-READ-CODE».decoded]
  exact «FN2-ECHO-SNAPSHOT-READ-CODE».export_body «ID» «FN2-CORE»

def «FN2-ECHO-RUN-FREE».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [69, 81]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 83, 78, 65, 80, 83, 72, 79, 84, 45, 82, 69, 65, 68, 45, 67, 79, 68, 69]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [66, 85, 68, 71, 69, 84]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [66, 89, 84, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [83, 84, 69, 80, 83]) (.cons (.symbol [65, 67, 76, 50] [68, 69, 83, 67, 82, 73, 80, 84, 79, 82, 83]) (.cons (.symbol [65, 67, 76, 50] [82, 85, 78, 78, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [82, 85, 78, 78, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [68, 69, 83, 67, 82, 73, 80, 84, 79, 82, 83]) (.cons (.symbol [65, 67, 76, 50] [83, 84, 69, 80, 83]) (.cons (.symbol [65, 67, 76, 50] [66, 89, 84, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [66, 89, 84, 69, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [83, 84, 69, 80, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [68, 69, 83, 67, 82, 73, 80, 84, 79, 82, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [82, 85, 78, 78, 65, 66, 76, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [85, 80, 68, 65, 84, 69, 45, 70, 78, 50, 45, 67, 79, 82, 69, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [82, 85, 78, 78, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [68, 69, 83, 67, 82, 73, 80, 84, 79, 82, 83]) (.cons (.symbol [65, 67, 76, 50] [83, 84, 69, 80, 83]) (.cons (.symbol [65, 67, 76, 50] [66, 89, 84, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (2)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (3)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (4)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [66, 85, 68, 71, 69, 84]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [66, 89, 84, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [83, 84, 69, 80, 83]) (.cons (.symbol [65, 67, 76, 50] [68, 69, 83, 67, 82, 73, 80, 84, 79, 82, 83]) (.cons (.symbol [65, 67, 76, 50] [82, 85, 78, 78, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [66, 89, 84, 69, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [83, 84, 69, 80, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [68, 69, 83, 67, 82, 73, 80, 84, 79, 82, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [82, 85, 78, 78, 65, 66, 76, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (2)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [77, 86, 45, 78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (3)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [77, 86]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 82, 85, 78, 45, 70, 82, 69, 69, 45, 67, 72, 73, 76, 68, 82, 69, 78]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [83, 76, 79, 84]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [66, 85, 68, 71, 69, 84]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))))))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76, 45, 82, 69, 67, 79, 82, 68, 45, 83, 84, 79, 80]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (15)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [73, 70]) (.cons (.cons (.symbol [65, 67, 76, 50] [78, 65, 84, 80]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [60]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 82, 79, 87, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 83, 76, 79, 84]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (4294967295)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [66, 85, 68, 71, 69, 84]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 84, 65, 66, 76, 69]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69, 45, 67, 79, 78, 84, 82, 79, 76]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.symbol [65, 67, 76, 50] [66, 85, 68, 71, 69, 84]) (.cons (.symbol [65, 67, 76, 50] [73, 68]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))))) (.cons (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [67, 79, 78, 83]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69, 45, 83, 84, 79, 80]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (15)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 67, 79, 82, 69]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))))
def «FN2-ECHO-RUN-FREE».body : Term := (.app "IF" [(.app "EQ" [(.app "FN2-ECHO-SNAPSHOT-READ-CODE" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK"))]), (.lam ["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL", "FN2-CORE", "BUDGET", "ID"] (.lam ["MV", "FN2-CORE"] (.lam ["BYTES", "STEPS", "DESCRIPTORS", "RUNNABLE", "FN2-CONTROL", "FN2-CORE"] (.lam ["FN2-CORE", "RUNNABLE", "DESCRIPTORS", "STEPS", "BYTES"] (.app "CONS" [(.var "BYTES"), (.app "CONS" [(.var "STEPS"), (.app "CONS" [(.var "DESCRIPTORS"), (.app "CONS" [(.var "RUNNABLE"), (.app "CONS" [(.var "FN2-CORE"), (.quote Val.nil)])])])])]) [(.app "UPDATE-FN2-CORE-CONTROL" [(.var "FN2-CONTROL"), (.var "FN2-CORE")]), (.var "RUNNABLE"), (.var "DESCRIPTORS"), (.var "STEPS"), (.var "BYTES")]) [(.app "MV-NTH" [(.quote (Val.int 0)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 1)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 2)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 3)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 4)), (.var "MV")]), (.var "FN2-CORE")]) [(.lam ["SLOT", "FN2-CONTROL", "BUDGET", "FN2-MACHINES", "ID", "FN2-ECHO"] (.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "IF" [(.app "<" [(.var "SLOT"), (.app "FN2-ECHO-ROWS" [(.var "FN2-ECHO")])]), (.app "IF" [(.app "NATP" [(.var "ID")]), (.app "<" [(.var "ID"), (.app "FN2-MACHINES-ROWS" [(.var "FN2-MACHINES")])]), (.quote Val.nil)]), (.quote Val.nil)]), (.quote Val.nil)]), (.lam ["MV", "FN2-CONTROL"] (.lam ["BYTES", "STEPS", "DESCRIPTORS", "RUNNABLE", "FN2-CONTROL"] (.app "CONS" [(.var "BYTES"), (.app "CONS" [(.var "STEPS"), (.app "CONS" [(.var "DESCRIPTORS"), (.app "CONS" [(.var "RUNNABLE"), (.app "CONS" [(.var "FN2-CONTROL"), (.quote Val.nil)])])])])]) [(.app "MV-NTH" [(.quote (Val.int 0)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 1)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 2)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 3)), (.var "MV")]), (.var "FN2-CONTROL")]) [(.app "FN2-ECHO-RUN-FREE-CHILDREN" [(.var "ID"), (.var "SLOT"), (.quote (Val.int 1)), (.quote (Val.int 0)), (.var "BUDGET"), (.var "FN2-ECHO"), (.var "FN2-MACHINES")]), (.var "FN2-CONTROL")]), (.lam ["FN2-CONTROL"] (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote (Val.int 1)), (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote Val.nil), (.app "CONS" [(.var "FN2-CONTROL"), (.quote Val.nil)])])])])]) [(.app "FN2-CONTROL-RECORD-STOP" [(.quote (Val.int 15)), (.var "FN2-CONTROL")])])]) [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "ID")]), (.app "<" [(.var "ID"), (.app "FN2-MACHINES-ROWS" [(.var "FN2-MACHINES")])]), (.quote Val.nil)]), (.app "FN2-MACHINES-SLOT" [(.var "ID"), (.var "FN2-MACHINES")]), (.quote (Val.int 4294967295))]), (.var "FN2-CONTROL"), (.var "BUDGET"), (.var "FN2-MACHINES"), (.var "ID"), (.var "FN2-ECHO")]), (.var "FN2-CORE")]) [(.app "FN2-ECHO-TABLE" [(.var "FN2-CORE")]), (.app "FN2-CORE-MACHINES" [(.var "FN2-CORE")]), (.app "FN2-CORE-CONTROL" [(.var "FN2-CORE")]), (.var "FN2-CORE"), (.var "BUDGET"), (.var "ID")]), (.lam ["FN2-CORE"] (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote (Val.int 1)), (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote Val.nil), (.app "CONS" [(.var "FN2-CORE"), (.quote Val.nil)])])])])]) [(.app "FN2-CORE-STOP" [(.quote (Val.int 15)), (.var "FN2-CORE")])])])
theorem «FN2-ECHO-RUN-FREE».decoded : Translation.readTerm 512 «FN2-ECHO-RUN-FREE».canonicalBody = some «FN2-ECHO-RUN-FREE».body := by rfl
theorem «FN2-ECHO-RUN-FREE».export_body («ID» : Val) («BUDGET» : Val) («FN2-CORE» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("ID", «ID»), ("BUDGET", «BUDGET»), ("FN2-CORE", «FN2-CORE»)] «FN2-ECHO-RUN-FREE».body 512 = .ok («FN2-ECHO-RUN-FREE» «ID» «BUDGET» «FN2-CORE») := by
  change Translation.eval fns [("ID", «ID»), ("BUDGET", «BUDGET»), ("FN2-CORE", «FN2-CORE»)] (.app "IF" [(.app "EQ" [(.app "FN2-ECHO-SNAPSHOT-READ-CODE" [(.var "ID"), (.var "FN2-CORE")]), (.quote (Val.sym ":OK"))]), (.lam ["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL", "FN2-CORE", "BUDGET", "ID"] (.lam ["MV", "FN2-CORE"] (.lam ["BYTES", "STEPS", "DESCRIPTORS", "RUNNABLE", "FN2-CONTROL", "FN2-CORE"] (.lam ["FN2-CORE", "RUNNABLE", "DESCRIPTORS", "STEPS", "BYTES"] (.app "CONS" [(.var "BYTES"), (.app "CONS" [(.var "STEPS"), (.app "CONS" [(.var "DESCRIPTORS"), (.app "CONS" [(.var "RUNNABLE"), (.app "CONS" [(.var "FN2-CORE"), (.quote Val.nil)])])])])]) [(.app "UPDATE-FN2-CORE-CONTROL" [(.var "FN2-CONTROL"), (.var "FN2-CORE")]), (.var "RUNNABLE"), (.var "DESCRIPTORS"), (.var "STEPS"), (.var "BYTES")]) [(.app "MV-NTH" [(.quote (Val.int 0)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 1)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 2)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 3)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 4)), (.var "MV")]), (.var "FN2-CORE")]) [(.lam ["SLOT", "FN2-CONTROL", "BUDGET", "FN2-MACHINES", "ID", "FN2-ECHO"] (.app "IF" [(.app "IF" [(.app "NATP" [(.var "SLOT")]), (.app "IF" [(.app "<" [(.var "SLOT"), (.app "FN2-ECHO-ROWS" [(.var "FN2-ECHO")])]), (.app "IF" [(.app "NATP" [(.var "ID")]), (.app "<" [(.var "ID"), (.app "FN2-MACHINES-ROWS" [(.var "FN2-MACHINES")])]), (.quote Val.nil)]), (.quote Val.nil)]), (.quote Val.nil)]), (.lam ["MV", "FN2-CONTROL"] (.lam ["BYTES", "STEPS", "DESCRIPTORS", "RUNNABLE", "FN2-CONTROL"] (.app "CONS" [(.var "BYTES"), (.app "CONS" [(.var "STEPS"), (.app "CONS" [(.var "DESCRIPTORS"), (.app "CONS" [(.var "RUNNABLE"), (.app "CONS" [(.var "FN2-CONTROL"), (.quote Val.nil)])])])])]) [(.app "MV-NTH" [(.quote (Val.int 0)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 1)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 2)), (.var "MV")]), (.app "MV-NTH" [(.quote (Val.int 3)), (.var "MV")]), (.var "FN2-CONTROL")]) [(.app "FN2-ECHO-RUN-FREE-CHILDREN" [(.var "ID"), (.var "SLOT"), (.quote (Val.int 1)), (.quote (Val.int 0)), (.var "BUDGET"), (.var "FN2-ECHO"), (.var "FN2-MACHINES")]), (.var "FN2-CONTROL")]), (.lam ["FN2-CONTROL"] (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote (Val.int 1)), (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote Val.nil), (.app "CONS" [(.var "FN2-CONTROL"), (.quote Val.nil)])])])])]) [(.app "FN2-CONTROL-RECORD-STOP" [(.quote (Val.int 15)), (.var "FN2-CONTROL")])])]) [(.app "IF" [(.app "IF" [(.app "NATP" [(.var "ID")]), (.app "<" [(.var "ID"), (.app "FN2-MACHINES-ROWS" [(.var "FN2-MACHINES")])]), (.quote Val.nil)]), (.app "FN2-MACHINES-SLOT" [(.var "ID"), (.var "FN2-MACHINES")]), (.quote (Val.int 4294967295))]), (.var "FN2-CONTROL"), (.var "BUDGET"), (.var "FN2-MACHINES"), (.var "ID"), (.var "FN2-ECHO")]), (.var "FN2-CORE")]) [(.app "FN2-ECHO-TABLE" [(.var "FN2-CORE")]), (.app "FN2-CORE-MACHINES" [(.var "FN2-CORE")]), (.app "FN2-CORE-CONTROL" [(.var "FN2-CORE")]), (.var "FN2-CORE"), (.var "BUDGET"), (.var "ID")]), (.lam ["FN2-CORE"] (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote (Val.int 1)), (.app "CONS" [(.quote (Val.int 0)), (.app "CONS" [(.quote Val.nil), (.app "CONS" [(.var "FN2-CORE"), (.quote Val.nil)])])])])]) [(.app "FN2-CORE-STOP" [(.quote (Val.int 15)), (.var "FN2-CORE")])])]) 512 = _
  refine Translation.eval_if (vc := («EQ» («FN2-ECHO-SNAPSHOT-READ-CODE» «ID» «FN2-CORE») (Val.sym ":OK"))) (va := (Val.cons (Native.nth (Val.int 0) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons (Native.nth (Val.int 1) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons (Native.nth (Val.int 2) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons (Native.nth (Val.int 3) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons («UPDATE-FN2-CORE-CONTROL» (Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) «FN2-CORE») Val.nil)))))) (vb := (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CORE-STOP» (Val.int 15) «FN2-CORE») Val.nil)))))) ?_ ?_ ?_
  ·
    refine Translation.eval_app (vs := [(«FN2-ECHO-SNAPSHOT-READ-CODE» «ID» «FN2-CORE»), (Val.sym ":OK")]) (by decide) (by decide) ?_ (by rfl)
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«ID», «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          rfl
  ·
    refine Translation.eval_lam (vs := [(«FN2-ECHO-TABLE» «FN2-CORE»), («FN2-CORE-MACHINES» «FN2-CORE»), («FN2-CORE-CONTROL» «FN2-CORE»), «FN2-CORE», «BUDGET», «ID»]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            rfl
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            refine Translation.eval_app (vs := [«FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
    ·
      refine Translation.eval_lam (vs := [(if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil)))))), «FN2-CORE»]) ?_ ?_
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          refine Translation.eval_lam (vs := [(if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)), («FN2-CORE-CONTROL» «FN2-CORE»), «BUDGET», («FN2-CORE-MACHINES» «FN2-CORE»), «ID», («FN2-ECHO-TABLE» «FN2-CORE»)]) ?_ ?_
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_if (vc := (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)) (va := («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»))) (vb := (Val.int 4294967295)) ?_ ?_ ?_
              ·
                refine Translation.eval_if (vc := («NATP» «ID»)) (va := (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                ·
                  refine Translation.eval_app (vs := [«ID»]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
                ·
                  refine Translation.eval_app (vs := [«ID», («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [(«FN2-CORE-MACHINES» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            rfl
                      ·
                        rfl
                ·
                  rfl
              ·
                refine Translation.eval_app (vs := [«ID», («FN2-CORE-MACHINES» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
              ·
                rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
          ·
            refine Translation.eval_if (vc := (if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)) (va := (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil)))))) (vb := (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil)))))) ?_ ?_ ?_
            ·
              refine Translation.eval_if (vc := («NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))) (va := (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil)) (vb := Val.nil) ?_ ?_ ?_
              ·
                refine Translation.eval_app (vs := [(if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295))]) (by decide) (by decide) ?_ (by rfl)
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
              ·
                refine Translation.eval_if (vc := (Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))) (va := (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)) (vb := Val.nil) ?_ ?_ ?_
                ·
                  refine Translation.eval_app (vs := [(if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)), («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [(«FN2-ECHO-TABLE» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            rfl
                      ·
                        rfl
                ·
                  refine Translation.eval_if (vc := («NATP» «ID»)) (va := (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»)))) (vb := Val.nil) ?_ ?_ ?_
                  ·
                    refine Translation.eval_app (vs := [«ID»]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
                  ·
                    refine Translation.eval_app (vs := [«ID», («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          refine Translation.eval_app (vs := [(«FN2-CORE-MACHINES» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              rfl
                        ·
                          rfl
                  ·
                    rfl
                ·
                  rfl
              ·
                rfl
            ·
              refine Translation.eval_lam (vs := [(«FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»)), («FN2-CORE-CONTROL» «FN2-CORE»)]) ?_ ?_
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  refine Translation.eval_app (vs := [«ID», (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)), (Val.int 1), (Val.int 0), «BUDGET», («FN2-ECHO-TABLE» «FN2-CORE»), («FN2-CORE-MACHINES» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
              ·
                refine Translation.eval_lam (vs := [(Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))), (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))), (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))), (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))), («FN2-CORE-CONTROL» «FN2-CORE»)]) ?_ ?_
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    refine Translation.eval_app (vs := [(Val.int 0), («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      refine Translation.eval_app (vs := [(Val.int 1), («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [(Val.int 2), («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          refine Translation.eval_app (vs := [(Val.int 3), («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))]) (by decide) (by decide) ?_ (by rfl)
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              rfl
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                rfl
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            rfl
                ·
                  refine Translation.eval_app (vs := [(Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))), (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [(Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))), (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil)))]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              refine Translation.eval_app (vs := [(Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))), (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))]) (by decide) (by decide) ?_ (by rfl)
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    refine Translation.eval_app (vs := [(Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))), (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil)]) (by decide) (by decide) ?_ (by rfl)
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          refine Translation.eval_app (vs := [(«FN2-CORE-CONTROL» «FN2-CORE»), Val.nil]) (by decide) (by decide) ?_ (by rfl)
                                          ·
                                            refine Translation.eval_args_cons ?_ ?_
                                            ·
                                              rfl
                                            ·
                                              refine Translation.eval_args_cons ?_ ?_
                                              ·
                                                rfl
                                              ·
                                                rfl
                                        ·
                                          rfl
                                  ·
                                    rfl
                            ·
                              rfl
                      ·
                        rfl
            ·
              refine Translation.eval_lam (vs := [(«FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»))]) ?_ ?_
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  refine Translation.eval_app (vs := [(Val.int 15), («FN2-CORE-CONTROL» «FN2-CORE»)]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
                ·
                  rfl
              ·
                refine Translation.eval_app (vs := [(Val.int 0), (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))]) (by decide) (by decide) ?_ (by rfl)
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      refine Translation.eval_app (vs := [(Val.int 1), (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil)))]) (by decide) (by decide) ?_ (by rfl)
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            refine Translation.eval_app (vs := [(Val.int 0), (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))]) (by decide) (by decide) ?_ (by rfl)
                            ·
                              refine Translation.eval_args_cons ?_ ?_
                              ·
                                rfl
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  refine Translation.eval_app (vs := [Val.nil, (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil)]) (by decide) (by decide) ?_ (by rfl)
                                  ·
                                    refine Translation.eval_args_cons ?_ ?_
                                    ·
                                      rfl
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        refine Translation.eval_app (vs := [(«FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)), Val.nil]) (by decide) (by decide) ?_ (by rfl)
                                        ·
                                          refine Translation.eval_args_cons ?_ ?_
                                          ·
                                            rfl
                                          ·
                                            refine Translation.eval_args_cons ?_ ?_
                                            ·
                                              rfl
                                            ·
                                              rfl
                                      ·
                                        rfl
                                ·
                                  rfl
                          ·
                            rfl
                    ·
                      rfl
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            rfl
      ·
        refine Translation.eval_lam (vs := [(Native.nth (Val.int 0) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Native.nth (Val.int 1) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Native.nth (Val.int 2) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Native.nth (Val.int 3) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), «FN2-CORE»]) ?_ ?_
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            refine Translation.eval_app (vs := [(Val.int 0), (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [(Val.int 1), (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                refine Translation.eval_app (vs := [(Val.int 2), (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))]) (by decide) (by decide) ?_ (by rfl)
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  refine Translation.eval_app (vs := [(Val.int 3), (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    refine Translation.eval_app (vs := [(Val.int 4), (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))]) (by decide) (by decide) ?_ (by rfl)
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        rfl
                      ·
                        refine Translation.eval_args_cons ?_ ?_
                        ·
                          rfl
                        ·
                          rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
        ·
          refine Translation.eval_lam (vs := [(«UPDATE-FN2-CORE-CONTROL» (Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) «FN2-CORE»), (Native.nth (Val.int 3) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Native.nth (Val.int 2) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Native.nth (Val.int 1) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Native.nth (Val.int 0) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil)))))))]) ?_ ?_
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              refine Translation.eval_app (vs := [(Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    rfl
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  rfl
                ·
                  refine Translation.eval_args_cons ?_ ?_
                  ·
                    rfl
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      rfl
          ·
            refine Translation.eval_app (vs := [(Native.nth (Val.int 0) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Val.cons (Native.nth (Val.int 1) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons (Native.nth (Val.int 2) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons (Native.nth (Val.int 3) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons («UPDATE-FN2-CORE-CONTROL» (Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) «FN2-CORE») Val.nil))))]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  refine Translation.eval_app (vs := [(Native.nth (Val.int 1) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Val.cons (Native.nth (Val.int 2) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons (Native.nth (Val.int 3) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons («UPDATE-FN2-CORE-CONTROL» (Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) «FN2-CORE») Val.nil)))]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [(Native.nth (Val.int 2) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Val.cons (Native.nth (Val.int 3) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) (Val.cons («UPDATE-FN2-CORE-CONTROL» (Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) «FN2-CORE») Val.nil))]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              refine Translation.eval_app (vs := [(Native.nth (Val.int 3) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))), (Val.cons («UPDATE-FN2-CORE-CONTROL» (Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) «FN2-CORE») Val.nil)]) (by decide) (by decide) ?_ (by rfl)
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    refine Translation.eval_app (vs := [(«UPDATE-FN2-CORE-CONTROL» (Native.nth (Val.int 4) (if ((if ((«NATP» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)))).truthy then (if ((Prim.lt (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) («FN2-ECHO-ROWS» («FN2-ECHO-TABLE» «FN2-CORE»)))).truthy then (if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil) else Val.nil) else Val.nil)).truthy then (Val.cons (Native.nth (Val.int 0) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 1) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 2) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons (Native.nth (Val.int 3) («FN2-ECHO-RUN-FREE-CHILDREN» «ID» (if ((if ((«NATP» «ID»)).truthy then (Prim.lt «ID» («FN2-MACHINES-ROWS» («FN2-CORE-MACHINES» «FN2-CORE»))) else Val.nil)).truthy then («FN2-MACHINES-SLOT» «ID» («FN2-CORE-MACHINES» «FN2-CORE»)) else (Val.int 4294967295)) (Val.int 1) (Val.int 0) «BUDGET» («FN2-ECHO-TABLE» «FN2-CORE») («FN2-CORE-MACHINES» «FN2-CORE»))) (Val.cons («FN2-CORE-CONTROL» «FN2-CORE») Val.nil))))) else (Val.cons (Val.int 0) (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CONTROL-RECORD-STOP» (Val.int 15) («FN2-CORE-CONTROL» «FN2-CORE»)) Val.nil))))))) «FN2-CORE»), Val.nil]) (by decide) (by decide) ?_ (by rfl)
                                    ·
                                      refine Translation.eval_args_cons ?_ ?_
                                      ·
                                        rfl
                                      ·
                                        refine Translation.eval_args_cons ?_ ?_
                                        ·
                                          rfl
                                        ·
                                          rfl
                                  ·
                                    rfl
                            ·
                              rfl
                      ·
                        rfl
                ·
                  rfl
  ·
    refine Translation.eval_lam (vs := [(«FN2-CORE-STOP» (Val.int 15) «FN2-CORE»)]) ?_ ?_
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 15), «FN2-CORE»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
    ·
      refine Translation.eval_app (vs := [(Val.int 0), (Val.cons (Val.int 1) (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CORE-STOP» (Val.int 15) «FN2-CORE») Val.nil))))]) (by decide) (by decide) ?_ (by rfl)
      ·
        refine Translation.eval_args_cons ?_ ?_
        ·
          rfl
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            refine Translation.eval_app (vs := [(Val.int 1), (Val.cons (Val.int 0) (Val.cons Val.nil (Val.cons («FN2-CORE-STOP» (Val.int 15) «FN2-CORE») Val.nil)))]) (by decide) (by decide) ?_ (by rfl)
            ·
              refine Translation.eval_args_cons ?_ ?_
              ·
                rfl
              ·
                refine Translation.eval_args_cons ?_ ?_
                ·
                  refine Translation.eval_app (vs := [(Val.int 0), (Val.cons Val.nil (Val.cons («FN2-CORE-STOP» (Val.int 15) «FN2-CORE») Val.nil))]) (by decide) (by decide) ?_ (by rfl)
                  ·
                    refine Translation.eval_args_cons ?_ ?_
                    ·
                      rfl
                    ·
                      refine Translation.eval_args_cons ?_ ?_
                      ·
                        refine Translation.eval_app (vs := [Val.nil, (Val.cons («FN2-CORE-STOP» (Val.int 15) «FN2-CORE») Val.nil)]) (by decide) (by decide) ?_ (by rfl)
                        ·
                          refine Translation.eval_args_cons ?_ ?_
                          ·
                            rfl
                          ·
                            refine Translation.eval_args_cons ?_ ?_
                            ·
                              refine Translation.eval_app (vs := [(«FN2-CORE-STOP» (Val.int 15) «FN2-CORE»), Val.nil]) (by decide) (by decide) ?_ (by rfl)
                              ·
                                refine Translation.eval_args_cons ?_ ?_
                                ·
                                  rfl
                                ·
                                  refine Translation.eval_args_cons ?_ ?_
                                  ·
                                    rfl
                                  ·
                                    rfl
                            ·
                              rfl
                      ·
                        rfl
                ·
                  rfl
          ·
            rfl
theorem «FN2-ECHO-RUN-FREE».canonical_body («ID» : Val) («BUDGET» : Val) («FN2-CORE» : Val) :
    Translation.evalExport 512 «FN2-ECHO-RUN-FREE».canonicalBody fns [("ID", «ID»), ("BUDGET", «BUDGET»), ("FN2-CORE", «FN2-CORE»)] = .ok («FN2-ECHO-RUN-FREE» «ID» «BUDGET» «FN2-CORE») := by
  simp only [Translation.evalExport, «FN2-ECHO-RUN-FREE».decoded]
  exact «FN2-ECHO-RUN-FREE».export_body «ID» «BUDGET» «FN2-CORE»

def «FN2-ECHO-PHASE$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (0)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-PHASE$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 0)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-PHASE$AI».decoded : Translation.readTerm 512 «FN2-ECHO-PHASE$AI».canonicalBody = some «FN2-ECHO-PHASE$AI».body := by rfl
theorem «FN2-ECHO-PHASE$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-PHASE$AI».body 512 = .ok («FN2-ECHO-PHASE$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 0)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 0) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 0), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-PHASE$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-PHASE$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-PHASE$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-PHASE$AI».decoded]
  exact «FN2-ECHO-PHASE$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-PHASE».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 80, 72, 65, 83, 69, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-PHASE».body : Term := (.app "FN2-ECHO-PHASE$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-PHASE».decoded : Translation.readTerm 512 «FN2-ECHO-PHASE».canonicalBody = some «FN2-ECHO-PHASE».body := by rfl
theorem «FN2-ECHO-PHASE».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-PHASE».body 512 = .ok («FN2-ECHO-PHASE» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-PHASE$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-PHASE».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-PHASE».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-PHASE» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-PHASE».decoded]
  exact «FN2-ECHO-PHASE».export_body «I» «FN2-ECHO»

def «FN2-ECHO-GENERATION$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-GENERATION$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 1)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-GENERATION$AI».decoded : Translation.readTerm 512 «FN2-ECHO-GENERATION$AI».canonicalBody = some «FN2-ECHO-GENERATION$AI».body := by rfl
theorem «FN2-ECHO-GENERATION$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-GENERATION$AI».body 512 = .ok («FN2-ECHO-GENERATION$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 1)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 1) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 1), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-GENERATION$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-GENERATION$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-GENERATION$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-GENERATION$AI».decoded]
  exact «FN2-ECHO-GENERATION$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-GENERATION».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 71, 69, 78, 69, 82, 65, 84, 73, 79, 78, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-GENERATION».body : Term := (.app "FN2-ECHO-GENERATION$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-GENERATION».decoded : Translation.readTerm 512 «FN2-ECHO-GENERATION».canonicalBody = some «FN2-ECHO-GENERATION».body := by rfl
theorem «FN2-ECHO-GENERATION».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-GENERATION».body 512 = .ok («FN2-ECHO-GENERATION» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-GENERATION$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-GENERATION».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-GENERATION».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-GENERATION» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-GENERATION».decoded]
  exact «FN2-ECHO-GENERATION».export_body «I» «FN2-ECHO»

def «FN2-ECHO-PRINCIPAL-SLOT$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (2)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-PRINCIPAL-SLOT$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 2)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-PRINCIPAL-SLOT$AI».decoded : Translation.readTerm 512 «FN2-ECHO-PRINCIPAL-SLOT$AI».canonicalBody = some «FN2-ECHO-PRINCIPAL-SLOT$AI».body := by rfl
theorem «FN2-ECHO-PRINCIPAL-SLOT$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-PRINCIPAL-SLOT$AI».body 512 = .ok («FN2-ECHO-PRINCIPAL-SLOT$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 2)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 2) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 2), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-PRINCIPAL-SLOT$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-PRINCIPAL-SLOT$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-PRINCIPAL-SLOT$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-PRINCIPAL-SLOT$AI».decoded]
  exact «FN2-ECHO-PRINCIPAL-SLOT$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-PRINCIPAL-SLOT».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 80, 82, 73, 78, 67, 73, 80, 65, 76, 45, 83, 76, 79, 84, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-PRINCIPAL-SLOT».body : Term := (.app "FN2-ECHO-PRINCIPAL-SLOT$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-PRINCIPAL-SLOT».decoded : Translation.readTerm 512 «FN2-ECHO-PRINCIPAL-SLOT».canonicalBody = some «FN2-ECHO-PRINCIPAL-SLOT».body := by rfl
theorem «FN2-ECHO-PRINCIPAL-SLOT».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-PRINCIPAL-SLOT».body 512 = .ok («FN2-ECHO-PRINCIPAL-SLOT» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-PRINCIPAL-SLOT$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-PRINCIPAL-SLOT».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-PRINCIPAL-SLOT».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-PRINCIPAL-SLOT» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-PRINCIPAL-SLOT».decoded]
  exact «FN2-ECHO-PRINCIPAL-SLOT».export_body «I» «FN2-ECHO»

def «FN2-ECHO-ACCOUNT-REF$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (3)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-ACCOUNT-REF$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 3)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-ACCOUNT-REF$AI».decoded : Translation.readTerm 512 «FN2-ECHO-ACCOUNT-REF$AI».canonicalBody = some «FN2-ECHO-ACCOUNT-REF$AI».body := by rfl
theorem «FN2-ECHO-ACCOUNT-REF$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-ACCOUNT-REF$AI».body 512 = .ok («FN2-ECHO-ACCOUNT-REF$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 3)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 3) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 3), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-ACCOUNT-REF$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-ACCOUNT-REF$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-ACCOUNT-REF$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-ACCOUNT-REF$AI».decoded]
  exact «FN2-ECHO-ACCOUNT-REF$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-ACCOUNT-REF».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 65, 67, 67, 79, 85, 78, 84, 45, 82, 69, 70, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-ACCOUNT-REF».body : Term := (.app "FN2-ECHO-ACCOUNT-REF$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-ACCOUNT-REF».decoded : Translation.readTerm 512 «FN2-ECHO-ACCOUNT-REF».canonicalBody = some «FN2-ECHO-ACCOUNT-REF».body := by rfl
theorem «FN2-ECHO-ACCOUNT-REF».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-ACCOUNT-REF».body 512 = .ok («FN2-ECHO-ACCOUNT-REF» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-ACCOUNT-REF$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-ACCOUNT-REF».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-ACCOUNT-REF».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-ACCOUNT-REF» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-ACCOUNT-REF».decoded]
  exact «FN2-ECHO-ACCOUNT-REF».export_body «I» «FN2-ECHO»

def «FN2-ECHO-DEADLINE$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (4)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-DEADLINE$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 4)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-DEADLINE$AI».decoded : Translation.readTerm 512 «FN2-ECHO-DEADLINE$AI».canonicalBody = some «FN2-ECHO-DEADLINE$AI».body := by rfl
theorem «FN2-ECHO-DEADLINE$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-DEADLINE$AI».body 512 = .ok («FN2-ECHO-DEADLINE$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 4)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 4) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 4), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-DEADLINE$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-DEADLINE$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-DEADLINE$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-DEADLINE$AI».decoded]
  exact «FN2-ECHO-DEADLINE$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-DEADLINE».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 68, 69, 65, 68, 76, 73, 78, 69, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-DEADLINE».body : Term := (.app "FN2-ECHO-DEADLINE$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-DEADLINE».decoded : Translation.readTerm 512 «FN2-ECHO-DEADLINE».canonicalBody = some «FN2-ECHO-DEADLINE».body := by rfl
theorem «FN2-ECHO-DEADLINE».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-DEADLINE».body 512 = .ok («FN2-ECHO-DEADLINE» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-DEADLINE$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-DEADLINE».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-DEADLINE».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-DEADLINE» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-DEADLINE».decoded]
  exact «FN2-ECHO-DEADLINE».export_body «I» «FN2-ECHO»

def «FN2-ECHO-CAP-INDEX$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (5)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-CAP-INDEX$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 5)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-CAP-INDEX$AI».decoded : Translation.readTerm 512 «FN2-ECHO-CAP-INDEX$AI».canonicalBody = some «FN2-ECHO-CAP-INDEX$AI».body := by rfl
theorem «FN2-ECHO-CAP-INDEX$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-CAP-INDEX$AI».body 512 = .ok («FN2-ECHO-CAP-INDEX$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 5)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 5) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 5), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-CAP-INDEX$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-CAP-INDEX$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-CAP-INDEX$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-CAP-INDEX$AI».decoded]
  exact «FN2-ECHO-CAP-INDEX$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-CAP-INDEX».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 67, 65, 80, 45, 73, 78, 68, 69, 88, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-CAP-INDEX».body : Term := (.app "FN2-ECHO-CAP-INDEX$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-CAP-INDEX».decoded : Translation.readTerm 512 «FN2-ECHO-CAP-INDEX».canonicalBody = some «FN2-ECHO-CAP-INDEX».body := by rfl
theorem «FN2-ECHO-CAP-INDEX».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-CAP-INDEX».body 512 = .ok («FN2-ECHO-CAP-INDEX» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-CAP-INDEX$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-CAP-INDEX».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-CAP-INDEX».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-CAP-INDEX» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-CAP-INDEX».decoded]
  exact «FN2-ECHO-CAP-INDEX».export_body «I» «FN2-ECHO»

def «FN2-ECHO-CAP-NONCE$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (6)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-CAP-NONCE$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 6)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-CAP-NONCE$AI».decoded : Translation.readTerm 512 «FN2-ECHO-CAP-NONCE$AI».canonicalBody = some «FN2-ECHO-CAP-NONCE$AI».body := by rfl
theorem «FN2-ECHO-CAP-NONCE$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-CAP-NONCE$AI».body 512 = .ok («FN2-ECHO-CAP-NONCE$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 6)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 6) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 6), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-CAP-NONCE$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-CAP-NONCE$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-CAP-NONCE$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-CAP-NONCE$AI».decoded]
  exact «FN2-ECHO-CAP-NONCE$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-CAP-NONCE».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 67, 65, 80, 45, 78, 79, 78, 67, 69, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-CAP-NONCE».body : Term := (.app "FN2-ECHO-CAP-NONCE$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-CAP-NONCE».decoded : Translation.readTerm 512 «FN2-ECHO-CAP-NONCE».canonicalBody = some «FN2-ECHO-CAP-NONCE».body := by rfl
theorem «FN2-ECHO-CAP-NONCE».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-CAP-NONCE».body 512 = .ok («FN2-ECHO-CAP-NONCE» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-CAP-NONCE$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-CAP-NONCE».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-CAP-NONCE».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-CAP-NONCE» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-CAP-NONCE».decoded]
  exact «FN2-ECHO-CAP-NONCE».export_body «I» «FN2-ECHO»

def «FN2-ECHO-POOL-SLOT$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (7)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-POOL-SLOT$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 7)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-POOL-SLOT$AI».decoded : Translation.readTerm 512 «FN2-ECHO-POOL-SLOT$AI».canonicalBody = some «FN2-ECHO-POOL-SLOT$AI».body := by rfl
theorem «FN2-ECHO-POOL-SLOT$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-POOL-SLOT$AI».body 512 = .ok («FN2-ECHO-POOL-SLOT$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 7)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 7) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 7), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-POOL-SLOT$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-POOL-SLOT$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-POOL-SLOT$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-POOL-SLOT$AI».decoded]
  exact «FN2-ECHO-POOL-SLOT$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-POOL-SLOT».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 80, 79, 79, 76, 45, 83, 76, 79, 84, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-POOL-SLOT».body : Term := (.app "FN2-ECHO-POOL-SLOT$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-POOL-SLOT».decoded : Translation.readTerm 512 «FN2-ECHO-POOL-SLOT».canonicalBody = some «FN2-ECHO-POOL-SLOT».body := by rfl
theorem «FN2-ECHO-POOL-SLOT».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-POOL-SLOT».body 512 = .ok («FN2-ECHO-POOL-SLOT» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-POOL-SLOT$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-POOL-SLOT».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-POOL-SLOT».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-POOL-SLOT» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-POOL-SLOT».decoded]
  exact «FN2-ECHO-POOL-SLOT».export_body «I» «FN2-ECHO»

def «FN2-ECHO-POOL-GEN$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (8)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-POOL-GEN$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 8)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-POOL-GEN$AI».decoded : Translation.readTerm 512 «FN2-ECHO-POOL-GEN$AI».canonicalBody = some «FN2-ECHO-POOL-GEN$AI».body := by rfl
theorem «FN2-ECHO-POOL-GEN$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-POOL-GEN$AI».body 512 = .ok («FN2-ECHO-POOL-GEN$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 8)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 8) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 8), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-POOL-GEN$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-POOL-GEN$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-POOL-GEN$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-POOL-GEN$AI».decoded]
  exact «FN2-ECHO-POOL-GEN$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-POOL-GEN».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 80, 79, 79, 76, 45, 71, 69, 78, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-POOL-GEN».body : Term := (.app "FN2-ECHO-POOL-GEN$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-POOL-GEN».decoded : Translation.readTerm 512 «FN2-ECHO-POOL-GEN».canonicalBody = some «FN2-ECHO-POOL-GEN».body := by rfl
theorem «FN2-ECHO-POOL-GEN».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-POOL-GEN».body 512 = .ok («FN2-ECHO-POOL-GEN» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-POOL-GEN$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-POOL-GEN».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-POOL-GEN».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-POOL-GEN» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-POOL-GEN».decoded]
  exact «FN2-ECHO-POOL-GEN».export_body «I» «FN2-ECHO»

def «FN2-ECHO-OFF$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (9)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-OFF$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 9)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-OFF$AI».decoded : Translation.readTerm 512 «FN2-ECHO-OFF$AI».canonicalBody = some «FN2-ECHO-OFF$AI».body := by rfl
theorem «FN2-ECHO-OFF$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-OFF$AI».body 512 = .ok («FN2-ECHO-OFF$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 9)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 9) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 9), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-OFF$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-OFF$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-OFF$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-OFF$AI».decoded]
  exact «FN2-ECHO-OFF$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-OFF».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 79, 70, 70, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-OFF».body : Term := (.app "FN2-ECHO-OFF$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-OFF».decoded : Translation.readTerm 512 «FN2-ECHO-OFF».canonicalBody = some «FN2-ECHO-OFF».body := by rfl
theorem «FN2-ECHO-OFF».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-OFF».body 512 = .ok («FN2-ECHO-OFF» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-OFF$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-OFF».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-OFF».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-OFF» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-OFF».decoded]
  exact «FN2-ECHO-OFF».export_body «I» «FN2-ECHO»

def «FN2-ECHO-LENGTH$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (10)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-LENGTH$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 10)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-LENGTH$AI».decoded : Translation.readTerm 512 «FN2-ECHO-LENGTH$AI».canonicalBody = some «FN2-ECHO-LENGTH$AI».body := by rfl
theorem «FN2-ECHO-LENGTH$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-LENGTH$AI».body 512 = .ok («FN2-ECHO-LENGTH$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 10)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 10) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 10), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-LENGTH$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-LENGTH$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-LENGTH$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-LENGTH$AI».decoded]
  exact «FN2-ECHO-LENGTH$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-LENGTH».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 76, 69, 78, 71, 84, 72, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-LENGTH».body : Term := (.app "FN2-ECHO-LENGTH$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-LENGTH».decoded : Translation.readTerm 512 «FN2-ECHO-LENGTH».canonicalBody = some «FN2-ECHO-LENGTH».body := by rfl
theorem «FN2-ECHO-LENGTH».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-LENGTH».body 512 = .ok («FN2-ECHO-LENGTH» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-LENGTH$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-LENGTH».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-LENGTH».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-LENGTH» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-LENGTH».decoded]
  exact «FN2-ECHO-LENGTH».export_body «I» «FN2-ECHO»

def «FN2-ECHO-PENDING$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (11)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-PENDING$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 11)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-PENDING$AI».decoded : Translation.readTerm 512 «FN2-ECHO-PENDING$AI».canonicalBody = some «FN2-ECHO-PENDING$AI».body := by rfl
theorem «FN2-ECHO-PENDING$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-PENDING$AI».body 512 = .ok («FN2-ECHO-PENDING$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 11)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 11) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 11), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-PENDING$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-PENDING$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-PENDING$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-PENDING$AI».decoded]
  exact «FN2-ECHO-PENDING$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-PENDING».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 80, 69, 78, 68, 73, 78, 71, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-PENDING».body : Term := (.app "FN2-ECHO-PENDING$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-PENDING».decoded : Translation.readTerm 512 «FN2-ECHO-PENDING».canonicalBody = some «FN2-ECHO-PENDING».body := by rfl
theorem «FN2-ECHO-PENDING».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-PENDING».body 512 = .ok («FN2-ECHO-PENDING» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-PENDING$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-PENDING».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-PENDING».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-PENDING» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-PENDING».decoded]
  exact «FN2-ECHO-PENDING».export_body «I» «FN2-ECHO»

def «FN2-ECHO-BORROWS$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (12)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-BORROWS$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 12)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-BORROWS$AI».decoded : Translation.readTerm 512 «FN2-ECHO-BORROWS$AI».canonicalBody = some «FN2-ECHO-BORROWS$AI».body := by rfl
theorem «FN2-ECHO-BORROWS$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-BORROWS$AI».body 512 = .ok («FN2-ECHO-BORROWS$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 12)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 12) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 12), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-BORROWS$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-BORROWS$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-BORROWS$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-BORROWS$AI».decoded]
  exact «FN2-ECHO-BORROWS$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-BORROWS».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 66, 79, 82, 82, 79, 87, 83, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-BORROWS».body : Term := (.app "FN2-ECHO-BORROWS$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-BORROWS».decoded : Translation.readTerm 512 «FN2-ECHO-BORROWS».canonicalBody = some «FN2-ECHO-BORROWS».body := by rfl
theorem «FN2-ECHO-BORROWS».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-BORROWS».body 512 = .ok («FN2-ECHO-BORROWS» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-BORROWS$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-BORROWS».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-BORROWS».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-BORROWS» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-BORROWS».decoded]
  exact «FN2-ECHO-BORROWS».export_body «I» «FN2-ECHO»

def «FN2-ECHO-NEXT-FREE$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (13)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-NEXT-FREE$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 13)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-NEXT-FREE$AI».decoded : Translation.readTerm 512 «FN2-ECHO-NEXT-FREE$AI».canonicalBody = some «FN2-ECHO-NEXT-FREE$AI».body := by rfl
theorem «FN2-ECHO-NEXT-FREE$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-NEXT-FREE$AI».body 512 = .ok («FN2-ECHO-NEXT-FREE$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 13)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 13) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 13), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-NEXT-FREE$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-NEXT-FREE$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-NEXT-FREE$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-NEXT-FREE$AI».decoded]
  exact «FN2-ECHO-NEXT-FREE$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-NEXT-FREE».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 78, 69, 88, 84, 45, 70, 82, 69, 69, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-NEXT-FREE».body : Term := (.app "FN2-ECHO-NEXT-FREE$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-NEXT-FREE».decoded : Translation.readTerm 512 «FN2-ECHO-NEXT-FREE».canonicalBody = some «FN2-ECHO-NEXT-FREE».body := by rfl
theorem «FN2-ECHO-NEXT-FREE».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-NEXT-FREE».body 512 = .ok («FN2-ECHO-NEXT-FREE» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-NEXT-FREE$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-NEXT-FREE».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-NEXT-FREE».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-NEXT-FREE» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-NEXT-FREE».decoded]
  exact «FN2-ECHO-NEXT-FREE».export_body «I» «FN2-ECHO»

def «FN2-ECHO-STOPPED$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (14)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-STOPPED$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 14)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-STOPPED$AI».decoded : Translation.readTerm 512 «FN2-ECHO-STOPPED$AI».canonicalBody = some «FN2-ECHO-STOPPED$AI».body := by rfl
theorem «FN2-ECHO-STOPPED$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-STOPPED$AI».body 512 = .ok («FN2-ECHO-STOPPED$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 14)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 14) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 14), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-STOPPED$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-STOPPED$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-STOPPED$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-STOPPED$AI».decoded]
  exact «FN2-ECHO-STOPPED$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-STOPPED».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 83, 84, 79, 80, 80, 69, 68, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-STOPPED».body : Term := (.app "FN2-ECHO-STOPPED$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-STOPPED».decoded : Translation.readTerm 512 «FN2-ECHO-STOPPED».canonicalBody = some «FN2-ECHO-STOPPED».body := by rfl
theorem «FN2-ECHO-STOPPED».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-STOPPED».body 512 = .ok («FN2-ECHO-STOPPED» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-STOPPED$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-STOPPED».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-STOPPED».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-STOPPED» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-STOPPED».decoded]
  exact «FN2-ECHO-STOPPED».export_body «I» «FN2-ECHO»

def «FN2-ECHO-MODE$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (15)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-MODE$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 15)), (.var "FN2-ECHO")])])
theorem «FN2-ECHO-MODE$AI».decoded : Translation.readTerm 512 «FN2-ECHO-MODE$AI».canonicalBody = some «FN2-ECHO-MODE$AI».body := by rfl
theorem «FN2-ECHO-MODE$AI».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-MODE$AI».body 512 = .ok («FN2-ECHO-MODE$AI» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 15)), (.var "FN2-ECHO")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 15) «FN2-ECHO»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 15), «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-ECHO-MODE$AI».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-MODE$AI».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-MODE$AI» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-MODE$AI».decoded]
  exact «FN2-ECHO-MODE$AI».export_body «I» «FN2-ECHO»

def «FN2-ECHO-MODE».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79, 45, 77, 79, 68, 69, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 69, 67, 72, 79]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-ECHO-MODE».body : Term := (.app "FN2-ECHO-MODE$AI" [(.var "I"), (.var "FN2-ECHO")])
theorem «FN2-ECHO-MODE».decoded : Translation.readTerm 512 «FN2-ECHO-MODE».canonicalBody = some «FN2-ECHO-MODE».body := by rfl
theorem «FN2-ECHO-MODE».export_body («I» : Val) («FN2-ECHO» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] «FN2-ECHO-MODE».body 512 = .ok («FN2-ECHO-MODE» «I» «FN2-ECHO») := by
  change Translation.eval fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] (.app "FN2-ECHO-MODE$AI" [(.var "I"), (.var "FN2-ECHO")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-ECHO»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-ECHO-MODE».canonical_body («I» : Val) («FN2-ECHO» : Val) :
    Translation.evalExport 512 «FN2-ECHO-MODE».canonicalBody fns [("I", «I»), ("FN2-ECHO", «FN2-ECHO»)] = .ok («FN2-ECHO-MODE» «I» «FN2-ECHO») := by
  simp only [Translation.evalExport, «FN2-ECHO-MODE».decoded]
  exact «FN2-ECHO-MODE».export_body «I» «FN2-ECHO»

def «FN2-MACHINES-READY-PREV$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (2)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-READY-PREV$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 2)), (.var "FN2-MACHINES")])])
theorem «FN2-MACHINES-READY-PREV$AI».decoded : Translation.readTerm 512 «FN2-MACHINES-READY-PREV$AI».canonicalBody = some «FN2-MACHINES-READY-PREV$AI».body := by rfl
theorem «FN2-MACHINES-READY-PREV$AI».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-READY-PREV$AI».body 512 = .ok («FN2-MACHINES-READY-PREV$AI» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 2)), (.var "FN2-MACHINES")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 2) «FN2-MACHINES»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 2), «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-MACHINES-READY-PREV$AI».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-READY-PREV$AI».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-READY-PREV$AI» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-READY-PREV$AI».decoded]
  exact «FN2-MACHINES-READY-PREV$AI».export_body «I» «FN2-MACHINES»

def «FN2-MACHINES-READY-PREV».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 82, 69, 65, 68, 89, 45, 80, 82, 69, 86, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-READY-PREV».body : Term := (.app "FN2-MACHINES-READY-PREV$AI" [(.var "I"), (.var "FN2-MACHINES")])
theorem «FN2-MACHINES-READY-PREV».decoded : Translation.readTerm 512 «FN2-MACHINES-READY-PREV».canonicalBody = some «FN2-MACHINES-READY-PREV».body := by rfl
theorem «FN2-MACHINES-READY-PREV».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-READY-PREV».body 512 = .ok («FN2-MACHINES-READY-PREV» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "FN2-MACHINES-READY-PREV$AI" [(.var "I"), (.var "FN2-MACHINES")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-MACHINES-READY-PREV».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-READY-PREV».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-READY-PREV» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-READY-PREV».decoded]
  exact «FN2-MACHINES-READY-PREV».export_body «I» «FN2-MACHINES»

def «FN2-MACHINES-READY-NEXT$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (3)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-READY-NEXT$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 3)), (.var "FN2-MACHINES")])])
theorem «FN2-MACHINES-READY-NEXT$AI».decoded : Translation.readTerm 512 «FN2-MACHINES-READY-NEXT$AI».canonicalBody = some «FN2-MACHINES-READY-NEXT$AI».body := by rfl
theorem «FN2-MACHINES-READY-NEXT$AI».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-READY-NEXT$AI».body 512 = .ok («FN2-MACHINES-READY-NEXT$AI» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 3)), (.var "FN2-MACHINES")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 3) «FN2-MACHINES»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 3), «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-MACHINES-READY-NEXT$AI».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-READY-NEXT$AI».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-READY-NEXT$AI» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-READY-NEXT$AI».decoded]
  exact «FN2-MACHINES-READY-NEXT$AI».export_body «I» «FN2-MACHINES»

def «FN2-MACHINES-READY-NEXT».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 82, 69, 65, 68, 89, 45, 78, 69, 88, 84, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-READY-NEXT».body : Term := (.app "FN2-MACHINES-READY-NEXT$AI" [(.var "I"), (.var "FN2-MACHINES")])
theorem «FN2-MACHINES-READY-NEXT».decoded : Translation.readTerm 512 «FN2-MACHINES-READY-NEXT».canonicalBody = some «FN2-MACHINES-READY-NEXT».body := by rfl
theorem «FN2-MACHINES-READY-NEXT».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-READY-NEXT».body 512 = .ok («FN2-MACHINES-READY-NEXT» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "FN2-MACHINES-READY-NEXT$AI" [(.var "I"), (.var "FN2-MACHINES")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-MACHINES-READY-NEXT».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-READY-NEXT».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-READY-NEXT» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-READY-NEXT».decoded]
  exact «FN2-MACHINES-READY-NEXT».export_body «I» «FN2-MACHINES»

def «FN2-MACHINES-WAIT-REASON$AI».canonicalBody : Translation.Object := (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 84, 72]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (4)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-WAIT-REASON$AI».body : Term := (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 4)), (.var "FN2-MACHINES")])])
theorem «FN2-MACHINES-WAIT-REASON$AI».decoded : Translation.readTerm 512 «FN2-MACHINES-WAIT-REASON$AI».canonicalBody = some «FN2-MACHINES-WAIT-REASON$AI».body := by rfl
theorem «FN2-MACHINES-WAIT-REASON$AI».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-WAIT-REASON$AI».body 512 = .ok («FN2-MACHINES-WAIT-REASON$AI» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "NTH" [(.var "I"), (.app "NTH" [(.quote (Val.int 4)), (.var "FN2-MACHINES")])]) 512 = _
  refine Translation.eval_app (vs := [«I», (Native.nth (Val.int 4) «FN2-MACHINES»)]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        refine Translation.eval_app (vs := [(Val.int 4), «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
        ·
          refine Translation.eval_args_cons ?_ ?_
          ·
            rfl
          ·
            refine Translation.eval_args_cons ?_ ?_
            ·
              rfl
            ·
              rfl
      ·
        rfl
theorem «FN2-MACHINES-WAIT-REASON$AI».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-WAIT-REASON$AI».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-WAIT-REASON$AI» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-WAIT-REASON$AI».decoded]
  exact «FN2-MACHINES-WAIT-REASON$AI».export_body «I» «FN2-MACHINES»

def «FN2-MACHINES-WAIT-REASON».canonicalBody : Translation.Object := (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83, 45, 87, 65, 73, 84, 45, 82, 69, 65, 83, 79, 78, 36, 65, 73]) (.cons (.symbol [65, 67, 76, 50] [73]) (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 77, 65, 67, 72, 73, 78, 69, 83]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))))
def «FN2-MACHINES-WAIT-REASON».body : Term := (.app "FN2-MACHINES-WAIT-REASON$AI" [(.var "I"), (.var "FN2-MACHINES")])
theorem «FN2-MACHINES-WAIT-REASON».decoded : Translation.readTerm 512 «FN2-MACHINES-WAIT-REASON».canonicalBody = some «FN2-MACHINES-WAIT-REASON».body := by rfl
theorem «FN2-MACHINES-WAIT-REASON».export_body («I» : Val) («FN2-MACHINES» : Val) :
    Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] «FN2-MACHINES-WAIT-REASON».body 512 = .ok («FN2-MACHINES-WAIT-REASON» «I» «FN2-MACHINES») := by
  change Translation.eval fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] (.app "FN2-MACHINES-WAIT-REASON$AI" [(.var "I"), (.var "FN2-MACHINES")]) 512 = _
  refine Translation.eval_app (vs := [«I», «FN2-MACHINES»]) (by decide) (by decide) ?_ (by rfl)
  ·
    refine Translation.eval_args_cons ?_ ?_
    ·
      rfl
    ·
      refine Translation.eval_args_cons ?_ ?_
      ·
        rfl
      ·
        rfl
theorem «FN2-MACHINES-WAIT-REASON».canonical_body («I» : Val) («FN2-MACHINES» : Val) :
    Translation.evalExport 512 «FN2-MACHINES-WAIT-REASON».canonicalBody fns [("I", «I»), ("FN2-MACHINES", «FN2-MACHINES»)] = .ok («FN2-MACHINES-WAIT-REASON» «I» «FN2-MACHINES») := by
  simp only [Translation.evalExport, «FN2-MACHINES-WAIT-REASON».decoded]
  exact «FN2-MACHINES-WAIT-REASON».export_body «I» «FN2-MACHINES»

end Fn2.Instances.BridgeWorld
