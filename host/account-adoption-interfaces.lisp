; Declarations are checked by the actual build world. PROGRAM entries have
; no :raw-with proof claim; installation/compiled BODY remains unavailable.
(in-package "ACL2")
(definterface fn-owner-account-adoption-begin
 :class :program
 :exempt ((config "Borrowed original parsed config; lexical phase2 source must cover it")
          (bindings "Borrowed original bindings; never a host numeric allowance")
          (entropy "Original entropy observation; not namespace authority"))
 :direct "Explicit five-MV PROGRAM account entry; compiled source and BODY installation remain required")
(definterface fn-owner-account-adoption-tick
 :class :program
 :direct "Explicit five-MV PROGRAM account continuation with actual ticket and CURRENT custody")
(definterface fn-owner-account-adoption-collect
 :class :program
 :direct "Explicit five-MV PROGRAM collector derives actual durable output internally")
(definterface fn-owner-account-turn-return-current
 :class :program
 :direct "Actual owner epilogue PROGRAM subject; no supplied receipt, vector, or joined Boolean")
(definterface fn-owner-account-adoption-status
 :class :common-lisp-compliant)
