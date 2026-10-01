; Declarations are checked by the actual build world. PROGRAM entries have
; no :raw-with proof claim; installation/compiled BODY remains unavailable.
(in-package "ACL2")
(definterface fn-owner-account-adoption-begin
 :class :program
 :exempt ((config "Borrowed original parsed config; lexical phase2 source must cover it")
          (bindings "Borrowed original bindings; never a host numeric allowance")
          (entropy "Original entropy observation; not namespace authority")))
(definterface fn-owner-account-adoption-tick
 :class :program)
(definterface fn-owner-account-adoption-collect
 :class :program)
(definterface fn-owner-account-adoption-publication-step
 :class :program)
(definterface fn-owner-account-turn-return-current
 :class :program)
; Stage 0 (D46): fn-owner-account-adoption-status is dispatched by no loaded
; file (host/native/account-adoption.lisp is not loaded); declared again with it.
