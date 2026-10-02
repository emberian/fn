; Declarations are checked by the actual build world. PROGRAM entries have
; no :raw-with proof claim; installation/compiled BODY remains unavailable.
(in-package "ACL2")
; Stage 0 (D46): fn-owner-account-adoption-status is dispatched by no loaded
; file (host/native/account-adoption.lisp is not loaded); declared again with it.
; Stage 0 (D46, 2026-10-01): the five account-adoption entry declarations
; (fn-owner-account-adoption-begin, -tick, -collect, -publication-step,
; fn-owner-account-turn-return-current) are withdrawn with their dispatcher
; (host/native/account-adoption.lisp, not loaded); they return with the
; account-adoption producer, each with its :direct claim true.
