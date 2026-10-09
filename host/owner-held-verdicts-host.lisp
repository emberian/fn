; fn: the owner's held-row verdicts, for the developer image's inspection only
; (FN_NATIVE_TEST_HELD_VERDICTS_FILE, host/native/owner.lisp
; fnn-dev-held-verdicts-dump; coordinator ruling 2026-10-09 on
; OWNER-RECLAIM-PREDICT-FOLD-CONTEXT).  No served verb reads it.
;
; The reclaim swap's pass 3 rewrites only tombstoned records, whose content
; nothing serves after expiry; what the prediction decides is the held
; context (verdict, keyring generation) those rows carry.  This view prints
; the acceptance evidence the owner's store holds, newest first, (msgid .
; verdict) per held row (books/store-node.lisp fn-sn-verdicts), so a test
; compares the swapped owner with a restarted one.
(in-package "ACL2")
(include-book "../books/definterface")
(include-book "../books/owner-state-accessors")
(include-book "../books/store-node")

; A reader: it returns no state, so it is no writer of the carried owner
; state (host/owner-served-carried.lisp).
(defun fn-owner-held-verdicts (state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (fn-sn-verdicts (fn-owner-store state)))

(definterface fn-owner-held-verdicts
  :class :common-lisp-compliant)
