; The installers' effects and frames are books/owner-carrier.lisp's.

; Proof-only carried entry-state invariant. Never called by native serving
; code or used as an executable guard: it names the maintained relation.
(defun fn-owner-retain-statep (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st :guard t :verify-guards nil))
  (and (fn-owner-boundp fn-owner-st)
       (fn-lgoc-invariantp (fn-owner-ocfg fn-owner-st))
       (fn-prc-carryp (fn-owner-retain-carry fn-owner-st))))

