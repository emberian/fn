; The owner installer is books/owner-carrier.lisp fn-owner-install-ocfg (the
; carrier's field update); the view, a state global, is untouched by it --
; a frame the stobj discipline gives: the installer takes no STATE.

; Cold open's install: the same update (it installed a rebuilt view beside
; the owner before the park).
(defun fn-owner-install-open-ocfg (oc fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-owner-install-ocfg oc fn-owner-st))

(defthm fn-owner-open-ocfg-effect
  (equal (fn-owner-ocfg (fn-owner-install-open-ocfg oc fn-owner-st)) oc))
(defthm fn-owner-open-owner-bound
  (fn-owner-boundp (fn-owner-install-open-ocfg oc fn-owner-st)))
(defthm fn-owner-open-ocfg-preserves-stp
  (implies (fn-owner-stp fn-owner-st)
           (fn-owner-stp (fn-owner-install-open-ocfg oc fn-owner-st))))

(in-theory (disable fn-owner-obligation-view fn-owner-install-open-ocfg))
