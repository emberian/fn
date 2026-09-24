; fn: the per-read clock observation as its own guard-verified transition.
;
; The native host hands the owner one clock reading before every socket read
; (host/native/owner.lisp fnn-owner-handle-chunk -> fnn-owner-advance-clock
; -> host/owner-host.lisp fn-owner-observe).  That call went through
; fn-ocfg-step, whose guard is the whole-store recognizer
; (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) and whose guards are not
; verified.  Under guard-checking t (the saved image asserts it,
; host/native/io.lisp), the executable counterpart of an unverified function
; evaluates its guard and then runs the logic body, so every served command
; -- STAT, ARTICLE, IHAVE, CHECK alike -- revalidated the entire store
; (fn-sn-statep twice, fn-node-statep three times, traced 2026-09-24) before
; the command was framed.  planning/evidence/t17-msgid-index-2026-09-24.md
; has the traced calls and the measured per-command cost before and after.
;
; fn-ocfg-observe is the same transition with guard t.  The equation below
; makes it the subject the host calls: every theorem about fn-ocfg-step's
; (:observe obs) arm is a theorem about it.
(in-package "ACL2")
(include-book "owner-config")

(defun fn-ocfg-observe (oc obs)
  (declare (xargs :guard t))
  (fn-ocfg-with-owner oc (fn-own-observe (fn-ocfg-owner oc) obs)))

; The subject equation (AGENTS.md, first assurance rule): the (:observe obs)
; event of the configured owner step is fn-ocfg-observe, for every oc and
; every obs, with no hypothesis.  It unfolds the otherwise arm of
; fn-ocfg-step through fn-ocfg-pass and fn-own-step's :observe arm.
(defthm fn-ocfg-step-observe-is-fn-ocfg-observe
  (equal (fn-ocfg-step oc (list :observe obs))
         (fn-ocfg-observe oc obs))
  :hints (("Goal" :in-theory (enable fn-ocfg-step fn-ocfg-pass fn-own-step
                                      fn-ocfg-observe))))
