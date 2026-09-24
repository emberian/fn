; Teeth for books/owner-config-observe.lisp.
(in-package "ACL2")
(include-book "../../books/owner-config-observe")
(include-book "std/testing/must-fail" :dir :system)
(include-book "config-owner-live-tests")

(defconst *oco-t-obs* (fn-clock-observation 999999 1790000000000 10 t))
(defconst *oco-t-observed* (fn-ocfg-observe *ocl-t-created* *oco-t-obs*))

; Reachable, non-degenerate witness: the configured owner after a live group
; creation (config-owner-live-tests) takes a later reading, and the reading
; becomes the owner's clock; the store, the configuration and the pin table
; are the ones it had.
(assert-event (fn-ocl-relation *ocl-t-created*))
(assert-event (not (equal (fn-own-clock (fn-ocfg-owner *ocl-t-created*))
                          *oco-t-obs*)))
(assert-event (equal (fn-own-clock (fn-ocfg-owner *oco-t-observed*))
                     *oco-t-obs*))
(assert-event (equal (fn-own-store (fn-ocfg-owner *oco-t-observed*))
                     (fn-own-store (fn-ocfg-owner *ocl-t-created*))))
(assert-event (equal (fn-ocfg-config *oco-t-observed*)
                     (fn-ocfg-config *ocl-t-created*)))
(assert-event (equal (fn-ocfg-pins *oco-t-observed*)
                     (fn-ocfg-pins *ocl-t-created*)))
; The equation, evaluated on the witness.
(assert-event (equal *oco-t-observed*
                     (fn-ocfg-step *ocl-t-created* (list :observe *oco-t-obs*))))

; The point of the transition: the host's per-read call runs compiled code
; with no guard to evaluate.  fn-ocfg-step is not guard-verified and its
; guard is the whole-store recognizer, so the host must not reach the clock
; through it.
(assert-event (eq (symbol-class 'fn-ocfg-observe (w state))
                  :common-lisp-compliant))

; The equation has no hypothesis.  Its separation: the reading is not
; ignored -- two readings give two owners -- so the equation is not the
; trivial one of a transition that drops its argument.
(must-fail
 (defthm fn-oco-t-observe-ignores-the-reading
   (equal (fn-ocfg-observe oc obs1) (fn-ocfg-observe oc obs2))
   :hints (("Goal" :in-theory (enable fn-ocfg-observe)))))
(assert-event
 (not (equal (fn-ocfg-observe *ocl-t-created* *oco-t-obs*)
             (fn-ocfg-observe *ocl-t-created*
                              (fn-clock-observation 1999999 1790000001000 10 t)))))
