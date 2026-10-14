; Pool OVER dispatch selects only an ordinary OVER cursor at the plan head.
(in-package "ACL2")
(include-book "../../books/over-render-plan")
(include-book "over-render-lease-tests")
(defconst *ovrpt-cur* (fn-ovw-cursor "fn.test" 1 3 3 nil t "s"))
(defconst *ovrpt-next* (fn-ovw-cursor "fn.test" 2 3 3 nil nil "s"))
(defconst *ovrpt-effect* (fn-ovw-cursor-effect *ovrpt-cur*))
(defconst *ovrpt-plan* (cons nil (list '(:yield) *ovrpt-effect* '(:reply (46 13 10)))))
(assert-event (equal (fn-ovr-plan-cursor *ovrpt-plan*) *ovrpt-cur*))
(assert-event (equal (fn-ovr-plan-next *ovrpt-plan* *ovrpt-next*)
                     (cons nil (list '(:yield) (fn-ovw-cursor-effect *ovrpt-next*) '(:reply (46 13 10))))))
(assert-event (equal (fn-ovr-plan-next *ovrpt-plan* nil)
                     '(nil (:yield) (:reply (46 13 10)))))
; Pending bytes, HDR, NEWNEWS and LIST stay on their existing dispatch.
(assert-event (not (fn-ovr-plan-cursor (cons '(65) (cdr *ovrpt-plan*)))))
(assert-event (not (fn-ovr-plan-cursor (cons nil (cons '(:reply (65)) (cdr *ovrpt-plan*))))))
(assert-event (not (fn-ovr-plan-cursor
                   (cons nil (list (fn-ovw-cursor-effect (fn-ovw-hdr-cursor "fn.test" 1 3 3 t :subject)))))))
(assert-event (not (fn-ovr-plan-cursor (cons nil (list '(:newnews-cursor (1)) *ovrpt-effect*)))))
(assert-event (not (fn-ovr-plan-cursor (cons nil (list '(:list-cursor (1)) *ovrpt-effect*)))))
(assert-event (equal (fn-ovr-plan-next '(nil (:reply (65))) *ovrpt-next*) '(nil (:reply (65)))))

; The total hosted entry refuses HDR without changing its pool state.
(defun ovrpt-refused-plan (fn-rtc-st fn-arena fn-cat)
 (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil))
 (let* ((fn-rtc-st (fn-rtc-st-init '(2 1 0 0 0 1 4) fn-rtc-st))
        (before (fn-rtc-x-state fn-rtc-st))
        (plan (cons nil (list (fn-ovw-cursor-effect
                               (fn-ovw-hdr-cursor "fn.test" 1 3 3 t :subject))))))
  (mv-let (n next j op fn-rtc-st)
   (fn-ovr-plan-lease-quantum plan 3 0 1 1 fn-rtc-st fn-arena fn-cat)
   (mv (and (not (fn-ovr-plan-cursor plan))
            (equal n 0) (null next) (equal j 0) (null op)
            (equal before (fn-rtc-x-state fn-rtc-st))) fn-rtc-st))))
(defun ovrpt-refused-plan-scene ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (ok fn-arena)
   (with-local-stobj fn-cat
    (mv-let (ok fn-arena fn-cat)
     (with-local-stobj fn-rtc-st
      (mv-let (ok fn-rtc-st) (ovrpt-refused-plan fn-rtc-st fn-arena fn-cat)
       (mv ok fn-arena fn-cat)))
     (mv ok fn-arena))) ok)))
(assert-event (ovrpt-refused-plan-scene))

; Taken N=3 is the positive control; the HDR refusal above is its N=0 tooth.
(defun ovrpt-taken-plan (fn-rtc-st fn-arena fn-cat)
 (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil))
 (mv-let (id inc fn-rtc-st) (pc1-boot 1000 nil fn-rtc-st)
  (let ((plan (cons nil (list (fn-ovw-cursor-effect *pc1-cur*)))))
   (mv-let (n next j op fn-rtc-st)
    (fn-ovr-plan-lease-quantum plan 3 0 id inc fn-rtc-st fn-arena fn-cat)
    (declare (ignore next))
    (mv (and (equal n 3) (posp j) (natp op)
             (equal (fn-ovr-plan-cursor plan) *pc1-cur*)
             (fn-ovw-cursorp (fn-ovr-plan-cursor plan))) fn-rtc-st)))))
(defun ovrpt-taken-plan-scene ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (ok fn-arena)
   (with-local-stobj fn-cat
    (mv-let (ok fn-arena fn-cat)
     (mv-let (fn-arena fn-cat) (pc1-seed *ovrs-a* *ovrs-c* fn-arena fn-cat)
      (with-local-stobj fn-rtc-st
       (mv-let (ok fn-rtc-st) (ovrpt-taken-plan fn-rtc-st fn-arena fn-cat)
        (mv ok fn-arena fn-cat))))
     (mv ok fn-arena))) ok)))
(assert-event (ovrpt-taken-plan-scene))
