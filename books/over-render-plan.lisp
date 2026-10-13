; The served OVER plan's pool-lease boundary. The executor owns bytes and
; sends; these total selectors own cursor selection and plan continuation.
(in-package "ACL2")
(include-book "over-render-lease")
(include-book "served-query-plan")

(defun fn-ovr-rest-cursor (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (cond ((fn-qplan-cursor-effectp (car rest))
             (let ((cur (fn-cur-at 1 (car rest))))
               (if (and (fn-ovw-cursor-effectp (car rest)) (consp cur)
                        (fn-ovw-cursorp cur) (not (nth 7 cur)))
                   cur
                 nil)))
            ((consp (fn-srb-effect-octets (car rest))) nil)
            (t (fn-ovr-rest-cursor (cdr rest))))
    nil))

(defun fn-ovr-plan-cursor (plan)
  (declare (xargs :guard t))
  (and (atom (fn-splan-cur plan)) (fn-ovr-rest-cursor (fn-splan-rest plan))))

(defun fn-ovr-rest-next (rest next)
  (declare (xargs :guard t))
  (if (consp rest)
      (cond ((fn-qplan-cursor-effectp (car rest))
             (if (fn-ovr-rest-cursor rest)
                 (if next (cons (fn-ovw-cursor-effect next) (cdr rest)) (cdr rest))
               rest))
            ((consp (fn-srb-effect-octets (car rest))) rest)
            (t (cons (car rest) (fn-ovr-rest-next (cdr rest) next))))
    rest))

(defun fn-ovr-plan-next (plan next)
  (declare (xargs :guard t))
  (if (fn-ovr-plan-cursor plan)
      (cons (fn-splan-cur plan) (fn-ovr-rest-next (fn-splan-rest plan) next))
    plan))

(local (defthm fn-ovr-rest-cursor-is-over
 (implies (fn-ovr-rest-cursor rest)
 (and (consp (fn-ovr-rest-cursor rest)) (fn-ovw-cursorp (fn-ovr-rest-cursor rest))
      (not (nth 7 (fn-ovr-rest-cursor rest)))))
 :hints (("Goal" :induct (fn-ovr-rest-cursor rest)
 :in-theory (e/d (fn-ovr-rest-cursor) (fn-qplan-cursor-effectp fn-ovw-cursor-effectp fn-ovw-cursorp fn-srb-effect-octets))))))

(defthm fn-ovr-plan-cursor-is-an-over-cursor
 (implies (fn-ovr-plan-cursor plan)
 (and (consp (fn-ovr-plan-cursor plan)) (fn-ovw-cursorp (fn-ovr-plan-cursor plan))
      (not (nth 7 (fn-ovr-plan-cursor plan)))))
 :hints (("Goal" :use (:instance fn-ovr-rest-cursor-is-over (rest (fn-splan-rest plan)))
 :in-theory (union-theories '(fn-ovr-plan-cursor) (theory 'minimal-theory)))))

; Total hosted entry: N=0, NEXT=nil, J=0, OP=nil refuses a non-OVER plan.
(defun fn-ovr-plan-lease-quantum (plan w h id inc fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil
                  :guard (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-st-config fn-rtc-st)))))
  (let ((cur (fn-ovr-plan-cursor plan)))
    (if cur
        (fn-ovr-lease-quantum cur w h id inc fn-rtc-st fn-arena fn-cat)
      (mv 0 nil 0 nil fn-rtc-st))))
(verify-guards fn-ovr-plan-lease-quantum
  :hints (("Goal" :use fn-ovr-plan-cursor-is-an-over-cursor
                 :in-theory (disable fn-ovr-plan-cursor fn-ovw-cursorp))))

; A taken total-entry result establishes selection, rather than requiring it.
(defthm fn-ovr-plan-lease-quantum-taken-is-over
  (implies (posp (mv-nth 0 (fn-ovr-plan-lease-quantum plan w h id inc s fn-arena fn-cat)))
           (and (fn-ovr-plan-cursor plan)
                (fn-ovw-cursorp (fn-ovr-plan-cursor plan))))
  :hints (("Goal" :use fn-ovr-plan-cursor-is-an-over-cursor
                 :in-theory (union-theories '(fn-ovr-plan-lease-quantum
                       mv-nth car-cons cdr-cons posp zp)
                       (theory 'minimal-theory)))))
