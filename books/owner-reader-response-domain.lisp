; Domain of the actual owner response decoration used at RC completion.
; Proposed source proof: no receipt, runtime envelope or custody authority.
(in-package "ACL2")
(include-book "owner-log")
(include-book "public-exposure-reply")

(defthm fn-olog-served-refusal-lines-are-proper
 (true-listp (fn-olog-served-refusal-lines o id effects))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-olog-served-refusal-lines o id effects)
  :in-theory (union-theories (theory 'minimal-theory)
                            '(fn-olog-served-refusal-lines true-listp)))))

; Exact projection performed immediately by fn-owner-exposure-observe.
(defthm fn-exp-observe-effects-close-is-octets-or-nil
 (let* ((r (fn-exp-observe-effects xs lim id now effects consumed subject submitted))
        (close (if (consp (car r)) (cadr (car r)) nil)))
  (or (null close) (fn-cbor-octet-listp close)))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-exp-observe-effects fn-exp-observe fn-exp-observe-facts
     (:executable-counterpart fn-exp-line)
     (:executable-counterpart fn-cbor-octet-listp)
     car-cons cdr-cons)))))
