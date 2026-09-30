(in-package "ACL2")
(include-book "../../books/consumer-account-initial")

(defun fn-caict-hypotheses (history incarnation frontier hn in)
  (declare (xargs :guard t))
  (list (fn-scc-octet-listp history) (equal hn (len history))
        (fn-scc-octet-listp incarnation) (equal in (len incarnation))
        (integerp frontier)))
(defun fn-caict-correspondp (history incarnation frontier hn in)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (cp metadata)
    (fn-caac-initial history incarnation frontier hn in)
    (fn-scs-correspondsp (fn-cp-nth 1 metadata) cp)))
;@positive fn-caac-initial-seven-fields-correspond
(assert-event
 (let* ((history '(1 2)) (incarnation '(3 4))
        (one (mv-list 2 (fn-caac-initial history incarnation 7 2 2)))
        (cp (car one)) (metadata (cadr one)))
   (and (equal (fn-caict-hypotheses history incarnation 7 2 2) '(t t t t t))
        (fn-caict-correspondp '(1 2) '(3 4) 7 2 2)
        (fn-cp-statep cp)
        (equal cp (fn-cp-initial history incarnation 7))
        (null (fn-cp-nth 2 metadata)) (null (fn-cp-nth 3 metadata))
        (equal (fn-cp-nth 6 cp) '(:authority 0 1 nil nil nil))
        (not (fn-cp-nth 3 (fn-cp-nth 6 cp))))))

;@hypothesis-removal fn-caac-initial-seven-fields-correspond history-octets
(assert-event
 (and (equal (fn-caict-hypotheses '(300) '(3 4) 7 1 2) '(nil t t t t))
      (not (fn-caict-correspondp '(300) '(3 4) 7 1 2))))

;@hypothesis-removal fn-caac-initial-seven-fields-correspond history-count
(assert-event
 (and (equal (fn-caict-hypotheses '(1 2) '(3 4) 7 3 2) '(t nil t t t))
      (not (fn-caict-correspondp '(1 2) '(3 4) 7 3 2))))

;@hypothesis-removal fn-caac-initial-seven-fields-correspond incarnation-octets
(assert-event
 (and (equal (fn-caict-hypotheses '(1 2) '(300) 7 2 1) '(t t nil t t))
      (not (fn-caict-correspondp '(1 2) '(300) 7 2 1))))

;@hypothesis-removal fn-caac-initial-seven-fields-correspond incarnation-count
(assert-event
 (and (equal (fn-caict-hypotheses '(1 2) '(3 4) 7 2 3) '(t t t nil t))
      (not (fn-caict-correspondp '(1 2) '(3 4) 7 2 3))))

;@hypothesis-removal fn-caac-initial-seven-fields-correspond frontier-scalar
(assert-event
 (and (equal (fn-caict-hypotheses '(1 2) '(3 4) '(7) 2 2) '(t t t t nil))
      (not (fn-caict-correspondp '(1 2) '(3 4) '(7) 2 2))))

; Explicit executable anchor outside the lexical-binding witness, so a
; constant-FALSE fixture predicate cannot satisfy the removal corpus.
(assert-event (fn-caict-correspondp '(1 2) '(3 4) 7 2 2))
