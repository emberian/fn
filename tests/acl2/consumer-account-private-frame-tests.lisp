(in-package "ACL2")
(include-book "../../books/consumer-account-private-frame")
(include-book "../../books/consumer-account-config-row-carry")
(local (include-book "consumer-account-config-commit-tests"))

(defun fn-acjft-framep (cp one)
 (declare (xargs :guard t))
 (let ((a (fn-cp-nth 6 cp)) (b (fn-cp-nth 6 (fn-cp-nth 1 one))))
  (and (equal (fn-cp-nth 1 b) (fn-cp-nth 1 a))
       (equal (fn-cp-nth 2 b) (fn-cp-nth 2 a))
       (equal (fn-cp-nth 3 b) (fn-cp-nth 3 a))
       (equal (fn-cp-nth 4 b) (fn-cp-nth 4 a)))))

(defconst *acjft-event* '(:consumer-authority 0 1 0 (:authority-begin (65) 0 1 7)))
(defconst *acjft-one*
 (fn-acj-stage *acjt-initial* *acjt-metadata* nil *bcpt-base* *acjft-event* 0 nil))

;@positive-witness fn-acj-private-stage-preserves-current-authority
(assert-event
 (and (eq (fn-cp-nth 0 *acjft-one*) :ok)
      (fn-acjft-framep *acjt-initial* *acjft-one*)))

;@hyp-removal-witness fn-acj-private-stage-preserves-current-authority omitted=successful
(assert-event
 (let ((bad (fn-acj-stage *acjt-initial* *acjt-metadata* nil *bcpt-base*
                         *acjft-event* 1 nil)))
  (and (not (eq (fn-cp-nth 0 bad) :ok))
       (not (fn-acjft-framep *acjt-initial* bad)))))

; Independent literal fixed-row constructor/refinement, not a metadata ready
; assertion. The same actual BCP tick result is compared with the logical size.
;@mutation-witness actual-scan-complete-result-keeps-carried-size
(assert-event
 (let* ((one (fn-bcp-tick (fn-cp-nth 1 (fn-bcp-seal *bcpt-d*)) nil))
        (start (fn-cp-nth 1 one))
        (scan (fn-bcp-with start :scan nil nil (fn-cp-nth 7 start) (fn-cp-nth 8 start)
                           nil nil (list *bcpt-redeemed*) nil nil nil nil)))
  (and (fn-bcpr-row-domainp *bcpt-redeemed*)
       (equal (fn-bcp-tick scan (fn-bcpr-row-carry *bcpt-redeemed*))
              (fn-bcp-tick scan (fn-scs-summary *bcpt-redeemed*))))))
