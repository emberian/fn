(in-package "ACL2")

(include-book "consumer-account-config-commit-tests") ; its fixtures are used by non-local events

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
