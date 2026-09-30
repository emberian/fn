(in-package "ACL2")
(include-book "../../books/history-cold-runtime-status")

; Test-only finite trajectory, not a served or oracle codec implementation.
(defun fn-hrcs-test-ticks (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (zp fuel) c
    (mv-let (v byte next) (fn-hrcur-cold-tick c)
      (declare (ignore v byte))
      (fn-hrcs-test-ticks (1- fuel) next))))

(assert-event
 (mv-let (v byte next)
   (fn-hrcur-cold-tick
     (fn-hrcur-cold-begin '(:decoded (:span 6 0 4 1)) :capture :lease))
   (declare (ignore byte next))
   (and (equal v :continue)
        (not (equal v :write)) (not (equal v :io)))))

(assert-event
 (let ((c (fn-hrcs-test-ticks 5
             (fn-hrcur-cold-begin '(:decoded (:span 6 0 4 1)) :capture :lease))))
   (mv-let (d ignored next) (fn-hrcur-cold-tick c)
     (declare (ignore ignored next))
     (mv-let (v byte next) (fn-hrcur-cold-supply c 4 17)
       (declare (ignore next))
       (and (equal d '(:need-byte 4 :span-body 4))
            (equal v :emit) (equal byte 17)
            (not (equal v :write)) (not (equal v :io)))))))

; Malformed-state coverage of the same unconditional conclusion.
(assert-event
 (mv-let (v byte next) (fn-hrcur-cold-tick nil)
   (declare (ignore byte next))
   (mv-let (w byte next) (fn-hrcur-cold-supply nil 4 17)
     (declare (ignore byte next))
     (and (not (equal v :write)) (not (equal v :io))
          (not (equal w :write)) (not (equal w :io))))))
