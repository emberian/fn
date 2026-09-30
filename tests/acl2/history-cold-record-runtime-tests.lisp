(in-package "ACL2")
(include-book "../../books/history-cold-record-runtime")
; Test driver only: an immutable octet list stands in for authenticated supply.
(defun fn-hrcur-cold-test-run (fuel c pool bytes)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (list :fuel bytes c)
    (mv-let (v b next) (fn-hrcur-cold-tick c)
      (cond
       ((eq v :prepared) (list :prepared bytes next))
       ((eq v :emit) (fn-hrcur-cold-test-run (1- fuel) next pool
                                           (append bytes (list b))))
       ((eq v :continue) (fn-hrcur-cold-test-run (1- fuel) next pool bytes))
       ((and (consp v) (eq (car v) :need-byte))
        (mv-let (sv sb sc)
          (fn-hrcur-cold-supply c (fn-hrcur-field 1 v)
                                (nth (fn-hrcur-field 1 v) pool))
          (cond ((eq sv :emit)
                 (fn-hrcur-cold-test-run (1- fuel) sc pool (append bytes (list sb))))
                ((eq sv :continue)
                 (fn-hrcur-cold-test-run (1- fuel) sc pool bytes))
                (t (list sv bytes sc)))))
       (t (list v bytes next))))))

(assert-event
 (equal (car (fn-hrcur-cold-test-run 50
                (fn-hrcur-cold-begin '(:decoded (:atom 257)) :capture :lease) nil nil))
        :prepared))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 50
                (fn-hrcur-cold-begin '(:decoded (:atom 257)) :capture :lease) nil nil))
        (fn-scc-encode 257)))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 50
                (fn-hrcur-cold-begin '(:decoded (:span 3 0 1 3)) :capture :lease)
                '(0 65 66 67) nil)) (fn-scc-encode "ABC")))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 50
                (fn-hrcur-cold-begin '(:decoded (:span 6 0 1 3)) :capture :lease)
                '(0 65 66 67) nil)) (fn-scc-encode '(65 66 67))))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 100
                (fn-hrcur-cold-begin
                  '(:decoded (:pair (:atom 64) (:span 6 0 1 3))) :capture :lease)
                '(0 65 66 67) nil)) (fn-scc-encode '(64 65 66 67))))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 100
                (fn-hrcur-cold-begin
                  '(:decoded (:pair (:atom 65) (:span 4 1 0 3))) :capture :lease)
                '(78 73 76) nil)) (fn-scc-encode '(65))))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 20000
                (fn-hrcur-cold-begin '(:decoded (:span 4 1 0 3)) :capture :lease)
                '(67 65 82) nil)) (fn-scc-encode 'car)))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 20000
                (fn-hrcur-cold-begin '(:decoded (:span 4 2 0 3)) :capture :lease)
                '(78 73 76) nil)) (fn-scc-encode nil)))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 20000
                (fn-hrcur-cold-begin '(:decoded (:span 4 0 0 3)) :capture :lease)
                '(78 73 76) nil)) (fn-scc-encode :nil)))
(assert-event
 (equal (cadr (fn-hrcur-cold-test-run 20000
                (fn-hrcur-cold-begin
                  '(:decoded (:pair (:atom 65)
                    (:pair (:atom 66) (:pair (:atom -1) (:atom nil))))) :capture :lease)
                nil nil)) (fn-scc-encode '(65 66 -1))))
