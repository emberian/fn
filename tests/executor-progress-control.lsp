; Run against a world containing tests/executor-progress-unit. This controlled
; mutation restores precisely the old unconditional observation-budget stop.
; Actual init, clock posting, scheduler, and turn remain the served functions.
(in-package "ACL2")
(include-book "tests/executor-progress-unit")
(set-guard-checking nil)
:q
(let ((original (symbol-function 'fn2-concrete-loop-stop-p))
      (positive '(t ((t :more 1 8 1 (0 2) (0 1) t))))
      (invocations 0))
  (assert (equal (fn2-progress-clock-test 1 t 1) positive))
  (unwind-protect
      (progn
        (setf (symbol-function 'fn2-concrete-loop-stop-p)
              (lambda (h k a obs visits actions core)
                (when (>= obs h) (incf invocations))
                (or (>= obs h) (funcall original h k a obs visits actions core))))
        (assert (equal (fn2-progress-clock-test 1 t 8)
                       (list t (make-list 8 :initial-element
                                        '(t :more 1 0 0 (0 2) (0 2) t)))))
        (assert (not (equal (fn2-progress-clock-test 1 t 1) positive)))
        (assert (< 0 invocations)))
    (setf (symbol-function 'fn2-concrete-loop-stop-p) original))
  (assert (equal (fn2-progress-clock-test 1 t 1) positive))
  (format t "EXECUTOR-PROGRESS baseline=PASS old-stop=CAUGHT restored=PASS~%"))
(sb-ext:exit :code 0)
