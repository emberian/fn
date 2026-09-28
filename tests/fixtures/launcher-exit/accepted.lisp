;;; The same paths classified: an unknown status is a fault or uncertain.
(defun fx-run (program)
  (let ((process (sb-ext:run-program program nil :wait t)))
    (sb-ext:process-exit-code process)))

(defun fx-unknown-is-fault (program)
  (let ((code (fx-run program)))
    (cond ((eql code 0) :ok)
          ((eql code 1) (fnn-refuse "the child's own refusal line"))
          (t (fnn-fault "child exit ~a" code)))))

(defun fx-nonzero-is-uncertain (process)
  (let ((code (sb-ext:process-exit-code process)))
    (cond ((eql code 0) :ok)
          ((not (eql code 0)) (fnn-indeterminate "child exit ~a" code)))))
