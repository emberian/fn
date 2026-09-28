;;; Each unclassified child-status path the launcher rule refuses.
(defun fx-run (program)
  (let ((process (sb-ext:run-program program nil :wait t)))
    (sb-ext:process-exit-code process)))

(defun fx-unknown-is-refused (program)
  (let ((code (fx-run program)))
    (cond ((eql code 0) :ok)
          ((eql code 5) (fnn-fault "usage"))
          (t (fnn-refuse "child failed")))))

(defun fx-no-unknown-arm (program)
  (let ((code (fx-run program)))
    (cond ((eql code 0) :ok)
          ((eql code 1) (fnn-refuse "child refused")))))

(defun fx-forwarded (program)
  (sb-ext:exit :code (fx-run program)))

(defun fx-nonzero-is-exit-one (process)
  (let ((code (sb-ext:process-exit-code process)))
    (cond ((eql code 0) +fnn-exit-ok+)
          ((not (eql code 0)) +fnn-exit-refused+))))
