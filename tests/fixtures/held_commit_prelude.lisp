;;; The shipped fnn-owner-held-commit macro (host/native/owner.lisp) for a raw
;;; harness that evaluates a caller's defun out of bp-app.lisp, bp-node.lisp,
;;; hybrid-control.lisp or owner.lisp.  Without the macro the form
;;; (fnn-owner-held-commit (SECTION SERVICE CID . CLASS) . BODY) compiles as a
;;; call of a function and its first argument as an application, so the
;;; caller dies at load or run time (UNDEFINED-FUNCTION :POSTER, or the
;;; section entry).  The macro and the transit-detail variable the callers set
;;; (*fnn-owner-transit-detail*) are read from the source, not restated.
;;; The settle (fnn-owner-held-finish) is read from the source too.  Quantum 1's
;;; START answers an empty frames job here: nothing is queued in a harness, so
;;; the job is :done and quantum 2 runs BODY, as ACL2's :submit does;
;;; a harness that wants a held batch defines fnn-owner-held-start itself
;;; before loading this file.  Not a harness itself.
(in-package "ACL2")

(with-open-file (stream "host/native/owner.lisp")
  (let ((macro nil) (detail nil) (finish nil))
    (loop for form = (read stream nil :eof) until (or (eq form :eof) (and macro detail finish))
          do (cond ((and (consp form) (eq (car form) 'defmacro)
                         (eq (cadr form) 'fnn-owner-held-commit))
                    (eval form) (setq macro t))
                   ((and (consp form) (eq (car form) 'defvar)
                         (eq (cadr form) '*fnn-owner-transit-detail*))
                    (eval form) (setq detail t))
                   ((and (consp form) (eq (car form) 'defun)
                         (eq (cadr form) 'fnn-owner-held-finish))
                    (eval form) (setq finish t))))
    (unless macro (error "fnn-owner-held-commit not found in host/native/owner.lisp"))
    (unless detail (error "*fnn-owner-transit-detail* not found in host/native/owner.lisp"))
    (unless finish (error "fnn-owner-held-finish not found in host/native/owner.lisp"))))
(unless (fboundp 'fnn-owner-held-start)
  (defun fnn-owner-held-start (service) (declare (ignore service)) (list :frames nil nil)))
(unless (fboundp 'fnn-owner-held-frames-wait)
  (defun fnn-owner-held-frames-wait (service frames capture)
    (declare (ignore service frames capture)) :done))
(unless (fboundp 'fnn-owner-held-frames-complete)
  (defun fnn-owner-held-frames-complete (service result thunk)
    (declare (ignore service result)) (when thunk (funcall thunk))))
