;;; The shipped fnn-owner-held-commit macro (host/native/owner.lisp) for a raw
;;; harness that evaluates a caller's defun out of bp-app.lisp, bp-node.lisp,
;;; hybrid-control.lisp or owner.lisp.  Without the macro the form
;;; (fnn-owner-held-commit (SECTION SERVICE CID . CLASS) . BODY) compiles as a
;;; call of a function and its first argument as an application, so the
;;; caller dies at load or run time (UNDEFINED-FUNCTION :POSTER, or the
;;; section entry).  The macro is read from the source, not restated.
;;; Quantum 1's START answers (:inline) here: nothing is queued in a harness,
;;; so BODY runs in the caller's own section call, as ACL2's :submit does;
;;; a harness that wants a held batch defines fnn-owner-held-start itself
;;; before loading this file.  Not a harness itself.
(in-package "ACL2")
(with-open-file (stream "host/native/owner.lisp")
  (let ((found nil))
    (loop for form = (read stream nil :eof) until (eq form :eof)
          when (and (consp form) (eq (car form) 'defmacro)
                    (eq (cadr form) 'fnn-owner-held-commit))
            do (eval form) (setq found t) (return))
    (unless found (error "fnn-owner-held-commit not found in host/native/owner.lisp"))))
(unless (fboundp 'fnn-owner-held-start)
  (defun fnn-owner-held-start (service) (declare (ignore service)) (list :inline)))
