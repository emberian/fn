;;; Raw execution in an existing ACL2 world; this tests the real LD return
;;; convention and capture from a worker thread. Owner serialization is a named
;;; adapter, not a claim about the complete native owner.
(in-package "ACL2")
(defun fnn-owner-serialized (service cid thunk &optional class)
 (declare (ignore service cid class)) (funcall thunk))
(defun ev (text)
 ;; the old envelope: STATUS, a newline, the output
 (multiple-value-bind (status out) (fnn-dev-evaluate nil text)
  (concatenate 'string (symbol-name status) (string #\Newline) out)))
(sb-thread:join-thread
 (sb-thread:make-thread
  (lambda ()
   (let ((good (ev "(fnn-dev-admit '((in-package \"ACL2\") (defun fn-dev-ld-good (x) x)))")))
    (assert (search "OK" good :end2 2))
    (assert (search ":ADMITTED" good))
    (assert (search "Summary" good)))
   (let ((bad (ev "(fnn-dev-admit '((defthm fn-dev-ld-bad nil)))")))
    (assert (search "ERROR" bad :end2 5))
    (assert (search "ACL2 admission incomplete" bad)))
   (let ((after (ev "(fnn-dev-admit '((defthm fn-dev-ld-after (equal (fn-dev-ld-good x) x))))")))
    (assert (search "OK" after :end2 2))
    (assert (search ":ADMITTED" after)))
   ;; The real prover exhausts its allowance, LD returns, and the same world
   ;; remains usable. An observation timeout alone cannot provide this property.
   (let* ((before (step-limit-from-table (w *the-live-state*)))
          (limited (ev "(fnn-dev-admit '((defthm fn-dev-limited (equal (append (append x y) z) (append x (append y z)))) (defun fn-dev-must-not-admit (x) x)) :step-limit 0)")))
    (assert (search "ERROR" limited :end2 5))
    (assert (search "ACL2 Error [Step-limit]" limited))
    (assert (equal before (step-limit-from-table (w *the-live-state*))))
    (assert (not (getpropc 'fn-dev-must-not-admit 'formals nil (w *the-live-state*))))
    (assert (search "OK" (ev "(+ 20 22)") :end2 2))
    (assert (search ":ADMITTED" (ev "(fnn-dev-admit '((defthm fn-dev-after-limit (equal (fn-dev-ld-good x) x))) :step-limit nil)"))))
   (assert (search ":INVALID-STEP-LIMIT"
                   (ev "(fnn-dev-admit nil :step-limit -1)")))
   (format t "DEV-REPL-ACTUAL-LD-PASS~%"))))
