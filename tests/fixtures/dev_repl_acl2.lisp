;;; Raw execution in an existing ACL2 world; this tests the real LD return
;;; convention and capture from a worker thread. Owner serialization is a named
;;; adapter, not a claim about the complete native owner.
(in-package "ACL2")
(defun fnn-owner-serialized (service cid thunk &optional class)
 (declare (ignore service cid class)) (funcall thunk))
(sb-thread:join-thread
 (sb-thread:make-thread
  (lambda ()
   (let ((good (fnn-dev-evaluate nil "(fnn-dev-admit '((defun fn-dev-ld-good (x) x)))")))
    (assert (search "OK" good :end2 2))
    (assert (search ":ADMITTED" good))
    (assert (search "Summary" good)))
   (let ((bad (fnn-dev-evaluate nil "(fnn-dev-admit '((defthm fn-dev-ld-bad nil)))")))
    (assert (search "ERROR" bad :end2 5))
    (assert (search "ACL2 admission incomplete" bad)))
   (let ((after (fnn-dev-evaluate nil "(fnn-dev-admit '((defthm fn-dev-ld-after (equal (fn-dev-ld-good x) x))))")))
    (assert (search "OK" after :end2 2))
    (assert (search ":ADMITTED" after)))
   (format t "DEV-REPL-ACTUAL-LD-PASS~%"))))
