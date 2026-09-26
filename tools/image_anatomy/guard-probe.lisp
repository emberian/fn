; tools/image_anatomy/guard-probe.lisp -- provoke guard violations through the
; host's own boundary (fnn-call) inside ACL2's loop, exactly where the node
; runs (LP's :return-from-lp ld), and print what the host sees (lane
; image-anatomy).  Loaded by guard.sh before (acl2::sbcl-restart); it
; replaces the raw fn-native-entry for this process only.
(in-package "ACL2")
(defun ia-guard-probe ()
  (dolist (call '((fn-cp-nth "not-a-natural" (1 2))
                  (fn-store-txn-name "not-a-sequence")
                  (fn-cp-nth 1 (a b c))))
    (format *error-output* "~&IA-GUARD ~s -> ~a~%" call
            (handler-case (let ((v (apply #'fnn-call (car call) (cdr call))))
                            (format nil "VALUE ~s" v))
              (serious-condition (c)
                (format nil "CONDITION ~a: ~a" (type-of c)
                        (or (ignore-errors (princ-to-string c)) "?"))))))
  (format *error-output* "~&IA-GUARD-DONE~%")
  (finish-output *error-output*)
  (sb-ext:exit :code 0 :abort t))
(defun fn-native-entry (st)
  (declare (ignore st))
  (ia-guard-probe)
  (values nil :exited *the-live-state*))
