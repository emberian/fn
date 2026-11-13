; The served directory's identity is independent of CLI-side enumeration.
(in-package "ACL2")
(include-book "authority-served")

(defun fn2-authority-stream-resolve-positive ()
 (declare (xargs :verify-guards nil))
 (let* ((profile (put-assoc-equal :groups '(("ops.audit" . 71) ("ops.alert" . 19)) *fn2-as-served-profile*))
        (r (fn2-as-served-run profile
             (list (fn2-as-client
               (list (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.audit")))
                     (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.alert")))
                     (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.audi")))
                     (fn2-as-frame 'stream-resolve (list (fn2-as-o "ops.auditx")))))) nil)))
   (and (equal (nth 0 r) :quiet) (equal (nth 1 r) 0)
        (equal (car (nth 2 r))
          (append (fn2-as-accepted 'stream-resolve '(71))
                  (fn2-as-accepted 'stream-resolve '(19))
                  (fn2-as-refused 'stream-resolve "unknown-stream")
                  (fn2-as-refused 'stream-resolve "unknown-stream"))))))
(assert-event (fn2-authority-stream-resolve-positive))
