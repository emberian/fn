; Qualification-only observer, loaded by test_native_image_differential.py
; after the launcher's ordinary heap probe, before the command restart.
; Observe the actual init decision before publication, preserving BOTH return
; values. ACL2 resolves and reports its profile; this never reads the store
; whose subsequent status is compared against these complete expected rows.
(in-package "ACL2")
(cl:unless (cl:fboundp 'acl2::fnn-save-world-flavor)
  (cl:error "fn: this probe runs only inside a built fn-host image"))

(sb-int:encapsulate
 'fnn-heap-init-decision-noted 'native-image-init-decision
 (lambda (original &rest args)
   (multiple-value-bind (decision note) (apply original args)
     (let ((request (fnn-core 'fn-heap-init-decision-request decision)))
       (when request
         (let ((profile (fnn-core 'fn-bs-profile-resolve request nil)))
           (with-open-file (out "init-decision.status" :direction :output
                                :if-exists :error :if-does-not-exist :create
                                :external-format :ascii)
             (format out "profile~{ ~a=~a~}~%"
                     (loop for (name . value) in (fnn-core 'fn-store-profile-report profile)
                           collect name collect value))
             (dolist (line (fnn-core 'fn-lim-values-lines profile nil))
               (write-line line out))))))
     (values decision note))))
