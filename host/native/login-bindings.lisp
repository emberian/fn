;;; `principal set-password|bind|unbind' against a running owner (PKT-221;
;;; control request 14, books/peer-invite.lisp fn-pinv-bindings-request-*).
;;; The owner adopts its credential table from the file (ACL2's
;;; fn-native-auth-host-load, host/native/auth.lisp
;;; fnn-native-auth-reload-config) and bindings in one typed C adoption commit.
;;;
;;; I/O only.  After the verb made the credential file durable
;;; (host/native/auth-admin.lisp), it asks the owner, over the control socket,
;;; to re-read the file it was started with. The bounded startup reader feeds
;;; the same ACL2 account/signing preparation used by startup; each scheduler
;;; quantum is admitted before construction. The typed durable C completion
;;; publishes both roots together. Its runtime allowance remains unavailable
;;; until the genuine pooled issuer and producer are installed. Existing
;;; connections retain their pinned configuration.

(in-package "ACL2")

(defun fnn-login-bindings-owner-reload (service)
  ;; The bounded adoption driver enters/leaves the owner for each tick.
  ;; Holding a surrounding quantum would either deadlock a nested entry or
  ;; monopolize the owner for an operator table of arbitrary supported size.
  (let ((path *fnn-native-auth-live-path*))
    (if (null path) :refused
      (let ((max-credentials
              (fnn-profile-nat 'fn-store-profile-max-credentials
                               (fnn-owner-service-store service))))
        (multiple-value-bind (octets presentp)
            (fnn-native-auth-read path (fnn-core 'fn-native-auth-host-max-octets
                                                 max-credentials))
          (fnn-native-auth-reload-config service octets presentp max-credentials))))))

(defvar *fnn-login-bindings-next-handler* *fnn-hybrid-control-handler*)

(defun fnn-login-bindings-control-handle (service frame)
  (cond ((and (typep frame 'fnn-octets)
              (fnn-core 'fn-pinv-host-bindings-request-decode
                        (fnn-octet-list frame)))
         (fnn-login-bindings-owner-reload service))
        (*fnn-login-bindings-next-handler*
         (funcall *fnn-login-bindings-next-handler* service frame))
        (t nil)))

(setq *fnn-hybrid-control-handler* #'fnn-login-bindings-control-handle)

(defun fnn-login-bindings-request-reload (control-path)
  "Ask the owner at CONTROL-PATH to republish the credential file's bindings.
Answers :accepted, :uncertain or :refused (no socket, or the owner refused)."
  (if (null control-path)
      :refused
    (handler-case
        (let ((code (fnn-core 'fn-native-control-host-status-exit-code
                              (fnn-hybrid-control-send
                               control-path
                               (fnn-core 'fn-pinv-host-bindings-request-encode)))))
          (cond ((eql code +fnn-exit-ok+) :accepted)
                ((eql code +fnn-exit-uncertain+) :uncertain)
                (t :refused)))
      (error () :refused))))
