;;; `principal bind|unbind' against a running owner (PKT-221; control request
;;; 14, books/peer-invite.lisp fn-pinv-bindings-request-*).
;;;
;;; I/O only.  After the verb made the credential file durable
;;; (host/native/auth-admin.lisp), it asks the owner, over the control socket,
;;; to re-read the file it was started with; the owner, under its mutex, reads
;;; it with the same bounded reader as at start and publishes ACL2's plan
;;; (books/login-binding-live.lisp fn-lb-sync-plan) through
;;; fnn-owner-live-reconfigure-locked (host/native/auth.lisp
;;; fnn-native-auth-publish-bindings).  A connection open at that moment keeps
;;; the table it pinned; the next connection pins the published one.

(in-package "ACL2")

(defun fnn-login-bindings-owner-reload (service)
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let ((path *fnn-native-auth-live-path*))
       (if (null path)
           :refused
         (let ((max-credentials
                 (fnn-profile-nat 'fn-store-profile-max-credentials
                                  (fnn-owner-service-store service))))
           (multiple-value-bind (octets presentp)
               (fnn-native-auth-read path (fnn-core 'fn-native-auth-host-max-octets
                                                    max-credentials))
             (fnn-native-auth-publish-bindings service octets presentp
                                               max-credentials))))))))

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
