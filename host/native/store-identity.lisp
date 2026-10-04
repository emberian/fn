;;; `fn identity CONTROL' (Mini M4, books/store-identity.lisp): who this store
;;; is, asked of the running owner over its 0600 control socket.  The client
;;; sends FNCT kind 24 (an empty payload); the owner answers kind 25, sealed
;;; by ACL2 from the genesis verdict its open installed, its consumer state,
;;; the image's recorded source revision and the digest of the exported
;;; wire-grammar file the image renders.
;;;
;;; I/O only.  ACL2 decides the argv (fn-stid-cli-plan), builds the request,
;;; recognizes it at the owner, seals the reply, reads it at the client and
;;; renders the line and the exit code (host/store-identity-host.lisp).  The
;;; handler is a read: books/native-control-kinds.lisp classifies kind 24 as
;;; :read, so it is not shed as a mutating request under disk pressure.

(in-package "ACL2")

(defun fnn-store-identity-owner-reply (service)
  "The sealed kind-25 reply, read under the owner mutex (the consumer state is
the owner's; a render never observes a half-applied transition)."
  (let ((running (fnn-string-octets (fnn-checkpoint-revision))))
    (fnn-owner-serialized
     service nil
     (lambda ()
       (let ((reply (fnn-owner-core 'fn-stid-host-reply
                                    (fnn-octet-list running))))
         (unless (and (consp reply) (fnn-octet-list-p reply))
           (fnn-fault "ACL2 returned a malformed store-identity reply"))
         reply))
     :inspect)))

(defvar *fnn-store-identity-next-handler* *fnn-hybrid-control-handler*)

(defun fnn-store-identity-control-handle (service frame)
  (if (and (typep frame 'fnn-octets)
           (fnn-core 'fn-stid-host-request-p (fnn-control-frame-octet-list frame)))
      (list :sealed-reply (fnn-store-identity-owner-reply service))
    (and *fnn-store-identity-next-handler*
         (funcall *fnn-store-identity-next-handler* service frame))))

(setq *fnn-hybrid-control-handler* #'fnn-store-identity-control-handle)

(defun fnn-command-store-identity (args)
  "`fn identity CONTROL': print ACL2's line for the owner's reply and exit by
its class (0 accepted, 1 refused by name, 3 no readable reply)."
  (let ((plan (and (<= (length args) 2)
                   (every (lambda (word) (<= (length word) 512)) args)
                   (fnn-core 'fn-stid-host-cli-plan
                             (mapcar #'fnn-ascii-octet-list args)))))
    (unless (and (consp plan) (eq (first plan) :run))
      (fnn-err "~a" (fnn-core 'fn-stid-host-usage))
      (return-from fnn-command-store-identity +fnn-exit-usage+))
    (multiple-value-bind (frame stage)
        (handler-case
            (fnn-control-exchange (fnn-octets-string (fnn-octets (second plan)))
                                  (fnn-core 'fn-stid-host-request))
          (error () (values nil :before-submission)))
      (if (null frame)
          ;; No reply frame: the transport stage says what the client knows.
          (let ((status (fnn-control-transport-outcome stage)))
            (fnn-err "fn-store-identity-~(~a~)-v1 transport" status)
            (fnn-core 'fn-native-control-host-status-exit-code status))
        (let ((value (fnn-core 'fn-stid-host-reply-read (fnn-octet-list frame))))
          (fnn-out "~a" (fnn-octets-string
                         (fnn-octets (fnn-core 'fn-stid-host-line value))))
          (fnn-core 'fn-stid-host-exit-code value))))))

(fnn-register-verb "identity"
                   (lambda (first rest)
                     ;; `fn identity' and `fn identity help' print the usage.
                     (if (and (equal first "help") (null rest))
                         (progn (fnn-out "~a" (fnn-core 'fn-stid-host-usage))
                                +fnn-exit-ok+)
                       (fnn-command-store-identity (cons first rest)))))
