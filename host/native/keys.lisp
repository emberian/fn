;;; `operator CONFIG keys redecide MSGID' (PRF-166, PKT-325; specs/peering.md
;;; 7.4).
;;;
;;; I/O only.  The operator sends the Message-ID to the running owner as
;;; control request 12 (books/peer-invite.lisp fn-pinv-redecide-request-*);
;;; the owner, under its mutex, asks ACL2 for the stored statement
;;; (fn-ks-find-statement), the one primitive observation it names (the proof
;;; of possession's D09 subject, fn-ks-pop-request), the plan
;;; (fn-ks-redecide-plan under the live grants, which are the grants in force
;;; at the redecide's own txid) and the kind-3 event (fn-ks-redecide-event),
;;; all through host/owner-host.lisp; it commits the event, logs ACL2's line
;;; and answers the status.  No statement is re-filed: the kind-3 change is
;;; the redecide's one durable record, so the next open repeats nothing
;;; (fn-ks-reopen-after-a-redecide).  Offline there is no owner to decide it:
;;; the request is refused like every live verb.

(in-package "ACL2")

(defun fnn-keys-owner-redecide (service msgid)
  (fnn-owner-serialized
   service nil
   (lambda ()
     (let* ((event (fnn-owner-core 'fn-owner-key-statement-redecide-find msgid))
            (request (and event
                          (fnn-owner-core 'fn-owner-key-statement-request
                                          event)))
            (preimage (and request
                           (fnn-core 'fn-hsig-host-preimage (first request)
                                     (second request) (third request))))
            (observations (and preimage
                               (fnn-hsig-observe-raw
                                (cdr (first (second request)))
                                (cdr (second (second request)))
                                preimage (fourth request))))
            (ml-observation (second observations))
            (observed-ml-key (and (consp ml-observation) (second ml-observation)
                                  (coerce (second ml-observation) 'list)))
            (ed (first observations))
            (ml (and (consp ml-observation) (first ml-observation)))
            (plan (fnn-owner-core 'fn-owner-key-statement-redecide-plan event
                                  observed-ml-key ed ml))
            (acting (and (consp plan) (member (first plan) '(:enroll :revoke))))
            (coordinates (and acting
                              (fnn-owner-core 'fn-owner-next-store-coordinates)))
            (kind3 (and acting
                        (fnn-owner-core 'fn-owner-key-statement-redecide-event
                                        event observed-ml-key ed ml
                                        coordinates)))
            (outcome
              (and kind3
                   (handler-case
                       (progn (fnn-owner-identity-commit service kind3)
                              :committed)
                     (fnn-store-indeterminate (e) (error e))
                     (fnn-store-fault (e) (error e))
                     (fnn-store-error () :refused)))))
       (fnn-log-line (fnn-owner-core 'fn-owner-key-statement-redecide-log-line
                                     plan outcome))
       (if (eq outcome :committed) :accepted :refused)))))

(defvar *fnn-keys-next-handler* *fnn-hybrid-control-handler*)

(defun fnn-keys-control-handle (service frame)
  (let ((msgid (and (typep frame 'fnn-octets)
                    (fnn-core 'fn-pinv-host-redecide-request-decode
                              (fnn-octet-list frame)))))
    (cond (msgid (fnn-keys-owner-redecide service msgid))
          (*fnn-keys-next-handler*
           (funcall *fnn-keys-next-handler* service frame))
          (t nil))))

(setq *fnn-hybrid-control-handler* #'fnn-keys-control-handle)

(defun fnn-keys-execute (result)
  "Execute an accepted `keys redecide MSGID' plan over the control socket."
  (let* ((msgid (fnn-core 'fn-native-operator-host-result-keys-msgid-octets
                          result))
         (control (fnn-core
                   'fn-native-operator-host-result-keys-control-path-octets
                   result))
         (control-path (and (fnn-octet-list-p control) (consp control)
                            (fnn-octets-string (fnn-octets control)))))
    (handler-case
        (let ((code
                (cond ((not (and (fnn-octet-list-p msgid) (consp msgid)))
                       (fnn-fault "ACL2 accepted a keys plan with no Message-ID"))
                      ((null control-path)
                       (fnn-refuse "the configuration names no control socket"))
                      (t
                       (let ((request (fnn-core
                                       'fn-pinv-host-redecide-request-encode
                                       msgid)))
                         (when (eq request :bad)
                           (fnn-refuse "ACL2 refused the redecide request"))
                         (fnn-core 'fn-native-control-host-status-exit-code
                                   (fnn-hybrid-control-send control-path
                                                            request)))))))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "keys")
          code)
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code)
                                    "keys" condition)
          code)))))
