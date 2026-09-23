;;; Shared-owner native surface for durable forwarding obligations.
(in-package "ACL2")

(defun fnn-bpo-call-with-owner-journal
    (store-root journal-root writable thunk)
  (let ((service nil) (journal nil))
    (unwind-protect
         (progn
           (setq service (fnn-owner-install store-root 1))
           (fnn-owner-serialized
            service nil
            (lambda ()
              (setq journal
                    (fnn-app-open (fnn-owner-service-store service)
                                  journal-root :workflow :owner-mode t))
              (when (and writable
                         (fnn-store-fenced (fnn-owner-service-store service)))
                (fnn-indeterminate "BP obligation owner Store is fenced"))
              (funcall thunk journal service))))
      (when journal (fnn-app-journal-close journal))
      (when service
        (fnn-owner-feed-close-all service)
        (fnn-store-close (fnn-owner-service-store service))))))

(defun fnn-command-bpo-owner-status (store journal work-id)
  (fnn-bpo-call-with-owner-journal
   store journal nil
   (lambda (opened service)
     (declare (ignore service))
     (declare (ignore opened))
     (fnn-out "BP obligation owner work=~a status=~(~a~) pinned=~a"
              work-id (fnn-core-state 'fn-workflow-work-status work-id)
              (if (eq (fnn-owner-core
                       'fn-owner-workflow-forward-pinnedp work-id) t)
                  "yes" "no"))
     +fnn-exit-ok+)))

(defun fnn-command-bpo-owner-undertake (store journal work-id charge)
  (fnn-bpo-call-with-owner-journal
   store journal t
   (lambda (opened service)
     (let ((event (fnn-owner-core 'fn-owner-workflow-store-undertake work-id charge)))
       (unless event (fnn-refuse "workflow forwarding obligation is not admissible"))
       (fnn-owner-retention-commit service event))
     (fnn-owner-action 'fn-owner-workflow-sync-store-node)
     (fnn-out "BP obligation owner durable undertaking work=~a charge=~d"
              work-id charge)
     +fnn-exit-ok+)))

(defun fnn-bpo-canonical-release (service release)
  (let ((event (fnn-owner-core 'fn-owner-workflow-store-release release)))
    (unless event
      (fnn-fault "committed receipt has no canonical Store release"))
    ;; The owner path releases through Store, so the developer namespace cut
    ;; belongs to that canonical publication, not an FNWF :release record.
    (let* ((cut-fired nil)
           (release-cut
             (string= (or (fnn-developer-selector
                           "FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE") "") "1"))
           (*fnn-record-directory-fault-observer*
             (and release-cut
                  (lambda (path)
                    (setq cut-fired t)
                    (fnn-os-fail sb-posix:eio path)))))
      (handler-case
          (fnn-owner-retention-commit service event)
        (fnn-store-indeterminate (e)
          (if cut-fired
              (fnn-indeterminate
               "application release publication is uncertain")
            (error e)))))
    (fnn-owner-action 'fn-owner-workflow-sync-store-node)))

(defun fnn-command-bpo-owner-receipt
    (store journal receipt txid generation profile)
  (fnn-bpo-call-with-owner-journal
   store journal t
   (lambda (opened service)
     (let ((receipt-id
            (fnn-workflow-accept-receipt
             opened receipt txid generation profile
             (lambda (release)
               (fnn-bpo-canonical-release service release)))))
       (fnn-out "BP obligation owner durable release receipt=~a profile=~a"
                receipt-id profile)
       +fnn-exit-ok+))))

(defun fnn-dispatch-bp-obligation (command args)
  (flet ((need (n)
           (when (< (length args) n)
             (error 'fnn-usage-error
                    :message "bp-obligation: missing arguments"))))
    (cond
      ((string= command "status")
       (need 3)
       (fnn-command-bpo-owner-status (first args) (second args) (third args)))
      ((string= command "undertake")
       (need 4)
       (fnn-command-bpo-owner-undertake
        (first args) (second args) (third args) (parse-integer (fourth args))))
      ((string= command "receipt")
       (need 6)
       (fnn-command-bpo-owner-receipt
        (first args) (second args) (third args)
        (parse-integer (fourth args)) (parse-integer (fifth args))
        (sixth args)))
      (t (error 'fnn-usage-error
                :message (format nil "unknown bp-obligation command ~a"
                                 command))))))

(fnn-register-verb "bp-obligation" #'fnn-dispatch-bp-obligation)
