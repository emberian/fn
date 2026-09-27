; ACL2-only request projections for the filesystem receiver glue.
(in-package "ACL2")
(include-book "../books/bp-receipt")
(include-book "../books/bp-native-app-fast")
(defun fn-bpreq-request (adu)
  (let ((answer (fn-bpa-decode-exact adu)))
    (if (and (fn-bpa-result-okp answer)
             (fn-bpa-requestp (fn-bpa-result-message answer)))
        (fn-bpa-result-message answer) nil)))
(defun fn-bpreq-article (adu state)
  (declare (xargs :stobjs state :mode :program))
  (let ((request (fn-bpreq-request adu)))
    (value (if request (fn-bpa-request-article request) nil))))
(defun fn-bpreq-work-id (adu state)
 (declare (xargs :stobjs state :mode :program))
 (let ((request (fn-bpreq-request adu)))
  (value (if request (fn-record-string-octets (fn-bpa-request-work-id request)) nil))))
; The Store record for a request, by ACL2's lookup through the event index
; (fn-bpaj-record-lookup-fast: the request article's Message-ID, the
; checked Store predicate fn-bpr-store-record-acceptedp under
; fn-sn-statep and fn-ceis-indexedp); no history walk and no whole-Store
; recognizer per request (PRF-220, PKT-448 (a), (g)).
(defun fn-bpreq-existing-record (adu state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((request (fn-bpreq-request adu))
        (store (f-get-global 'fn-store-sn state))
        (lookup (and request (fn-bpaj-record-lookup-fast store request))))
  (value (if (equal (car lookup) :found)
             (fn-record-encode (cadr lookup)) nil))))
(defun fn-bpreq-request-status (adu state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((request (fn-bpreq-request adu))
        (st (f-get-global 'fn-bprj-state state)))
  (value
   (if (not request) :malformed
    (if (not (and (equal (fn-bpa-request-destination-eid request)
                        (fn-bpr-config-destination (fn-bpr-state-config st)))
                  (equal (fn-bpa-request-policy-id request)
                        (fn-bpr-config-policy-id (fn-bpr-state-config st)))))
        :refused
      (let* ((work-id (fn-bpa-request-work-id request))
             (context (fn-bpr-find-context work-id (fn-bpr-state-contexts st)))
             (pending (fn-bpr-state-pending st)))
       (cond ((and context (not (equal (fn-bpaj-request-ref request)
                                       (fn-bpr-context-request-ref context))))
              :conflict)
             ((and context (fn-bpr-receipt-adu st request)) :committed)
             ((consp pending)
              (if (equal work-id
                         (fn-bpr-context-work-id
                          (fn-bpr-receipt-entry-context pending)))
                  :pending :blocked))
             (context :context)
             (t :new))))))))
(defun fn-bpreq-subject-matchp (adu subject-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((request (fn-bpreq-request adu)))
    (value (if request
               (equal (fn-bpa-request-subject request)
                      (fn-record-octets-string subject-octets)) nil))))
