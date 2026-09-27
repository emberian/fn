; Program-mode bridge for the receiver-side fn-bpr model.  It never decodes a
; BP request in Python and has no receipt side effect: callers must persist
; context/decision through Sol's receiver journal before transmitting bytes.
(in-package "ACL2")
(include-book "../books/bp-receipt")
(include-book "../books/bp-native-app-fast")

(defun fn-bpr-host-request (adu)
  (let ((answer (fn-bpa-decode-exact adu)))
    (if (and (fn-bpa-result-okp answer)
             (fn-bpa-requestp (fn-bpa-result-message answer)))
        (fn-bpa-result-message answer)
      nil)))

(defun fn-bpr-host-request-article (adu state)
  (declare (xargs :stobjs state :mode :program))
  (let ((request (fn-bpr-host-request adu)))
    (if request (value (fn-bpa-request-article request)) (value nil))))

(defun fn-bpr-host-reset (config state)
  (declare (xargs :stobjs state :mode :program))
  (if (fn-bpr-configp config)
      (let ((state (f-put-global 'fn-bpr-state (fn-bpr-initial-state config) state)))
        (value :ready))
    (value :invalid)))

; `policy-authorizedp` is supplied from explicitly trusted local lab policy.
; The decoded request auth-context is never used in place of that input.
; The record is ACL2's: the request article's own Message-ID selects it
; through the Store's event index (fn-bpaj-record-lookup-fast, equal to the
; history walk fn-bpaj-record-lookup under fn-ceis-indexedp), and two
; records under one Message-ID are a conflict, never a host's first pick.
; The receiver transition is the carried one
; (fn-bpaj-bpr-accept-request-fast, equal to fn-bpr-accept-request under
; fn-bpr-statep, fn-sn-statep and fn-ceis-indexedp): no whole-Store
; recognizer and no history walk runs per request (PRF-220, PKT-448 (a), (g)).
(defun fn-bpr-host-accept (adu policy-authorizedp state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((request (fn-bpr-host-request adu))
         (store (f-get-global 'fn-store-sn state))
         (lookup (and request (fn-bpaj-record-lookup-fast store request)))
         (record (and (equal (car lookup) :found) (cadr lookup)))
         (old (f-get-global 'fn-bpr-state state))
         (answer (if (and request record)
                     (fn-bpaj-bpr-accept-request-fast
                      old store record request policy-authorizedp)
                   (list :refused old))))
    (let ((state (f-put-global 'fn-bpr-state (car (cdr answer)) state)))
      (value (car answer)))))

(defun fn-bpr-host-prepare-receipt (work-id receipt-id policy-authorizedp state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((old (f-get-global 'fn-bpr-state state))
         (next (fn-bpr-prepare-receipt old work-id receipt-id policy-authorizedp)))
    (let ((state (f-put-global 'fn-bpr-state next state)))
      (value (if (consp (fn-bpr-state-pending next)) :pending :refused)))))

(defun fn-bpr-host-commit-receipt (work-id receipt-id outcome state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((old (f-get-global 'fn-bpr-state state))
         (next (fn-bpr-commit-receipt old work-id receipt-id outcome)))
    (let ((state (f-put-global 'fn-bpr-state next state)))
      (value (if (and (equal outcome :committed)
                       (null (fn-bpr-state-pending next)))
                 :committed :unchanged)))))

(defun fn-bpr-host-receipt-adu (adu state)
  (declare (xargs :stobjs state :mode :program))
  (let ((request (fn-bpr-host-request adu)))
    (value (if request
               (fn-bpr-receipt-adu (f-get-global 'fn-bpr-state state) request)
             nil))))
