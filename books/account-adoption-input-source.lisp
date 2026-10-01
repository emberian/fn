; Captured actual operator input. Constructors are INTERNAL after the SAME
; installed begin allowance/receipt. No source key or candidate authorizes
; credentials, allocation, publication, namespace uniqueness or retirement.
(in-package "ACL2")
(include-book "consumer-account-adoption-state")
(include-book "consumer-position-fields")

(defun fn-cado-widthp (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (null x)
  (and (consp x) (fn-cado-widthp (1- n) (cdr x)))))

; Constant source coordinate domains, not a credential-table recognizer.
(defun fn-cado-receipt-coordinatep (receipt)
 (declare (xargs :guard t))
 (and (fn-cado-widthp 4 receipt)
      (eq (fn-cp-nth 0 receipt) :account-preparation-turn)
      (natp (fn-cp-nth 1 receipt)) (natp (fn-cp-nth 2 receipt))
      (natp (fn-cp-nth 3 receipt))))

(defun fn-cado-source-keyp (key)
 (declare (xargs :guard t))
 (and (fn-cado-widthp 6 key)
      (eq (fn-cp-nth 0 key) :account-adoption-source)
      (fn-cado-receipt-coordinatep (fn-cp-nth 1 key))
      (natp (fn-cp-nth 2 key)) (natp (fn-cp-nth 3 key))
      (fn-cado-widthp 32 (fn-cp-nth 4 key))
      (fn-cbor-octet-listp (fn-cp-nth 4 key))
      (fn-cp-uintp (fn-cp-nth 5 key))))

; Fixed6: real typed account-turn receipt, epoch/config generation, captured incarnation,
; observed first txid. Observation is rebound by the sole authority-begin
; selector before any durable stage; it is never a transaction reservation.
(defun fn-cado-source-key (receipt epoch generation incarnation txid)
 (declare (xargs :guard t))
 (list :account-adoption-source receipt epoch generation incarnation txid))

; Fixed8. Parsed config/bindings, entropy, base config and redeemed rows are
; borrowed original refs, never copied or rescanned at a candidate fence.
(defun fn-cado-request (config bindings entropy base-config source candidate redeemed)
 (declare (xargs :guard t))
 (list :account-adoption-request config bindings entropy base-config source candidate redeemed))

(defun fn-owner-account-adoption-request-install (request state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-account-adoption-request request state))

; Readonly core readout from the CURRENT retained request and job. Equality
; concerns only the issued fixed source key, never config/groups/input lists.
(defun fn-owner-account-adoption-source (state)
 (declare (xargs :stobjs state :guard t))
 (let* ((request (fn-owner-account-adoption-request state))
        (key (fn-cp-nth 5 request))
        (job (fn-owner-account-adoption-job state)))
  (if (and (eq (fn-cp-nth 0 request) :account-adoption-request)
           (fn-cado-source-keyp key)
           (fn-cado-source-keyp (fn-cp-nth 2 job))
           (eq (fn-cp-nth 0 job) :account-adoption-job)
           (equal key (fn-cp-nth 2 job)))
      (mv :source-current key (fn-cp-nth 4 key) (fn-cp-nth 5 key))
    (mv :account-adoption-source-unavailable nil nil nil))))

(in-theory (disable fn-cado-widthp fn-cado-receipt-coordinatep fn-cado-source-keyp
                    fn-cado-source-key fn-cado-request
                    fn-owner-account-adoption-request-install
                    fn-owner-account-adoption-source))
