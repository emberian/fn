; ACL2-owned constructors for the native FNWF entry points.  A record is
; returned only when the current workflow image accepts that exact record.
; Receipt ADU bytes are decoded canonically and the trusted-peer observation
; must be explicitly supplied; this book does not authenticate the peer.
(in-package "ACL2")
(include-book "bp-release")
(include-book "bp-adu")

(defun fn-bprl-undertake-record (s work-id charge)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((record (list :undertake work-id charge))
         (answer (fn-bprl-apply-journal-record s record)))
    (if (and (fn-bprl-undertake-recordp record) (car answer))
        record
      nil)))

(defun fn-bprl-receipt-from-adu (adu)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bp-make-receipt
   (fn-bpa-receipt-id adu) (fn-bpa-receipt-work-id adu)
   (fn-bpa-receipt-subject adu) (fn-bpa-receipt-issuer adu)
   (fn-bpa-receipt-peer-eid adu) (fn-bpa-receipt-policy-id adu)
   (fn-bpa-receipt-incarnation adu) (fn-bpa-receipt-auth-context adu)
   (fn-bpa-receipt-terms-id adu)))

(defun fn-bprl-receipt-intent-record (s octets txid generation authorizedp)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (equal authorizedp t))
      nil
    (let* ((decoded (fn-bpa-decode-exact octets))
           (adu (and (fn-bpa-result-okp decoded)
                     (fn-bpa-result-message decoded))))
      (if (not (fn-bpa-receiptp adu))
          nil
        (let* ((receipt (fn-bprl-receipt-from-adu adu))
               (record
                (list :receipt-intent txid generation
                      (fn-bp-receipt-id receipt)
                      (fn-bp-receipt-work-id receipt)
                      (fn-bp-receipt-subject receipt)
                      (fn-bp-receipt-issuer receipt)
                      (fn-bp-receipt-peer-eid receipt)
                      (fn-bp-receipt-policy-id receipt)
                      (fn-bp-receipt-incarnation receipt)
                      (fn-bp-receipt-auth-context receipt)
                      (fn-bp-receipt-terms-id receipt)))
               (answer (fn-bprl-apply-journal-record s record)))
          (if (and (fn-bp-journal-recordp record) (car answer))
              record
            nil))))))

(defun fn-bprl-release-record-for-journal (s receipt-id)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((record (fn-bprl-release-record s receipt-id))
         (answer (fn-bprl-apply-journal-record s record)))
    (if (and (fn-bprl-release-recordp record) (car answer))
        record
      nil)))

; These are the exact ACL2 preflight facts the native host relies on before
; publishing.  The underlying release and receipt authority proofs live in
; bp-release-invariants and bp-workflow-records-invariants respectively.
(defthm fn-bprl-undertake-record-preflights
  (implies (fn-bprl-undertake-record s work-id charge)
           (and (fn-bprl-undertake-recordp
                 (fn-bprl-undertake-record s work-id charge))
                (car (fn-bprl-apply-journal-record
                      s (fn-bprl-undertake-record s work-id charge)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bprl-apply-journal-record
                                      fn-bprl-undertake-recordp))))

(defthm fn-bprl-receipt-intent-record-preflights
  (implies (fn-bprl-receipt-intent-record
            s octets txid generation authorizedp)
           (and (equal authorizedp t)
                (fn-bp-journal-recordp
                 (fn-bprl-receipt-intent-record
                  s octets txid generation authorizedp))
                (car (fn-bprl-apply-journal-record
                      s (fn-bprl-receipt-intent-record
                         s octets txid generation authorizedp)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bpa-decode-exact
                                      fn-bpa-receiptp
                                      fn-bp-journal-recordp
                                      fn-bprl-apply-journal-record))))

(defthm fn-bprl-release-record-for-journal-preflights
  (implies (fn-bprl-release-record-for-journal s receipt-id)
           (and (fn-bprl-release-recordp
                 (fn-bprl-release-record-for-journal s receipt-id))
                (car (fn-bprl-apply-journal-record
                      s (fn-bprl-release-record-for-journal s receipt-id)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bprl-release-record
                                      fn-bprl-release-recordp
                                      fn-bprl-apply-journal-record))))
