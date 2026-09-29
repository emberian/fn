; ACL2-owned constructors for the native FNWF entry points.  A record is
; returned only when the current workflow image accepts that exact record.
; Receipt ADU bytes are decoded canonically and the trusted-peer observation
; must be explicitly supplied; this book does not authenticate the peer.
(in-package "ACL2")
(include-book "bp-release")
(include-book "bp-adu")
(include-book "rev-onto")

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

; A native inbound receipt has no operator-supplied transaction pair.  The
; recovered FNWF image owns the entire used-pair history, including aborted
; preparations, so choose above every previously used transaction id.
; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element of the used-transaction history (data, not a bound).  The :logic is
; the recursion, unchanged; the :exec is a loop, equal by fn-bprl-max-used-txid-loop-of-rev-onto (a right fold, run from the left over the reversed list).
(defun fn-bprl-max-used-txid-step (x rest)
  (declare (xargs :guard (natp rest)))
  (max (nfix (fn-bp-nth 0 x)) rest))

(defun fn-bprl-max-used-txid-loop (rev acc)
  (declare (xargs :guard (natp acc)))
  (if (consp rev)
      (fn-bprl-max-used-txid-loop (cdr rev) (fn-bprl-max-used-txid-step (car rev) acc))
    acc))

(defun fn-bprl-max-used-txid (used maximum)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (atom used)
                  (nfix maximum)
                (max (nfix (fn-bp-nth 0 (car used)))
                     (fn-bprl-max-used-txid (cdr used) maximum)))
       :exec (fn-bprl-max-used-txid-loop (fn-ag-rev-onto used nil) (nfix maximum))))

(defthm fn-bprl-max-used-txid-loop-of-rev-onto
  (equal (fn-bprl-max-used-txid-loop (fn-ag-rev-onto used zs) (nfix maximum))
         (fn-bprl-max-used-txid-loop zs (fn-bprl-max-used-txid used maximum)))
  :hints (("Goal" :induct (fn-ag-rev-onto used zs)
                  :in-theory (union-theories
                              '(fn-bprl-max-used-txid-loop fn-bprl-max-used-txid fn-bprl-max-used-txid-step fn-ag-rev-onto atom car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(defthm fn-bprl-max-used-txid-natp
  (natp (fn-bprl-max-used-txid used maximum))
  :rule-classes :type-prescription)

(defthm fn-bprl-max-used-txid-loop-natp
  (implies (natp acc) (natp (fn-bprl-max-used-txid-loop rev acc)))
  :rule-classes :type-prescription)

(verify-guards fn-bprl-max-used-txid
  :hints (("Goal" :use ((:instance fn-bprl-max-used-txid-loop-of-rev-onto (zs nil))))))

(defun fn-bprl-receipt-auto-record (s octets authorizedp)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bp-statep s))
      nil
    (fn-bprl-receipt-intent-record
     s octets (1+ (fn-bprl-max-used-txid (fn-bp-state-used-txs s) 0))
     0 authorizedp)))

(defthm fn-bprl-max-used-txid-bounds-members
  (implies (member-equal pair used)
           (<= (nfix (fn-bp-nth 0 pair))
               (fn-bprl-max-used-txid used maximum)))
  :hints (("Goal" :in-theory (enable fn-bprl-max-used-txid))))

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
