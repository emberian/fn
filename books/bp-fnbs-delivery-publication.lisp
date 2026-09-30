; ACL2 authority for a kind-7 FNBS result.  The host may publish only the
; exact pending application result with the state-owned epoch/operation id.
(in-package "ACL2")
(include-book "bp-fnbs-delivery-codec")
(include-book "bp-fnbs-byte-publisher")
(include-book "consumer-position")
(set-verify-guards-eagerness 0)

(defun fn-bpah-publication-authorize
  (st epoch operation-id record lock-owned final-absent)
  ;; The *1* class (Q4a item 2): host-called; the guard names the kinds the
  ;; host passes (the entry guard checks them by name) and the wrapper runs raw.
  (declare (xargs :guard (and (fn-frame-natp epoch) (fn-frame-natp operation-id))
                  :verify-guards nil))
  (let ((issued (fn-bpnf-issued st)))
    (if (and (fn-bpnf-operationp issued)
             (fn-bpnf-operation-matchp issued epoch operation-id)
             (equal (fn-bpn-nth 3 issued) :deliver)
             (equal (fn-bpn-nth 4 issued) record)
             (equal (fn-bpn-nth 5 issued) :pending)
             (equal (fn-bpnf-epoch st) epoch)
             (equal (fn-bpnf-next-op st) (1+ operation-id))
             (fn-bpah-delivery-recordp record)
             (equal (fn-bpn-nth 1 record) epoch)
             (equal (fn-bpn-nth 2 record) operation-id)
             lock-owned final-absent)
        (let ((frame (fn-bpah-delivery-frame record)))
          (if (equal frame :bad)
              (list :fault :delivery-codec)
            (list :ok epoch operation-id record
                  (fn-bpnf-stored-record-name epoch operation-id)
                  frame (fn-jpub-initial t))))
      (list :fault :delivery-authority))))

(defun fn-bpah-publication-operationp (operation)
  (declare (xargs :guard t))
  (and (true-listp operation) (equal (len operation) 7)
       (equal (car operation) :ok)
       (fn-frame-natp (nth 1 operation))
       (fn-frame-natp (nth 2 operation))
       (fn-bpah-delivery-recordp (nth 3 operation))
       (equal (nth 4 operation)
              (fn-bpnf-stored-record-name (nth 1 operation)
                                            (nth 2 operation)))
       (equal (nth 5 operation)
              (fn-bpah-delivery-frame (nth 3 operation)))
       (not (equal (nth 5 operation) :bad))
       (equal (nth 6 operation) (fn-jpub-initial t))))

(defun fn-bpah-publication-name (operation)
  (declare (xargs :guard (true-listp operation))) (nth 4 operation))
(defun fn-bpah-publication-frame (operation)
  (declare (xargs :guard (true-listp operation))) (nth 5 operation))
(defun fn-bpah-publication-publisher (operation)
  (declare (xargs :guard (true-listp operation))) (nth 6 operation))

(verify-guards fn-bpah-publication-authorize)
(verify-guards fn-bpah-publication-operationp)
(verify-guards fn-bpah-publication-name)
(verify-guards fn-bpah-publication-frame)
(verify-guards fn-bpah-publication-publisher)

(defthm fn-bpah-publication-success-binds-pending-echo
  (implies (equal (car (fn-bpah-publication-authorize
                       st epoch operation-id record lock-owned final-absent))
                  :ok)
           (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :deliver)
                (equal (fn-bpn-nth 4 (fn-bpnf-issued st)) record)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (equal (fn-bpnf-epoch st) epoch)
                (equal (fn-bpnf-next-op st) (1+ operation-id))
                lock-owned final-absent))
  :hints (("Goal" :in-theory (e/d (fn-bpah-publication-authorize)
                                (fn-bpah-delivery-recordp
                                 fn-bpah-delivery-frame
                                 fn-bpnf-operationp
                                 fn-bpnf-operation-matchp))))
  :rule-classes nil)

; A stored record's epoch and operation id are frame naturals (the record
; recognizer says so); stated once so the keystone keeps the recognizer closed.
(defthm fn-bpah-delivery-record-epoch-and-op-are-frame-nats
  (implies (fn-bpah-delivery-recordp record)
           (and (fn-frame-natp (fn-bpn-nth 1 record))
                (fn-frame-natp (fn-bpn-nth 2 record))))
  :hints (("Goal" :in-theory (e/d (fn-bpah-delivery-recordp)
                                  (fn-frame-natp)))))

; KEYSTONE (PRF-1013).  The publication authorization, two-sided: the principal
; (the caller holds the publication lock), the policy context (the issued
; operation is the pending :deliver of this epoch and operation id, the record
; is the one it carries, the epoch and next operation id are the state's) and
; the evidence (the final name observed absent) in the conclusion; an
; operation is issued exactly under them and a framable record, and then it
; carries the epoch, the id, the record, the stored name, the frame and an
; initial authorized publication; otherwise one of the two faults.  It
; subsumes the one-sided echo theorem above.
(defthm fn-bpah-publication-authorize-admits-exactly-the-issued-pending-delivery
  (let ((answer (fn-bpah-publication-authorize st epoch operation-id record lock-owned final-absent))
        (issued (fn-bpnf-issued st)))
    (and (iff (fn-bpah-publication-operationp answer)
              (and (fn-bpnf-operationp issued)
                   (fn-bpnf-operation-matchp issued epoch operation-id)
                   (equal (fn-bpn-nth 3 issued) :deliver)
                   (equal (fn-bpn-nth 4 issued) record)
                   (equal (fn-bpn-nth 5 issued) :pending)
                   (equal (fn-bpnf-epoch st) epoch)
                   (equal (fn-bpnf-next-op st) (1+ operation-id))
                   (fn-bpah-delivery-recordp record)
                   (equal (fn-bpn-nth 1 record) epoch)
                   (equal (fn-bpn-nth 2 record) operation-id)
                   lock-owned final-absent
                   (not (equal (fn-bpah-delivery-frame record) :bad))))
         (implies (fn-bpah-publication-operationp answer)
                  (and (equal (nth 1 answer) epoch)
                       (equal (nth 2 answer) operation-id)
                       (equal (nth 3 answer) record)
                       (equal (fn-bpah-publication-name answer)
                              (fn-bpnf-stored-record-name epoch operation-id))
                       (equal (fn-bpah-publication-frame answer) (fn-bpah-delivery-frame record))
                       (equal (nth 6 answer) (fn-jpub-initial t))))
         (implies (not (fn-bpah-publication-operationp answer))
                  (or (equal answer '(:fault :delivery-authority))
                      (equal answer '(:fault :delivery-codec))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpah-delivery-record-epoch-and-op-are-frame-nats))
           :in-theory (e/d (fn-bpah-publication-authorize fn-bpah-publication-operationp fn-bpah-publication-name fn-bpah-publication-frame)
                           (fn-bpnf-operationp fn-bpnf-operation-matchp
                            fn-bpah-delivery-recordp fn-bpah-delivery-frame fn-bpnf-stored-record-name
                            fn-bpnf-issued fn-bpnf-epoch fn-bpnf-next-op
                            fn-jpub-initial fn-frame-natp)))))
