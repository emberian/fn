; ACL2 authority for the exact pending kind-18 family replacement image.
(in-package "ACL2")
(include-book "bp-node-fragment-step")
(include-book "bp-fnbs-byte-publisher")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-family-publication-authorize
  (st epoch op record lock-owned final-absent)
  (declare (xargs :guard t))
  (let ((issued (fn-bpnf-issued st)))
    (if (and (fn-bpnf-operationp issued)
             (fn-bpnf-operation-matchp issued epoch op)
             (equal (fn-bpn-nth 3 issued) :family)
             (equal (fn-bpn-nth 4 issued) record)
             (equal (fn-bpn-nth 5 issued) :pending)
             (equal (fn-bpnf-epoch st) epoch)
             (equal (fn-bpnf-next-op st) (1+ op))
             (equal (fn-bpnf-next-arrival st)
                    (1+ (fn-bpn-nth 4 record)))
             (fn-bpnf-family-record-atp record)
             (equal (fn-bpn-nth 1 record) epoch)
             (equal (fn-bpn-nth 2 record) op)
             lock-owned final-absent)
        (let ((frame (fn-bpnf-family-v1-frame record)))
          (if (equal frame :bad)
              (list :fault :family-codec)
            (list :ok epoch op record
                  (fn-bpnf-stored-record-name epoch op)
                  frame (fn-jpub-initial t))))
      (list :fault :family-authority))))

(defun fn-bpnf-family-publication-operationp (operation)
  (declare (xargs :guard t))
  (and (true-listp operation) (equal (len operation) 7)
       (equal (car operation) :ok)
       (fn-frame-natp (nth 1 operation))
       (fn-frame-natp (nth 2 operation))
       (fn-bpnf-family-record-atp (nth 3 operation))
       (equal (nth 4 operation)
              (fn-bpnf-stored-record-name (nth 1 operation)
                                          (nth 2 operation)))
       (equal (nth 5 operation)
              (fn-bpnf-family-v1-frame (nth 3 operation)))
       (not (equal (nth 5 operation) :bad))
       (equal (nth 6 operation) (fn-jpub-initial t))))

(defun fn-bpnf-family-publication-name (operation)
  (declare (xargs :guard t)) (nth 4 operation))
(defun fn-bpnf-family-publication-frame (operation)
  (declare (xargs :guard t)) (nth 5 operation))
(defun fn-bpnf-family-publication-publisher (operation)
  (declare (xargs :guard t)) (nth 6 operation))

(defthm fn-bpnf-family-publication-success-binds-exact-echo
  (implies (equal (car (fn-bpnf-family-publication-authorize
                       st epoch op record lock-owned final-absent)) :ok)
           (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :family)
                (equal (fn-bpn-nth 4 (fn-bpnf-issued st)) record)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (equal (fn-bpnf-epoch st) epoch)
                (equal (fn-bpnf-next-op st) (1+ op))
                (equal (fn-bpnf-next-arrival st)
                       (1+ (fn-bpn-nth 4 record)))
                lock-owned final-absent))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnf-family-publication-authorize)
                           (fn-bpnf-operationp
                            fn-bpnf-operation-matchp
                            fn-bpnf-family-record-atp
                            fn-bpnf-family-v1-frame))))
  :rule-classes nil)

; A stored record's epoch and operation id are frame naturals (the record
; recognizer says so); stated once so the keystone keeps the recognizer closed.
(defthm fn-bpnf-family-record-at-epoch-and-op-are-frame-nats
  (implies (fn-bpnf-family-record-atp record)
           (and (fn-frame-natp (fn-bpn-nth 1 record))
                (fn-frame-natp (fn-bpn-nth 2 record))))
  :hints (("Goal" :in-theory (e/d (fn-bpnf-family-record-atp fn-bpnf-family-recordp fn-bpnf-family-record fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr)
                                  (fn-frame-natp)))))

; KEYSTONE (PRF-1015).  The publication authorization, two-sided: the principal
; (the caller holds the publication lock), the policy context (the issued
; operation is the pending :family of this epoch and operation id, the record
; is the one it carries, the epoch and next operation id are the state's) and
; the evidence (the final name observed absent) in the conclusion; an
; operation is issued exactly under them and a framable record, and then it
; carries the epoch, the id, the record, the stored name, the frame and an
; initial authorized publication; otherwise one of the two faults.  It
; subsumes the one-sided echo theorem above.
(defthm fn-bpnf-family-publication-authorize-admits-exactly-the-issued-pending-family
  (let ((answer (fn-bpnf-family-publication-authorize st epoch op record lock-owned final-absent))
        (issued (fn-bpnf-issued st)))
    (and (iff (fn-bpnf-family-publication-operationp answer)
              (and (fn-bpnf-operationp issued)
                   (fn-bpnf-operation-matchp issued epoch op)
                   (equal (fn-bpn-nth 3 issued) :family)
                   (equal (fn-bpn-nth 4 issued) record)
                   (equal (fn-bpn-nth 5 issued) :pending)
                   (equal (fn-bpnf-epoch st) epoch)
                   (equal (fn-bpnf-next-op st) (1+ op))
                   (equal (fn-bpnf-next-arrival st)
                          (1+ (fn-bpn-nth 4 record)))
                   (fn-bpnf-family-record-atp record)
                   (equal (fn-bpn-nth 1 record) epoch)
                   (equal (fn-bpn-nth 2 record) op)
                   lock-owned final-absent
                   (not (equal (fn-bpnf-family-v1-frame record) :bad))))
         (implies (fn-bpnf-family-publication-operationp answer)
                  (and (equal (nth 1 answer) epoch)
                       (equal (nth 2 answer) op)
                       (equal (nth 3 answer) record)
                       (equal (fn-bpnf-family-publication-name answer)
                              (fn-bpnf-stored-record-name epoch op))
                       (equal (fn-bpnf-family-publication-frame answer) (fn-bpnf-family-v1-frame record))
                       (equal (nth 6 answer) (fn-jpub-initial t))))
         (implies (not (fn-bpnf-family-publication-operationp answer))
                  (or (equal answer '(:fault :family-authority))
                      (equal answer '(:fault :family-codec))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpnf-family-record-at-epoch-and-op-are-frame-nats))
           :in-theory (e/d (fn-bpnf-family-publication-authorize fn-bpnf-family-publication-operationp fn-bpnf-family-publication-name fn-bpnf-family-publication-frame)
                           (fn-bpnf-operationp fn-bpnf-operation-matchp
                            fn-bpnf-family-record-atp fn-bpnf-family-v1-frame fn-bpnf-stored-record-name
                            fn-bpnf-issued fn-bpnf-epoch fn-bpnf-next-op
                            fn-jpub-initial fn-frame-natp)))))
