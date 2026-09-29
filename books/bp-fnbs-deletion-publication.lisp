; ACL2 authorization for the exact pending kind-10 tombstone image.
(in-package "ACL2")
(include-book "bp-node-report-step")
(include-book "bp-fnbs-byte-publisher")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-delete-publication-authorize
  (st epoch op record lock-owned final-absent)
  (declare (xargs :guard t))
  (let* ((issued (fn-bpnf-issued st))
         (detail (fn-bpn-nth 4 issued)))
    (if (and (fn-bpnf-operationp issued)
             (fn-bpnf-operation-matchp issued epoch op)
             (equal (fn-bpn-nth 3 issued) :delete)
             (equal (fn-bpn-nth 0 detail) record)
             (equal (fn-bpn-nth 5 issued) :pending)
             (equal (fn-bpnf-epoch st) epoch)
             (equal (fn-bpnf-next-op st) (1+ op))
             (fn-bpn-report-delete-recordp record)
             (equal (fn-bpn-nth 1 record) epoch)
             (equal (fn-bpn-nth 2 record) op)
             lock-owned final-absent)
        (let ((frame (fn-bpnf-delete-frame record)))
          (if (equal frame :bad)
              (list :fault :delete-codec)
            (list :ok epoch op record
                  (fn-bpnf-stored-record-name epoch op)
                  frame (fn-jpub-initial t))))
      (list :fault :delete-authority))))

(defun fn-bpnf-delete-publication-operationp (operation)
  (declare (xargs :guard t))
  (and (true-listp operation) (equal (len operation) 7)
       (equal (car operation) :ok)
       (fn-frame-natp (nth 1 operation))
       (fn-frame-natp (nth 2 operation))
       (fn-bpn-report-delete-recordp (nth 3 operation))
       (equal (nth 4 operation)
              (fn-bpnf-stored-record-name (nth 1 operation)
                                          (nth 2 operation)))
       (equal (nth 5 operation)
              (fn-bpnf-delete-frame (nth 3 operation)))
       (not (equal (nth 5 operation) :bad))
       (equal (nth 6 operation) (fn-jpub-initial t))))

(defun fn-bpnf-delete-publication-name (operation)
  (declare (xargs :guard t)) (nth 4 operation))
(defun fn-bpnf-delete-publication-frame (operation)
  (declare (xargs :guard t)) (nth 5 operation))
(defun fn-bpnf-delete-publication-publisher (operation)
  (declare (xargs :guard t)) (nth 6 operation))

(defthm fn-bpnf-delete-publication-success-binds-exact-echo
  (implies (equal (car (fn-bpnf-delete-publication-authorize
                       st epoch op record lock-owned final-absent)) :ok)
           (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :delete)
                (equal (fn-bpn-nth 0
                        (fn-bpn-nth 4 (fn-bpnf-issued st))) record)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (equal (fn-bpnf-epoch st) epoch)
                (equal (fn-bpnf-next-op st) (1+ op))
                lock-owned final-absent))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnf-delete-publication-authorize)
                           (fn-bpnf-operationp
                            fn-bpnf-operation-matchp
                            fn-bpn-report-delete-recordp
                            fn-bpnf-delete-frame))))
  :rule-classes nil)

; fn-bpn-nth agrees with nth inside a true list (the deletion record
; recognizer is stated with nth, the authorization with fn-bpn-nth).
(defthm fn-bpn-nth-is-nth-on-true-lists
  (implies (and (natp n) (true-listp x) (< n (len x)))
           (equal (fn-bpn-nth n x) (nth n x)))
  :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr))))

; A stored record's epoch and operation id are frame naturals (the record
; recognizer says so); stated once so the keystone keeps the recognizer closed.
(defthm fn-bpn-report-delete-record-epoch-and-op-are-frame-nats
  (implies (fn-bpn-report-delete-recordp record)
           (and (fn-frame-natp (fn-bpn-nth 1 record))
                (fn-frame-natp (fn-bpn-nth 2 record))))
  :hints (("Goal" :in-theory (e/d (fn-bpn-report-delete-recordp fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr)
                                  (fn-frame-natp)))))

; KEYSTONE (PRF-1014).  The publication authorization, two-sided: the principal
; (the caller holds the publication lock), the policy context (the issued
; operation is the pending :delete of this epoch and operation id, the record
; is the one it carries, the epoch and next operation id are the state's) and
; the evidence (the final name observed absent) in the conclusion; an
; operation is issued exactly under them and a framable record, and then it
; carries the epoch, the id, the record, the stored name, the frame and an
; initial authorized publication; otherwise one of the two faults.  It
; subsumes the one-sided echo theorem above.
(defthm fn-bpnf-delete-publication-authorize-admits-exactly-the-issued-pending-deletion
  (let ((answer (fn-bpnf-delete-publication-authorize st epoch op record lock-owned final-absent))
        (issued (fn-bpnf-issued st)))
    (and (iff (fn-bpnf-delete-publication-operationp answer)
              (and (fn-bpnf-operationp issued)
                   (fn-bpnf-operation-matchp issued epoch op)
                   (equal (fn-bpn-nth 3 issued) :delete)
                   (equal (fn-bpn-nth 0 (fn-bpn-nth 4 issued)) record)
                   (equal (fn-bpn-nth 5 issued) :pending)
                   (equal (fn-bpnf-epoch st) epoch)
                   (equal (fn-bpnf-next-op st) (1+ op))
                   (fn-bpn-report-delete-recordp record)
                   (equal (fn-bpn-nth 1 record) epoch)
                   (equal (fn-bpn-nth 2 record) op)
                   lock-owned final-absent
                   (not (equal (fn-bpnf-delete-frame record) :bad))))
         (implies (fn-bpnf-delete-publication-operationp answer)
                  (and (equal (nth 1 answer) epoch)
                       (equal (nth 2 answer) op)
                       (equal (nth 3 answer) record)
                       (equal (fn-bpnf-delete-publication-name answer)
                              (fn-bpnf-stored-record-name epoch op))
                       (equal (fn-bpnf-delete-publication-frame answer) (fn-bpnf-delete-frame record))
                       (equal (nth 6 answer) (fn-jpub-initial t))))
         (implies (not (fn-bpnf-delete-publication-operationp answer))
                  (or (equal answer '(:fault :delete-authority))
                      (equal answer '(:fault :delete-codec))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpn-report-delete-record-epoch-and-op-are-frame-nats))
           :in-theory (e/d (fn-bpnf-delete-publication-authorize fn-bpnf-delete-publication-operationp fn-bpnf-delete-publication-name fn-bpnf-delete-publication-frame)
                           (fn-bpnf-operationp fn-bpnf-operation-matchp
                            fn-bpn-report-delete-recordp fn-bpnf-delete-frame fn-bpnf-stored-record-name
                            fn-bpnf-issued fn-bpnf-epoch fn-bpnf-next-op
                            fn-jpub-initial fn-frame-natp)))))
