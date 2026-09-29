; ACL2 authority for the exact pending version-2/kind-6 dispatch frame.
(in-package "ACL2")
(include-book "bp-node-progress")
(include-book "bp-fnbs-byte-publisher")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-dispatch-publication-authorize
  (st epoch op record lock-owned final-absent)
  ;; The *1* class (Q4a item 2): host-called; the guard names the kinds the
  ;; host passes (the entry guard checks them by name) and the wrapper runs raw.
  (declare (xargs :guard (and (fn-frame-natp epoch) (fn-frame-natp op))
                  :verify-guards nil))
  (let ((issued (fn-bpnf-issued st)))
    (if (and (fn-bpnf-operationp issued)
             (fn-bpnf-operation-matchp issued epoch op)
             (equal (fn-bpn-nth 3 issued) :dispatch)
             (equal (fn-bpn-nth 4 issued) record)
             (equal (fn-bpn-nth 5 issued) :pending)
             (equal (fn-bpnf-epoch st) epoch)
             (equal (fn-bpnf-next-op st) (1+ op))
             (fn-bpnp-dispatch-recordp record)
             (equal (fn-bpn-nth 1 record) epoch)
             (equal (fn-bpn-nth 2 record) op)
             lock-owned final-absent)
        (let ((frame (fn-bpnp-dispatch-frame record)))
          (if (equal frame :bad)
              (list :fault :dispatch-codec)
            (list :ok epoch op record
                  (fn-bpnf-stored-record-name epoch op)
                  frame (fn-jpub-initial t))))
      (list :fault :dispatch-authority))))

(defun fn-bpnp-dispatch-publication-operationp (operation)
  (declare (xargs :guard t))
  (and (true-listp operation) (equal (len operation) 7)
       (equal (car operation) :ok)
       (fn-frame-natp (nth 1 operation))
       (fn-frame-natp (nth 2 operation))
       (fn-bpnp-dispatch-recordp (nth 3 operation))
       (equal (nth 4 operation)
              (fn-bpnf-stored-record-name (nth 1 operation)
                                          (nth 2 operation)))
       (equal (nth 5 operation)
              (fn-bpnp-dispatch-frame (nth 3 operation)))
       (not (equal (nth 5 operation) :bad))
       (equal (nth 6 operation) (fn-jpub-initial t))))

(defun fn-bpnp-dispatch-publication-name (operation)
  (declare (xargs :guard (true-listp operation))) (nth 4 operation))
(defun fn-bpnp-dispatch-publication-frame (operation)
  (declare (xargs :guard (true-listp operation))) (nth 5 operation))
(defun fn-bpnp-dispatch-publication-publisher (operation)
  (declare (xargs :guard (true-listp operation))) (nth 6 operation))

(verify-guards fn-bpnp-dispatch-publication-authorize)
(verify-guards fn-bpnp-dispatch-publication-operationp)
(verify-guards fn-bpnp-dispatch-publication-name)
(verify-guards fn-bpnp-dispatch-publication-frame)
(verify-guards fn-bpnp-dispatch-publication-publisher)


; A stored dispatch record's epoch and operation id are frame naturals (the
; record recognizer says so); stated once so the keystone keeps the
; recognizer closed.
(defthm fn-bpnp-dispatch-record-epoch-and-op-are-frame-nats
  (implies (fn-bpnp-dispatch-recordp record)
           (and (fn-frame-natp (fn-bpn-nth 1 record))
                (fn-frame-natp (fn-bpn-nth 2 record))))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-dispatch-recordp)
                                  (fn-frame-natp)))))

; KEYSTONE (PRF-1016).  The dispatch publication authorization, two-sided:
; the principal (the caller holds the publication lock), the policy context
; (the issued operation is the pending :dispatch of this epoch and operation
; id, the record is the one it carries, the epoch and next operation id are
; the state's) and the evidence (the final name observed absent) in the
; conclusion; an operation is issued exactly under them and a framable
; record, and then it carries the epoch, the id, the record, the stored name,
; the frame and an initial authorized publication; otherwise one of the two
; faults.  The host (host/native/bp-service.lisp fnn-bps-persist-dispatch)
; treats the codec fault as :refused and any other non-operation answer as
; indeterminate; this theorem says those are the only answers.
(defthm fn-bpnp-dispatch-publication-authorize-admits-exactly-the-issued-pending-dispatch
  (let ((answer (fn-bpnp-dispatch-publication-authorize st epoch op record lock-owned final-absent))
        (issued (fn-bpnf-issued st)))
    (and (iff (fn-bpnp-dispatch-publication-operationp answer)
              (and (fn-bpnf-operationp issued)
                   (fn-bpnf-operation-matchp issued epoch op)
                   (equal (fn-bpn-nth 3 issued) :dispatch)
                   (equal (fn-bpn-nth 4 issued) record)
                   (equal (fn-bpn-nth 5 issued) :pending)
                   (equal (fn-bpnf-epoch st) epoch)
                   (equal (fn-bpnf-next-op st) (1+ op))
                   (fn-bpnp-dispatch-recordp record)
                   (equal (fn-bpn-nth 1 record) epoch)
                   (equal (fn-bpn-nth 2 record) op)
                   lock-owned final-absent
                   (not (equal (fn-bpnp-dispatch-frame record) :bad))))
         (implies (fn-bpnp-dispatch-publication-operationp answer)
                  (and (equal (nth 1 answer) epoch)
                       (equal (nth 2 answer) op)
                       (equal (nth 3 answer) record)
                       (equal (fn-bpnp-dispatch-publication-name answer)
                              (fn-bpnf-stored-record-name epoch op))
                       (equal (fn-bpnp-dispatch-publication-frame answer)
                              (fn-bpnp-dispatch-frame record))
                       (equal (fn-bpnp-dispatch-publication-publisher answer)
                              (fn-jpub-initial t))))
         (implies (not (fn-bpnp-dispatch-publication-operationp answer))
                  (or (equal answer '(:fault :dispatch-authority))
                      (equal answer '(:fault :dispatch-codec))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpnp-dispatch-record-epoch-and-op-are-frame-nats))
           :in-theory (e/d (fn-bpnp-dispatch-publication-authorize
                            fn-bpnp-dispatch-publication-operationp
                            fn-bpnp-dispatch-publication-name
                            fn-bpnp-dispatch-publication-frame
                            fn-bpnp-dispatch-publication-publisher)
                           (fn-bpnf-operationp fn-bpnf-operation-matchp
                            fn-bpnp-dispatch-recordp fn-bpnp-dispatch-frame
                            fn-bpnf-stored-record-name
                            fn-bpnf-issued fn-bpnf-epoch fn-bpnf-next-op
                            fn-jpub-initial fn-frame-natp)))))
