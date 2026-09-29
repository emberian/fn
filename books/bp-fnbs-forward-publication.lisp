; Exact pending kind-8/9/20 FNBS publication authority.  The host only writes
; the ACL2-selected frame and reports the three-valued persistence result.
(in-package "ACL2")
(include-book "bp-node-progress")
(include-book "bp-fnbs-byte-publisher")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-forward-publication-frame (kind record)
  (declare (xargs :guard t))
  (cond ((equal kind :attempt) (fn-bpnp-attempt-frame record))
        ((equal kind :forward-result) (fn-bpnp-result-frame record))
        ((equal kind :deferral) (fn-bpnp-deferral-frame record))
        (t :bad)))

(defun fn-bpnp-forward-publication-authorize
  (st epoch op record lock-owned final-absent)
  (declare (xargs :guard t))
  (let* ((issued (fn-bpnf-issued st))
         (kind (fn-bpn-nth 3 issued)))
    (if (and (fn-bpnf-operationp issued)
             (fn-bpnf-operation-matchp issued epoch op)
             (member-equal kind '(:attempt :forward-result :deferral))
             (equal (fn-bpn-nth 4 issued) record)
             (equal (fn-bpn-nth 5 issued) :pending)
             (equal (fn-bpnf-epoch st) epoch)
             (equal (fn-bpnf-next-op st) (1+ op))
             (equal (fn-bpn-nth 1 record) epoch)
             (equal (fn-bpn-nth 2 record) op)
             lock-owned final-absent)
        (let ((frame (fn-bpnp-forward-publication-frame kind record)))
          (if (equal frame :bad)
              (list :fault :forward-codec)
            (list :ok epoch op record
                  (fn-bpnf-stored-record-name epoch op)
                  frame (fn-jpub-initial t))))
      (list :fault :forward-authority))))

(defun fn-bpnp-forward-publication-operationp (operation)
  (declare (xargs :guard t))
  (and (true-listp operation) (equal (len operation) 7)
       (equal (car operation) :ok)
       (fn-frame-natp (fn-bpn-nth 1 operation))
       (fn-frame-natp (fn-bpn-nth 2 operation))
       (equal (fn-bpn-nth 4 operation)
              (fn-bpnf-stored-record-name
               (fn-bpn-nth 1 operation) (fn-bpn-nth 2 operation)))
       (or (equal (fn-bpn-nth 5 operation)
                  (fn-bpnp-attempt-frame (fn-bpn-nth 3 operation)))
           (equal (fn-bpn-nth 5 operation)
                  (fn-bpnp-result-frame (fn-bpn-nth 3 operation)))
           (equal (fn-bpn-nth 5 operation)
                  (fn-bpnp-deferral-frame (fn-bpn-nth 3 operation))))
       (not (equal (fn-bpn-nth 5 operation) :bad))
       (equal (fn-bpn-nth 6 operation) (fn-jpub-initial t))))

(defun fn-bpnp-forward-publication-name (operation)
  (declare (xargs :guard t)) (fn-bpn-nth 4 operation))
(defun fn-bpnp-forward-publication-octets (operation)
  (declare (xargs :guard t)) (fn-bpn-nth 5 operation))
(defun fn-bpnp-forward-publication-publisher (operation)
  (declare (xargs :guard t)) (fn-bpn-nth 6 operation))

; fn-bpn-nth on a cons (the operation is built by list; the recognizer reads
; it with fn-bpn-nth).
(local
 (defthm fn-bpnp-forward-publication-nth-of-cons
   (equal (fn-bpn-nth n (cons a b))
          (if (or (not (natp n)) (zp n)) a (fn-bpn-nth (1- n) b)))
   :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car)))))

; Each kind's frame is :bad unless that kind's record recognizer holds, and
; every one of the three recognizers carries the record's epoch and operation
; id as frame naturals: a framable record's epoch and id are frame naturals
; whatever its kind.  This closes, inside the function, the gap between
; fn-bpnf-operationp (natp epoch and op) and the operation recognizer
; (fn-frame-natp): the authorization's :ok branch requires a frame other than
; :bad and the record's epoch and id to be the offered ones.
(defthm fn-bpnp-forward-publication-frame-not-bad-implies-frame-nats
  (implies (not (equal (fn-bpnp-forward-publication-frame kind record) :bad))
           (and (fn-frame-natp (fn-bpn-nth 1 record))
                (fn-frame-natp (fn-bpn-nth 2 record))))
  :hints (("Goal" :in-theory (e/d (fn-bpnp-forward-publication-frame
                                   fn-bpnp-attempt-frame
                                   fn-bpnp-result-frame
                                   fn-bpnp-deferral-frame
                                   fn-bpnp-forward-attempt-recordp
                                   fn-bpnp-forward-result-recordp
                                   fn-bpnp-deferral-recordp)
                                  (fn-frame-natp fn-bpnp-forward-frame-with
                                   fn-bpnp-attempt-values fn-bpnp-result-values
                                   fn-bpnp-deferral-values
                                   fn-cbor-octet-listp fn-bpp-eidp
                                   fn-bpnp-session-idp fn-bpnp-forward-outcomep)))))

; KEYSTONE (PRF-1017).  The forward publication authorization (kinds 8, 9
; and 20: attempt, forward result, deferral), two-sided: the principal (the
; caller holds the publication lock), the policy context (the issued
; operation is a pending one of the three kinds for this epoch and operation
; id, the record is the one it carries, the epoch and next operation id are
; the state's) and the evidence (the final name observed absent) in the
; conclusion; an operation is issued exactly under them and a record the
; issued kind frames, and then it carries the epoch, the id, the record, the
; stored name, that frame and an initial authorized publication; otherwise
; one of the two faults.  The recognizer fn-bpnp-forward-publication-operationp
; is the same host entry's second call (fnn-bps-persist-forward) and is the
; left side of the iff.
(defthm fn-bpnp-forward-publication-authorize-admits-exactly-the-issued-pending-forward
  (let ((answer (fn-bpnp-forward-publication-authorize st epoch op record lock-owned final-absent))
        (issued (fn-bpnf-issued st)))
    (and (iff (fn-bpnp-forward-publication-operationp answer)
              (and (fn-bpnf-operationp issued)
                   (fn-bpnf-operation-matchp issued epoch op)
                   (member-equal (fn-bpn-nth 3 issued)
                                 '(:attempt :forward-result :deferral))
                   (equal (fn-bpn-nth 4 issued) record)
                   (equal (fn-bpn-nth 5 issued) :pending)
                   (equal (fn-bpnf-epoch st) epoch)
                   (equal (fn-bpnf-next-op st) (1+ op))
                   (equal (fn-bpn-nth 1 record) epoch)
                   (equal (fn-bpn-nth 2 record) op)
                   lock-owned final-absent
                   (not (equal (fn-bpnp-forward-publication-frame
                                (fn-bpn-nth 3 issued) record)
                               :bad))))
         (implies (fn-bpnp-forward-publication-operationp answer)
                  (and (equal (fn-bpn-nth 1 answer) epoch)
                       (equal (fn-bpn-nth 2 answer) op)
                       (equal (fn-bpn-nth 3 answer) record)
                       (equal (fn-bpnp-forward-publication-name answer)
                              (fn-bpnf-stored-record-name epoch op))
                       (equal (fn-bpnp-forward-publication-octets answer)
                              (fn-bpnp-forward-publication-frame
                               (fn-bpn-nth 3 issued) record))
                       (equal (fn-bpnp-forward-publication-publisher answer)
                              (fn-jpub-initial t))))
         (implies (not (fn-bpnp-forward-publication-operationp answer))
                  (or (equal answer '(:fault :forward-authority))
                      (equal answer '(:fault :forward-codec))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bpnp-forward-publication-frame-not-bad-implies-frame-nats
                                   (kind (fn-bpn-nth 3 (fn-bpnf-issued st)))))
           :in-theory (e/d (fn-bpnp-forward-publication-authorize
                            fn-bpnp-forward-publication-operationp
                            fn-bpnp-forward-publication-name
                            fn-bpnp-forward-publication-octets
                            fn-bpnp-forward-publication-publisher
                            fn-bpnp-forward-publication-frame)
                           (fn-bpnf-operationp fn-bpnf-operation-matchp
                            fn-bpnp-attempt-frame fn-bpnp-result-frame
                            fn-bpnp-deferral-frame fn-bpn-nth
                            fn-bpnf-stored-record-name
                            fn-bpnf-issued fn-bpnf-epoch fn-bpnf-next-op
                            fn-jpub-initial fn-frame-natp)))))
