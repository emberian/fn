; ACL2 authorization for the exact pending kind-14 conflict record image
; (spec bp-node-machine 3.3 and 4.1 step 4, N11).  The host publishes only
; what this returns: the stored-record name of the issued (epoch, op), the
; codec's frame of the issued record, and a fresh immutable publisher.
(in-package "ACL2")
(include-book "bp-node-foundation")
(include-book "bp-fnbs-conflict-codec")
(include-book "bp-fnbs-byte-publisher")
(set-verify-guards-eagerness 0)

; The issued :conflict operation: an fn-bpnf-operationp of kind :conflict
; whose detail is the (record ingress) pair fn-bpnp-conflict-propose-step
; issues.
(defun fn-bpnf-conflict-operation-shapep (issued)
  (declare (xargs :guard t))
  (and (fn-bpnf-operationp issued)
       (equal (fn-bpn-nth 3 issued) :conflict)
       (true-listp (fn-bpn-nth 4 issued))
       (equal (len (fn-bpn-nth 4 issued)) 2)))

(defun fn-bpnf-conflict-publication-authorize
  (st epoch op record lock-owned final-absent)
  (declare (xargs :guard t))
  (let* ((issued (fn-bpnf-issued st))
         (detail (fn-bpn-nth 4 issued)))
    (if (and (fn-bpnf-conflict-operation-shapep issued)
             (fn-bpnf-operation-matchp issued epoch op)
             (equal (fn-bpn-nth 3 issued) :conflict)
             (equal (fn-bpn-nth 0 detail) record)
             (equal (fn-bpn-nth 5 issued) :pending)
             (equal (fn-bpnf-epoch st) epoch)
             (equal (fn-bpnf-next-op st) (1+ op))
             (fn-bpnf-conflict-recordp record)
             (equal (fn-bpn-nth 1 record) epoch)
             (equal (fn-bpn-nth 2 record) op)
             lock-owned final-absent)
        (let ((frame (fn-bpnf-conflict-frame record)))
          (if (equal frame :bad)
              (list :fault :conflict-codec)
            (list :ok epoch op record
                  (fn-bpnf-stored-record-name epoch op)
                  frame (fn-jpub-initial t))))
      (list :fault :conflict-authority))))

(defun fn-bpnf-conflict-publication-operationp (operation)
  (declare (xargs :guard t))
  (and (true-listp operation) (equal (len operation) 7)
       (equal (car operation) :ok)
       (fn-frame-natp (nth 1 operation))
       (fn-frame-natp (nth 2 operation))
       (fn-bpnf-conflict-recordp (nth 3 operation))
       (equal (nth 4 operation)
              (fn-bpnf-stored-record-name (nth 1 operation)
                                          (nth 2 operation)))
       (equal (nth 5 operation)
              (fn-bpnf-conflict-frame (nth 3 operation)))
       (not (equal (nth 5 operation) :bad))
       (equal (nth 6 operation) (fn-jpub-initial t))))

(defun fn-bpnf-conflict-publication-name (operation)
  (declare (xargs :guard t)) (nth 4 operation))
(defun fn-bpnf-conflict-publication-frame (operation)
  (declare (xargs :guard t)) (nth 5 operation))
(defun fn-bpnf-conflict-publication-publisher (operation)
  (declare (xargs :guard t)) (nth 6 operation))

; KEYSTONE.  An authorized kind-14 publication is exactly the machine's
; pending :conflict operation (an fn-bpnf-operationp) at (epoch, op), with the next operation id
; already advanced past it, under the held lock and an absent final name;
; it publishes the codec's frame of that very record at the stored-record
; name of (epoch, op).
(defthm fn-bpnf-conflict-publication-success-binds-exact-echo
  (let ((operation (fn-bpnf-conflict-publication-authorize
                    st epoch op record lock-owned final-absent)))
    (implies (equal (car operation) :ok)
             (and (fn-bpnf-operationp (fn-bpnf-issued st))
                  (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :conflict)
                  (equal (fn-bpn-nth 0 (fn-bpn-nth 4 (fn-bpnf-issued st)))
                         record)
                  (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                  (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                  (equal (fn-bpnf-epoch st) epoch)
                  (equal (fn-bpnf-next-op st) (1+ op))
                  lock-owned final-absent
                  (equal (fn-bpnf-conflict-publication-name operation)
                         (fn-bpnf-stored-record-name epoch op))
                  (equal (fn-bpnf-conflict-publication-frame operation)
                         (fn-bpnf-conflict-frame record))
                  (not (equal (fn-bpnf-conflict-publication-frame operation)
                              :bad)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnf-conflict-publication-authorize
                            fn-bpnf-conflict-publication-name
                            fn-bpnf-conflict-publication-frame)
                           (fn-bpnf-operationp
                            fn-bpnf-operation-matchp
                            fn-bpnf-conflict-recordp
                            fn-bpnf-conflict-frame
                            fn-bpnf-stored-record-name
                            fn-jpub-initial))))
  :rule-classes nil)
