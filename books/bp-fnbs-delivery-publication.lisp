; ACL2 authority for a kind-7 FNBS result.  The host may publish only the
; exact pending application result with the state-owned epoch/operation id.
(in-package "ACL2")
(include-book "bp-fnbs-delivery-codec")
(include-book "bp-fnbs-byte-publisher")
(set-verify-guards-eagerness 0)

(defun fn-bpah-publication-authorize
  (st epoch operation-id record lock-owned final-absent)
  (declare (xargs :guard t))
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
  (declare (xargs :guard t)) (nth 4 operation))
(defun fn-bpah-publication-frame (operation)
  (declare (xargs :guard t)) (nth 5 operation))
(defun fn-bpah-publication-publisher (operation)
  (declare (xargs :guard t)) (nth 6 operation))

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
