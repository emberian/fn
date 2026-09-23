; Authorize one immutable kind-5 FNBS publication from the exact pending
; fn-bpnf-step effect.  The host supplies only lock/name observations;
; ACL2 owns record, final name, frame bytes, and fn-jpub authority.
(in-package "ACL2")
(include-book "bp-fnbs-byte-publisher")

(set-verify-guards-eagerness 0)

(defun fn-bpnf-publication-authorize
  (st epoch operation-id held lock-owned final-absent)
  (declare (xargs :guard t))
  (let* ((issued (fn-bpnf-issued st))
         (record (fn-bpnf-stored-record epoch operation-id held)))
    (if (and (fn-bpnf-operationp issued)
             (fn-bpnf-operation-matchp issued epoch operation-id)
             (equal (fn-bpn-nth 3 issued) :store)
             (equal (fn-bpn-nth 4 issued) held)
             (equal (fn-bpn-nth 5 issued) :pending)
             (equal (fn-bpnf-epoch st) epoch)
             (equal (fn-bpnf-next-op st) (1+ operation-id))
             (fn-bpnf-stored-recordp record)
             lock-owned final-absent)
        (let ((frame (fn-bpnf-stored-record-frame record)))
          (if (equal frame :bad)
              (list :fault :fnbs-publication-codec)
            (list :ok epoch operation-id held
                  (fn-bpnf-stored-record-name epoch operation-id)
                  frame (fn-jpub-initial t))))
      (list :fault :fnbs-publication-authority))))

(defun fn-bpnf-publication-operationp (operation)
  (declare (xargs :guard t))
  (and (true-listp operation) (equal (len operation) 7)
       (equal (car operation) :ok)
       (fn-frame-natp (nth 1 operation))
       (fn-frame-natp (nth 2 operation))
       (fn-bpnf-stored-recordp
        (fn-bpnf-stored-record (nth 1 operation) (nth 2 operation)
                                (nth 3 operation)))
       (equal (nth 4 operation)
              (fn-bpnf-stored-record-name
               (nth 1 operation) (nth 2 operation)))
       (equal (nth 5 operation)
              (fn-bpnf-stored-record-frame
               (fn-bpnf-stored-record (nth 1 operation) (nth 2 operation)
                                        (nth 3 operation))))
       (not (equal (nth 5 operation) :bad))
       (equal (nth 6 operation) (fn-jpub-initial t))))

(defun fn-bpnf-publication-operation-name (operation)
  (declare (xargs :guard t)) (nth 4 operation))
(defun fn-bpnf-publication-operation-frame (operation)
  (declare (xargs :guard t)) (nth 5 operation))
(defun fn-bpnf-publication-operation-publisher (operation)
  (declare (xargs :guard t)) (nth 6 operation))
