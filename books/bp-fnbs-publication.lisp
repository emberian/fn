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

; This is the authorization subject called by the native publisher.  In
; particular a successful result cannot be manufactured from a stale
; callback or a different held row, even when the final name is free.
(defthm fn-bpnf-publication-success-binds-pending-echo
  (implies (equal (car (fn-bpnf-publication-authorize
                       st epoch operation-id held lock-owned final-absent))
                  :ok)
           (and (fn-bpnf-operationp (fn-bpnf-issued st))
                (fn-bpnf-operation-matchp (fn-bpnf-issued st)
                                           epoch operation-id)
                (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :store)
                (equal (fn-bpn-nth 4 (fn-bpnf-issued st)) held)
                (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                (equal (fn-bpnf-epoch st) epoch)
                (equal (fn-bpnf-next-op st) (1+ operation-id))
                lock-owned final-absent
                (equal (fn-bpnf-publication-operation-name
                        (fn-bpnf-publication-authorize
                         st epoch operation-id held lock-owned final-absent))
                       (fn-bpnf-stored-record-name epoch operation-id))
                (equal (fn-bpnf-publication-operation-frame
                        (fn-bpnf-publication-authorize
                         st epoch operation-id held lock-owned final-absent))
                       (fn-bpnf-stored-record-frame
                        (fn-bpnf-stored-record epoch operation-id held)))
                (equal (fn-bpnf-publication-operation-publisher
                        (fn-bpnf-publication-authorize
                         st epoch operation-id held lock-owned final-absent))
                       (fn-jpub-initial t))))
  :hints (("Goal" :in-theory (enable fn-bpnf-publication-authorize
                                     fn-bpnf-publication-operation-name
                                     fn-bpnf-publication-operation-frame
                                     fn-bpnf-publication-operation-publisher))))

(defthm fn-bpnf-publication-authorize-yields-operation
  (implies (equal (car (fn-bpnf-publication-authorize
                       st epoch operation-id held lock-owned final-absent))
                  :ok)
           (fn-bpnf-publication-operationp
            (fn-bpnf-publication-authorize
             st epoch operation-id held lock-owned final-absent)))
  :hints (("Goal" :in-theory (enable fn-bpnf-publication-authorize
                                     fn-bpnf-publication-operationp))))
