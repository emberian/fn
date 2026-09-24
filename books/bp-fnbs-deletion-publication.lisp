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
