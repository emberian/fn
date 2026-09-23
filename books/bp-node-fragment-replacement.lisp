; Pure kind-18 application against the one held list. Live completion and
; ordered replay will call this same rule after validating the protected row.
(in-package "ACL2")
(include-book "bp-fnbs-family-codec")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-arrival-count (arrival held)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (consp held)
      (+ (if (equal (fn-bpn-nth 3 (car held)) arrival) 1 0)
         (fn-bpnf-arrival-count arrival (cdr held)))
    0))

(defun fn-bpnf-find-arrival (arrival held)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (consp held)
      (if (equal (fn-bpn-nth 3 (car held)) arrival)
          (car held)
        (fn-bpnf-find-arrival arrival (cdr held)))
    nil))

(defun fn-bpnf-family-retain-other-rows (held consumed)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (consp held)
      (if (fn-ag-member (car held) consumed)
          (fn-bpnf-family-retain-other-rows (cdr held) consumed)
        (cons (car held)
              (fn-bpnf-family-retain-other-rows (cdr held) consumed)))
    nil))

(defun fn-bpnf-family-apply (st record expected-arrival)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (let* ((held (fn-bpnf-held-list st))
         (anchor-arrival (fn-bpn-nth 3 record))
         (anchor (fn-bpnf-find-arrival anchor-arrival held)))
    (if (not (and (fn-bpnf-family-recordp record)
                  (fn-frame-natp expected-arrival)
                  (equal (fn-bpn-nth 4 record) expected-arrival)
                  (equal (fn-bpnf-arrival-count anchor-arrival held) 1)
                  (fn-bpnf-active-fragmentp anchor)))
        (list :fault :family-anchor)
      (let ((plan (fn-bpnf-family-plan st anchor)))
        (if (not (and (equal (fn-cbor-ag-car plan) :ready)
                      (equal (fn-bpn-nth 5 record) (fn-bpn-nth 2 plan))
                      (null (fn-bpnf-find-held
                             (fn-bpnf-held-key
                              (fn-bpnf-held-principal (fn-bpn-nth 4 plan))
                              (fn-bpb-bundle-id (fn-bpn-nth 1 plan)))
                             held))))
            (list :fault :family-image)
          (let* ((zero (fn-bpn-nth 4 plan))
                 (consumed (fn-bpnf-active-set st anchor))
                 (whole (fn-bpn-nth 1 plan))
                 (wire (fn-bpn-nth 2 plan))
                 (row (fn-bpnf-held
                       (fn-bpnf-held-principal zero)
                       (fn-bpb-bundle-id whole)
                       expected-arrival
                       (fn-bpn-nth 4 zero)
                       nil (list :reassembled (fn-bpn-nth 3 plan))
                       whole wire (fn-bpn-nth 9 zero)
                       nil nil '(:dispatch-pending) nil nil
                       expected-arrival)))
            (if (not (fn-bpnf-heldp row))
                (list :fault :family-row)
              (list :ready
                    (cons row (fn-bpnf-family-retain-other-rows held consumed))
                    row consumed))))))))

(defthm fn-bpnf-family-apply-ready-has-held-whole
  (implies (equal (car (fn-bpnf-family-apply st record expected-arrival))
                  :ready)
           (and (fn-bpnf-heldp
                 (fn-bpn-nth 2
                  (fn-bpnf-family-apply st record expected-arrival)))
                (equal (fn-bpn-nth 3
                        (fn-bpn-nth 2
                         (fn-bpnf-family-apply st record expected-arrival)))
                       expected-arrival)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnf-family-plan
                               fn-bpnf-active-set
                               fn-bpnf-family-retain-other-rows
                               fn-bpnf-find-held
                               fn-bpnf-family-recordp
                               fn-bpnf-heldp)))
  :rule-classes nil)
