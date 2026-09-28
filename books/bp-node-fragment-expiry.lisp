; A fragment family is eligible only when every selected source row is live
; at one ACL2 clock observation.  The active set is not filtered by time:
; doing so could hide a conflicting fragment or silently consume a partial
; family.  Expired rows are handled by the durable deletion transition.
(in-package "ACL2")
(include-book "bp-node-fragment-plan")
(include-book "bp-app-handoff-time")

(defun fn-bpnf-family-rows-livep (rows observation)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (and (equal (fn-bpah-held-expiry (car rows) observation) :live)
           (fn-bpnf-family-rows-livep (cdr rows) observation))
    (null rows)))

(defun fn-bpnf-family-plan-at (st anchor observation)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (let ((rows (fn-bpnf-active-set st anchor)))
    (if (and (fn-clock-observationp observation)
             (consp rows)
             (fn-bpnf-family-rows-livep rows observation))
        (fn-bpnf-family-plan st anchor)
      (list :blocked :expiry))))

(defthm fn-bpnf-family-plan-at-ready-binds-live-source-rows
  (implies (equal (car (fn-bpnf-family-plan-at st anchor observation))
                  :ready)
           (fn-bpnf-family-rows-livep
            (fn-bpnf-active-set st anchor) observation))
  :hints (("Goal" :in-theory (disable fn-bpnf-active-set
                                      fn-bpnf-family-plan)))
  :rule-classes nil)
