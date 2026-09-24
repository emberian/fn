; Exact durable received-carrier dispatch update.  The one held list is
; shared by live publication and ordered FNBS replay.
(in-package "ACL2")
(include-book "bp-node-fragment-replacement")
(include-book "bp-fnbs-dispatch-codec")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-dispatched-held (h peer)
  (declare (xargs :guard t))
  (if (true-listp h)
      (update-nth 12 '(:forward-pending)
                  (update-nth 11 peer
                              (update-nth 10 '(:dispatched :forward) h)))
    h))

(defun fn-bpnp-dispatch-matches-heldp (record h)
  (declare (xargs :guard t))
  (and (fn-bpnp-dispatch-recordp record)
       (equal (fn-bpn-nth 0 h) :bpnf-held)
       (equal (fn-bpn-nth 3 record) (fn-bpn-nth 3 h))
       (equal (fn-bpn-nth 4 record)
              (fn-bpah-held-primary-identity h))
       (null (fn-bpn-nth 10 h))
       (equal (fn-bpn-nth 12 h) '(:dispatch-pending))
       (null (fn-bpn-nth 13 h))
       (null (fn-bpn-nth 14 h))))

(defun fn-bpnp-replace-dispatched (arrival peer held)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) nil
    (if (equal arrival (fn-bpn-nth 3 (car held)))
        (cons (fn-bpnp-dispatched-held (car held) peer) (cdr held))
      (cons (car held)
            (fn-bpnp-replace-dispatched arrival peer (cdr held))))))

(defun fn-bpnp-dispatch-apply (record held)
  (declare (xargs :guard t))
  (let* ((arrival (fn-bpn-nth 3 record))
         (h (fn-bpnf-find-arrival arrival held)))
    (if (and (equal (fn-bpnf-arrival-count arrival held) 1)
             (fn-bpnp-dispatch-matches-heldp record h))
        (list :ready
              (fn-bpnp-replace-dispatched
               arrival (fn-bpn-nth 5 record) held)
              (fn-bpnp-dispatched-held h (fn-bpn-nth 5 record)))
      (list :fault :dispatch-row))))
