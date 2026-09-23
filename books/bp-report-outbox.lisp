; Recoverable status-report intent from the same immutable kind-10 tombstone.
; This is a carrier obligation only; it cannot release any local application pin.
(in-package "ACL2")
(include-book "bp-node-report-step")
(set-verify-guards-eagerness 0)

(defun fn-bpn-report-outbox-work (record)
  (declare (xargs :guard t))
  (fn-bpn-append
   (fn-record-string-octets "bp-status:")
   (fn-bpn-append
    (fn-record-string-octets (fn-prov-nat-string (fn-bpn-nth 1 record)))
    (cons 58
          (fn-record-string-octets
           (fn-prov-nat-string (fn-bpn-nth 2 record)))))))

(defun fn-bpn-report-outbox-view (held)
  (declare (xargs :guard t))
  (let* ((record (fn-bpn-nth 14 held))
         (payload (fn-bpn-nth 6 record)))
    (if (and (fn-bpn-report-deleted-record-matches-heldp record held)
             (not (equal payload '(0)))
             (fn-cbor-result-okp (fn-bpn-report-decode payload)))
        (list :report-outbox (fn-bpn-nth 3 held)
              (fn-bpp-report-to
               (fn-bpb-bundle-primary (fn-bpnf-held-bundle held)))
              payload (fn-bpn-report-outbox-work record)
              (fn-record-string-octets "status") 0)
      nil)))

(defun fn-bpn-report-outbox-next-aux (held-list after)
  (declare (xargs :guard t :measure (acl2-count held-list)))
  (if (atom held-list)
      nil
    (let ((h (car held-list)))
      (if (and (or (null after)
                   (and (natp after) (< after (fn-bpn-nth 3 h))))
               (fn-bpn-report-outbox-view h))
          (fn-bpn-report-outbox-view h)
        (fn-bpn-report-outbox-next-aux (cdr held-list) after)))))

(defun fn-bpn-report-outbox-next (st after)
  (declare (xargs :guard t))
  (fn-bpn-report-outbox-next-aux (fn-bpnf-held-list st) after))

(defthm fn-bpn-report-outbox-view-requires-tombstone
  (implies (fn-bpn-report-outbox-view held)
           (fn-bpn-report-deleted-record-matches-heldp
            (fn-bpn-nth 14 held) held))
  :hints (("Goal" :in-theory (disable fn-bpn-report-deleted-record-matches-heldp
                                      fn-bpn-report-decode)))
  :rule-classes nil)
