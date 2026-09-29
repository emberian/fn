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

(defun fn-bpn-report-outbox-next-aux (held-list after selected)
  (declare (xargs :guard t :measure (acl2-count held-list)))
  (if (atom held-list)
      selected
    (let* ((h (car held-list))
           (view (and (or (null after)
                          (and (natp after) (< after (fn-bpn-nth 3 h))))
                      (fn-bpn-report-outbox-view h))))
      (fn-bpn-report-outbox-next-aux
       (cdr held-list) after
       (if (and view
                (or (null selected)
                    (< (fn-bpn-nth 1 view) (fn-bpn-nth 1 selected))))
           view selected)))))

(defun fn-bpn-report-outbox-next (st after)
  (declare (xargs :guard t))
  (fn-bpn-report-outbox-next-aux (fn-bpnf-held-list st) after nil))

(defun fn-bpn-report-outbox-peer-matchp (view peer)
  (declare (xargs :guard t))
  (and (equal (fn-bpn-nth 0 view) :report-outbox)
       (fn-bpp-eidp peer)
       (equal (fn-bpn-nth 2 view) peer)))

(defthm fn-bpn-report-outbox-view-requires-tombstone
  (implies (fn-bpn-report-outbox-view held)
           (fn-bpn-report-deleted-record-matches-heldp
            (fn-bpn-nth 14 held) held))
  :hints (("Goal" :in-theory (disable fn-bpn-report-deleted-record-matches-heldp
                                      fn-bpn-report-decode)))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; KEYSTONE for fn-bpn-report-outbox-next (PRF-1048), the selection
; host/native/bp-node.lisp's report drive makes: the next outbox view after
; the arrival it last consumed.  A held row YIELDS when its arrival is after
; AFTER (nil: every arrival) and the row has an outbox view (a tombstoned
; report with a decodable payload); the selector answers nil exactly when no
; held row yields, else the view of a yielding row whose arrival is at most
; every yielding row's, under the comparison the scan itself makes.
(defun fn-bpn-report-outbox-yieldsp (held after)
  (declare (xargs :guard t))
  (and (or (null after)
           (and (natp after) (< after (fn-bpn-nth 3 held))))
       (fn-bpn-report-outbox-view held)
       t))

(defun fn-bpn-report-outbox-any-yields (held-list after)
  (declare (xargs :guard t))
  (if (atom held-list)
      nil
    (or (fn-bpn-report-outbox-yieldsp (car held-list) after)
        (fn-bpn-report-outbox-any-yields (cdr held-list) after))))

(defun fn-bpn-report-outbox-view-of-a-yielding-row (view held-list after)
  (declare (xargs :guard t))
  (if (atom held-list)
      nil
    (or (and (fn-bpn-report-outbox-yieldsp (car held-list) after)
             (equal view (fn-bpn-report-outbox-view (car held-list))))
        (fn-bpn-report-outbox-view-of-a-yielding-row view (cdr held-list) after))))

(defun fn-bpn-report-outbox-arrival-at-most-every-yield (arrival held-list after)
  (declare (xargs :guard t))
  (if (atom held-list)
      t
    (and (or (not (fn-bpn-report-outbox-yieldsp (car held-list) after))
             (not (< (fn-bpn-nth 1 (fn-bpn-report-outbox-view (car held-list)))
                     arrival)))
         (fn-bpn-report-outbox-arrival-at-most-every-yield
          arrival (cdr held-list) after))))

(defthm fn-bpn-report-outbox-next-aux-selects-the-least-yield
  (let ((r (fn-bpn-report-outbox-next-aux held-list after selected)))
    (and (iff r (or selected (fn-bpn-report-outbox-any-yields held-list after)))
         (implies r
                  (and (or (equal r selected)
                           (fn-bpn-report-outbox-view-of-a-yielding-row
                            r held-list after))
                       (fn-bpn-report-outbox-arrival-at-most-every-yield
                        (fn-bpn-nth 1 r) held-list after)
                       (implies selected
                                (not (< (fn-bpn-nth 1 selected) (fn-bpn-nth 1 r))))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bpn-report-outbox-next-aux held-list after selected)
           :in-theory (e/d (fn-bpn-report-outbox-next-aux)
                           (fn-bpn-report-outbox-view fn-bpn-nth)))))

(defthm fn-bpn-report-outbox-next-selects-exactly-the-least-yielding-row
  (let ((r (fn-bpn-report-outbox-next st after))
        (rows (fn-bpnf-held-list st)))
    (and (iff r (fn-bpn-report-outbox-any-yields rows after))
         (implies r
                  (and (fn-bpn-report-outbox-view-of-a-yielding-row r rows after)
                       (fn-bpn-report-outbox-arrival-at-most-every-yield
                        (fn-bpn-nth 1 r) rows after)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-report-outbox-next-aux-selects-the-least-yield
                            (held-list (fn-bpnf-held-list st)) (selected nil)))
           :in-theory (e/d (fn-bpn-report-outbox-next)
                           (fn-bpn-report-outbox-next-aux
                            fn-bpn-report-outbox-any-yields
                            fn-bpn-report-outbox-view-of-a-yielding-row
                            fn-bpn-report-outbox-arrival-at-most-every-yield
                            fn-bpn-report-outbox-view fn-bpn-nth
                            fn-bpnf-held-list)))))
