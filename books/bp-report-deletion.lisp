; Durable held deletion kernel for the first D1b status-report slice.
; A carrier expiry is not application release authority.  The kind-10
; tombstone prevents fresh delivery and preserves the received identity.
(in-package "ACL2")
(include-book "bp-app-handoff-time")
(include-book "bp-status-report")
(set-verify-guards-eagerness 0)

(defun fn-bpn-report-delete-record (epoch op arrival identity reason)
  (declare (xargs :guard t))
  (list :bpnf-deleted epoch op arrival identity reason))

(defun fn-bpn-report-delete-recordp (record)
  (declare (xargs :guard t))
  (and (true-listp record) (equal (len record) 6)
       (equal (car record) :bpnf-deleted)
       (fn-frame-natp (nth 1 record))
       (fn-frame-natp (nth 2 record))
       (fn-frame-natp (nth 3 record))
       (fn-cbor-octet-listp (nth 4 record))
       (consp (nth 4 record))
       (<= (len (nth 4 record)) 1024)
       (equal (nth 5 record) :lifetime-expired)))

(defun fn-bpn-report-held-delete-pendingp (held)
  (declare (xargs :guard t))
  (and (fn-bpnf-heldp held)
       (null (fn-bpn-nth 10 held))
       (equal (fn-bpn-nth 12 held) '(:dispatch-pending))
       (null (fn-bpn-nth 14 held))))

(defun fn-bpn-report-delete-matches-heldp (record held)
  (declare (xargs :guard t))
  (and (fn-bpn-report-delete-recordp record)
       (fn-bpn-report-held-delete-pendingp held)
       (equal (nth 3 record) (fn-bpn-nth 3 held))
       (equal (nth 4 record)
              (fn-bpp-primary-identity
               (fn-bpb-bundle-primary (fn-bpnf-held-bundle held))))))

(defthm fn-bpn-report-held-bundle-for-guard
  (implies (fn-bpnf-heldp held)
           (fn-bpb-bundlep (fn-bpnf-held-bundle held)))
  :hints (("Goal" :in-theory (enable fn-bpnf-heldp))))

(defthm fn-bpn-report-primary-for-guard
  (implies (fn-bpb-bundlep bundle)
           (fn-bpp-blockp (fn-bpb-bundle-primary bundle)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms ((fn-bpb-bundle-primary bundle))))
  :hints (("Goal" :in-theory (e/d (fn-bpb-bundlep)
                                  (fn-bpp-blockp fn-bpp-eidp
                                   fn-bpp-vchar-listp fn-bpp-vcharp)))))

(defun fn-bpn-report-tombstone-held (held reason)
  (declare (xargs :guard t))
  (fn-bpnf-held (fn-bpn-nth 1 held) (fn-bpn-nth 2 held)
                (fn-bpn-nth 3 held) (fn-bpn-nth 4 held)
                (fn-bpn-nth 5 held) (fn-bpn-nth 6 held)
                (fn-bpn-nth 7 held) (fn-bpn-nth 8 held)
                (fn-bpn-nth 9 held) (fn-bpn-nth 10 held)
                (fn-bpn-nth 11 held) (fn-bpn-nth 12 held)
                (fn-bpn-nth 13 held) reason (fn-bpn-nth 15 held)))

(defun fn-bpn-report-apply-delete (record held-list)
  (declare (xargs :guard t :measure (acl2-count held-list)))
  (if (atom held-list)
      (mv nil held-list)
    (if (equal (fn-bpn-nth 3 record) (fn-bpn-nth 3 (car held-list)))
        (if (fn-bpn-report-delete-matches-heldp record (car held-list))
            (mv t (cons (fn-bpn-report-tombstone-held
                         (car held-list) (fn-bpn-nth 5 record))
                        (cdr held-list)))
          (mv nil held-list))
      (mv-let (ok rest)
        (fn-bpn-report-apply-delete record (cdr held-list))
        (mv ok (cons (car held-list) rest))))))

; The only live source of this record is an uncommitted held carrier whose
; current ACL2 clock decision is definitely expired.  Legacy anchorless or
; ambiguous intervals return no candidate, never a guessed deletion.
(defun fn-bpn-report-find-expired-held (held-list observation)
  (declare (xargs :guard t :measure (acl2-count held-list)))
  (if (atom held-list)
      nil
    (if (and (fn-bpn-report-held-delete-pendingp (car held-list))
             (equal (fn-bpah-held-expiry (car held-list) observation)
                    :expired))
        (car held-list)
      (fn-bpn-report-find-expired-held (cdr held-list) observation))))

(defthm fn-bpn-report-find-expired-held-is-expired
  (implies (fn-bpn-report-find-expired-held held-list observation)
           (equal (fn-bpah-held-expiry
                   (fn-bpn-report-find-expired-held held-list observation)
                   observation)
                  :expired))
  :hints (("Goal" :induct (fn-bpn-report-find-expired-held
                            held-list observation)
           :in-theory (e/d (fn-bpn-report-find-expired-held)
                           (fn-bpah-held-expiry
                            fn-bpn-report-held-delete-pendingp)))))

(defthm fn-bpn-report-tombstone-not-pending
  (not (fn-bpn-report-held-delete-pendingp
        (fn-bpn-report-tombstone-held held :lifetime-expired)))
  :hints (("Goal" :in-theory (enable fn-bpn-report-held-delete-pendingp
                                      fn-bpn-report-tombstone-held))))

(verify-guards fn-bpn-report-delete-recordp)
(verify-guards fn-bpn-report-held-delete-pendingp)
(verify-guards fn-bpn-report-delete-matches-heldp
  :hints (("Goal" :use ((:instance fn-bpn-report-held-bundle-for-guard)
                         (:instance fn-bpn-report-primary-for-guard
                          (bundle (fn-bpnf-held-bundle held))))
           :in-theory (disable fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpp-blockp
                               fn-bpn-report-held-bundle-for-guard
                               fn-bpn-report-primary-for-guard))))
(verify-guards fn-bpn-report-tombstone-held)
(verify-guards fn-bpn-report-apply-delete)
(verify-guards fn-bpn-report-find-expired-held)
