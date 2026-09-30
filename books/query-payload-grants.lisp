; Indexed per-query arena ownership; snapshot singleton stays separate.
; Lower retained-grant primitive: GRANT is carried actual admission supplied
; by the provider; this book does not establish allocator/profile adequacy or
; captured-row source authorization. Segment slots bound each step, not data.
(in-package "ACL2")
(include-book "snapshot-source-token")
(defstobj fn-query-payload-grants
  (fn-qpg-rows :type (array t (64)) :initially nil)
  (fn-qpg-segment-id :type (integer 0 *) :initially 0)
  (fn-qpg-active :type (integer 0 *) :initially 0))
(defun fn-qpg-tokenp (x)
  (declare (xargs :guard t))
  (and (fn-omk-widthp x 7) (eq (fn-omk-at 0 x) :query-payload)
       (natp (fn-omk-at 1 x)) (natp (fn-omk-at 2 x))
       (natp (fn-omk-at 3 x)) (natp (fn-omk-at 4 x))
       (natp (fn-omk-at 5 x)) (posp (fn-omk-at 6 x))))
(defun fn-qpg-slot (token)
  (declare (xargs :guard t))
  (if (fn-qpg-tokenp token) (fn-omk-at 2 token) 0))
(defun fn-qpg-livep (token fn-query-payload-grants)
  (declare (xargs :stobjs fn-query-payload-grants :guard t))
  (and (fn-qpg-tokenp token)
       (equal (fn-omk-at 6 token) (fn-qpg-segment-id fn-query-payload-grants))
       (< (fn-qpg-slot token) (fn-qpg-rows-length fn-query-payload-grants))
       (let ((row (fn-qpg-rowsi (fn-qpg-slot token) fn-query-payload-grants)))
         (and (equal token (fn-omk-at 0 row))
              (member-eq (fn-omk-at 2 row) '(:active :cancelled)) t))))
; One fixed segment is installed by the provider's bounded registry path.
; This initializer does not allocate or resize the segment's fixed arrays.
(defun fn-qpg-install-segment (id fn-query-payload-grants)
  (declare (xargs :stobjs fn-query-payload-grants :guard (posp id)))
  (if (not (equal (fn-qpg-segment-id fn-query-payload-grants) 0))
      (mv :refused fn-query-payload-grants)
    (let ((fn-query-payload-grants
           (update-fn-qpg-segment-id id fn-query-payload-grants)))
      (mv :installed fn-query-payload-grants))))
(defun fn-qpg-acquire (ticket slot generation incarnation prefix grant fn-query-payload-grants)
  (declare (xargs :stobjs fn-query-payload-grants
                  :guard (and (natp ticket) (natp slot) (natp generation)
                              (natp incarnation) (natp prefix))))
  (if (or (not grant) (equal (fn-qpg-segment-id fn-query-payload-grants) 0) (>= slot (fn-qpg-rows-length fn-query-payload-grants)))
      (mv :refused nil fn-query-payload-grants)
    (let* ((old (fn-qpg-rowsi slot fn-query-payload-grants))
           (spent (fn-omk-at 3 old)))
      (if (or (member-eq (fn-omk-at 2 old) '(:active :cancelled))
              (and (natp spent) (<= ticket spent)))
          (mv :refused nil fn-query-payload-grants)
        (let* ((token (list :query-payload ticket slot generation incarnation prefix
                           (fn-qpg-segment-id fn-query-payload-grants)))
               (fn-query-payload-grants
                (update-fn-qpg-rowsi slot (list token grant :active ticket)
                                    fn-query-payload-grants))
               (fn-query-payload-grants
                (update-fn-qpg-active (+ 1 (fn-qpg-active fn-query-payload-grants))
                                     fn-query-payload-grants)))
          (mv :acquired token fn-query-payload-grants))))))
(defun fn-qpg-cancel (token fn-query-payload-grants)
  (declare (xargs :stobjs fn-query-payload-grants :guard t))
  (if (not (fn-qpg-livep token fn-query-payload-grants))
      (mv :stale fn-query-payload-grants)
    (let* ((slot (fn-qpg-slot token))
           (row (fn-qpg-rowsi slot fn-query-payload-grants))
           (fn-query-payload-grants
            (update-fn-qpg-rowsi slot
                                (list token (fn-omk-at 1 row) :cancelled (fn-omk-at 3 row))
                                fn-query-payload-grants)))
      (mv :retained fn-query-payload-grants))))
(defun fn-qpg-release (token settlement fn-query-payload-grants)
  (declare (xargs :stobjs fn-query-payload-grants :guard t))
  (cond ((not (fn-qpg-livep token fn-query-payload-grants))
         (mv :stale nil fn-query-payload-grants))
        ((or (not (eq settlement :joined))
             (equal (fn-qpg-active fn-query-payload-grants) 0))
         (mv :retained nil fn-query-payload-grants))
        (t (let* ((slot (fn-qpg-slot token))
                  (row (fn-qpg-rowsi slot fn-query-payload-grants))
                  (grant (fn-omk-at 1 row))
                  (fn-query-payload-grants
                   (update-fn-qpg-rowsi slot (list nil nil :released (fn-omk-at 3 row))
                                       fn-query-payload-grants))
                  (fn-query-payload-grants
                   (update-fn-qpg-active (- (fn-qpg-active fn-query-payload-grants) 1)
                                        fn-query-payload-grants)))
             (mv :released grant fn-query-payload-grants)))))
(defun fn-qpg-ownedp (fn-query-payload-grants)
  (declare (xargs :stobjs fn-query-payload-grants :guard t))
  (< 0 (fn-qpg-active fn-query-payload-grants)))
(defthm fn-qpg-cancellation-retains-all-grant-debt
  (equal (fn-qpg-active (mv-nth 1 (fn-qpg-cancel token fn-query-payload-grants)))
         (fn-qpg-active fn-query-payload-grants))
  :hints (("Goal" :in-theory (enable fn-qpg-cancel fn-qpg-active update-fn-qpg-rowsi))))
(defthm fn-qpg-unjoined-release-retains-exact-registry
  (implies (not (eq settlement :joined))
           (equal (mv-nth 2 (fn-qpg-release token settlement fn-query-payload-grants))
                  fn-query-payload-grants)))
(defthm fn-qpg-release-requires-exact-live-grant-and-joined-by-definition
  (iff (equal (mv-nth 0 (fn-qpg-release token settlement fn-query-payload-grants)) :released)
       (and (fn-qpg-livep token fn-query-payload-grants)
            (eq settlement :joined)
            (not (equal (fn-qpg-active fn-query-payload-grants) 0)))))
(defthm fn-qpg-acquisition-adds-exactly-one-active-grant
  (implies (equal (mv-nth 0 (fn-qpg-acquire ticket slot generation incarnation prefix grant fn-query-payload-grants)) :acquired)
           (equal (fn-qpg-active (mv-nth 2 (fn-qpg-acquire ticket slot generation incarnation prefix grant fn-query-payload-grants)))
                  (+ 1 (fn-qpg-active fn-query-payload-grants)))))
(defthm fn-qpg-settlement-removes-exactly-one-active-grant
  (implies (equal (mv-nth 0 (fn-qpg-release token settlement fn-query-payload-grants)) :released)
           (equal (fn-qpg-active (mv-nth 2 (fn-qpg-release token settlement fn-query-payload-grants)))
                  (- (fn-qpg-active fn-query-payload-grants) 1))))
