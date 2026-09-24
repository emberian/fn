; One ordered FNBS replay for kind 5 reception, kind 7 application result,
; and kind 18 atomic fragment-family replacement. This supersedes the
; kind-5/7-only fold when the native service enables family publication.
(in-package "ACL2")
(include-book "bp-node-fragment-replacement")
(include-book "bp-fnbs-delivery-replay")
(include-book "bp-fnbs-deletion-codec")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-family-replay-row-record (row)
  (declare (xargs :guard t))
  (if (not (fn-bpnf-replay-rowp row)) nil
    (let ((stored (fn-bpnf-stored-record-unframe (cadr row))))
      (if stored stored
        (let ((delivered (fn-bpah-delivery-unframe (cadr row))))
          (if delivered delivered
            (let ((family (fn-bpnf-family-replay-unframe (cadr row))))
              (if family family
                (fn-bpnf-delete-unframe (cadr row))))))))))

(defun fn-bpnf-family-replay-rows-aux
  (rows base held handoffs prior next-arrival)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (atom rows)
      (if (null rows) (list :ready held handoffs prior next-arrival)
        (list :fault :improper-rows))
    (let* ((row (car rows))
           (record (fn-bpnf-family-replay-row-record row))
           (epoch (fn-bpn-nth 1 record))
           (op (fn-bpn-nth 2 record))
           (next (cons epoch op)))
      (if (not (and record
                    (equal (car row) (fn-bpnf-stored-record-name epoch op))
                    (fn-bpnf-replay-pair-afterp epoch op prior)))
          (list :fault :received-row)
        (cond
         ((equal (car record) :bpnf-stored)
          (let ((h (fn-bpn-nth 3 record)))
            (if (not (and (equal (fn-bpn-nth 3 h) next-arrival)
                          (equal (fn-bpnf-receive-decision
                                  held (fn-bpn-nth 4 h)
                                  (fn-bpnf-held-bundle h)) :fresh)
                          (< (len held)
                             (fn-bpn-machine-state-max-jobs base))
                          (<= (+ (fn-bpnf-held-octets held)
                                 (len (fn-bpnf-held-wire h)))
                              (fn-bpn-machine-state-max-octets base))))
                (list :fault :kind-five-row)
              (fn-bpnf-family-replay-rows-aux
               (cdr rows) base (cons h held) handoffs next
               (1+ next-arrival)))))
         ((equal (car record) :bpnf-delivered)
          (mv-let (ok updated handoff)
            (fn-bpah-apply-delivery record held)
            (if (not ok) (list :fault :kind-seven-row)
              (fn-bpnf-family-replay-rows-aux
               (cdr rows) base updated
               (if handoff (cons handoff handoffs) handoffs)
               next next-arrival))))
         ((equal (car record) :bpnf-family)
          (let* ((st (fn-bpnf-state base held nil handoffs nil nil nil epoch op))
                 (applied (fn-bpnf-family-apply-at st record next-arrival)))
            (if (not (equal (car applied) :ready))
                (list :fault :kind-eighteen-row)
              (fn-bpnf-family-replay-rows-aux
               (cdr rows) base (fn-bpn-nth 1 applied)
               handoffs next (1+ next-arrival)))))
         ((equal (car record) :bpnf-deleted)
          (mv-let (ok updated)
            (fn-bpn-report-apply-delete record held)
            (if (not ok) (list :fault :kind-ten-row)
              (fn-bpnf-family-replay-rows-aux
               (cdr rows) base updated handoffs next next-arrival))))
         (t (list :fault :received-kind)))))))

(defun fn-bpnf-family-replay-rows (rows base)
  (declare (xargs :guard t))
  (fn-bpnf-family-replay-rows-aux rows base nil nil nil 0))

(defun fn-bpnf-family-recover-auto-event
  (st base-records sequence-ready rows)
  (declare (xargs :guard t))
  (let* ((replay (fn-bpnf-family-replay-rows rows (fn-bpnf-base st)))
         (prior (fn-bpn-nth 3 replay))
         (new-epoch (1+ (max (nfix (fn-bpnf-epoch st))
                             (nfix (and (consp prior) (car prior)))))))
    ; The count is the exact number of ordered received finals examined by
    ; replay, including rows subsequently consumed by a family replacement.
    ; It cannot be reconstructed from the surviving held list.
    (list :recover-fnbs new-epoch base-records sequence-ready replay
          (len rows))))

(defthm fn-bpnf-family-recover-event-carries-exact-row-count
  (equal (fn-bpn-nth
          5 (fn-bpnf-family-recover-auto-event
             st base-records sequence-ready rows))
         (len rows))
  :hints (("Goal" :in-theory (enable fn-bpnf-family-recover-auto-event)))
  :rule-classes nil)
