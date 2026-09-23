; One ordered FNBS recovery stream for received bundles (kind 5) and
; committed application results (kind 7).  A kind-7 result has authority
; only for the earlier exact kind-5 row it identifies.
(in-package "ACL2")
(include-book "bp-fnbs-delivery-codec")
(include-book "bp-fnbs-replay")
(include-book "bp-app-handoff")
(set-verify-guards-eagerness 0)

(defun fn-bpah-replay-row-record (row)
  (declare (xargs :guard t))
  (if (not (fn-bpnf-replay-rowp row)) nil
    (let ((stored (fn-bpnf-stored-record-unframe (cadr row))))
      (if stored stored (fn-bpah-delivery-unframe (cadr row))))))

(defun fn-bpah-replay-rows-aux (rows held handoffs prior max-held max-octets)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (atom rows)
      (if (null rows) (list :ready held handoffs prior)
        (list :fault :improper-rows))
    (let* ((row (car rows))
           (record (fn-bpah-replay-row-record row))
           (epoch (and record (nth 1 record)))
           (operation-id (and record (nth 2 record)))
           (next (cons epoch operation-id)))
      (if (not (and record
                    (equal (car row)
                           (fn-bpnf-stored-record-name epoch operation-id))
                    (fn-bpnf-replay-pair-afterp epoch operation-id prior)))
          (list :fault :received-row)
        (if (equal (car record) :bpnf-stored)
            (let ((h (nth 3 record)))
              (if (not (and (equal (nth 3 h) (len held))
                            (equal (fn-bpnf-receive-decision
                                    held (nth 4 h) (fn-bpnf-held-bundle h)) :fresh)
                            (natp max-held) (natp max-octets)
                            (< (len held) max-held)
                            (<= (+ (fn-bpnf-held-octets held)
                                   (len (fn-bpnf-held-wire h))) max-octets)))
                  (list :fault :kind-five-row)
                (fn-bpah-replay-rows-aux
                 (cdr rows) (cons h held) handoffs next max-held max-octets)))
          (mv-let (ok updated handoff)
            (fn-bpah-apply-delivery record held)
            (if (not ok)
                (list :fault :kind-seven-row)
              (fn-bpah-replay-rows-aux
               (cdr rows) updated
               (if handoff (cons handoff handoffs) handoffs)
               next max-held max-octets))))))))

(defun fn-bpah-replay-rows (rows max-held max-octets)
  (declare (xargs :guard t))
  (fn-bpah-replay-rows-aux rows nil nil nil max-held max-octets))

(defun fn-bpah-recover-auto-event (st base-records sequence-ready rows)
  (declare (xargs :guard t))
  (let* ((replay
          (fn-bpah-replay-rows
           rows
           (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
           (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
         (prior (fn-bpn-nth 3 replay))
         (new-epoch
          (1+ (max (nfix (fn-bpnf-epoch st))
                   (nfix (and (consp prior) (car prior)))))))
    (list :recover-fnbs new-epoch base-records sequence-ready replay)))

(defthm fn-bpah-kind-seven-without-kind-five-faults
  (implies (fn-bpah-delivery-recordp record)
           (equal (fn-bpah-apply-delivery record nil)
                  (mv nil nil nil))))
