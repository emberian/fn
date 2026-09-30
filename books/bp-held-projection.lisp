;; The receiver's held projection at open (lane bp-catalog, wave 5).
;;
;; The open replays the receiver journal (FNBS) into the held list:
;; fn-bpnf-family-replay-rows-aux, the fold that bp-fnbs-family-replay
;; defines, is the SPEC and is kept.  As written, every kind-5 row re-summed
;; the wire lengths of the whole held list to check the profile's octet
;; bound (fn-bpnf-held-octets): quadratic in the held octets, 5 s of
;; SCN-077's 51.9 s open at 1,311 held rows of 4 KiB (bp-lifecycle-5).
;;
;; Here the octet total is a PROJECTION carried beside the held list and
;; advanced by each row: a kind-5 arrival adds its wire length; a row that
;; rewrites the held list (kinds 7, 18, 10, 6, 8, 9, 20) re-derives it from
;; the list it produced (those rows are rare at open: one per completed
;; family or settled job); a kind-14 row keeps it.  The relation the fold
;; maintains is OCTETS = (fn-bpnf-held-octets HELD); it is established at
;; the open's entry (0 for the empty list, the checkpoint's held list summed
;; once) and preserved by every arm, which is fn-bphp-replay-rows-is-aux.
;;
;; The host entry: host/native/bp-service.lisp fnn-bps-open calls
;; fn-bphp-recover-auto-event, equal to fn-bpnr-recover-auto-event by
;; fn-bphp-recover-auto-event-is-bpnr (hypothesis-free), so every theorem
;; about the recovery event (PRF-081, N16's rotation keystones, PRF-131's
;; profile replay) is about the event the host builds.
(in-package "ACL2")
(include-book "bp-node-rotation")
(set-verify-guards-eagerness 0)

(defun fn-bphp-replay-rows
  (rows base held handoffs prior next-arrival octets)
  (declare (xargs :guard (and (fn-bpn-machine-statep base)
                              (natp next-arrival) (natp octets)
                              (or (null prior)
                                  (and (consp prior) (natp (car prior))
                                       (natp (cdr prior)))))
                  :measure (acl2-count rows)))
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
            (cond
             ((not (and (equal (fn-bpn-nth 3 h) next-arrival)
                        (equal (fn-bpnf-receive-decision
                                held (fn-bpn-nth 4 h)
                                (fn-bpnf-held-bundle h)) :fresh)))
              (list :fault :kind-five-row))
             ;; A well-formed row the node's profile cannot hold (the
             ;; journal was written under a larger profile): a named
             ;; verdict, never a truncated held list (PRF-131 part 2).
             ((not (and (< (len held)
                           (fn-bpn-machine-state-max-jobs base))
                        (<= (+ octets (len (fn-bpnf-held-wire h)))
                            (fn-bpn-machine-state-max-octets base))))
              (list :fault :held-beyond-profile))
             (t
              (fn-bphp-replay-rows
               (cdr rows) base (cons h held) handoffs next
               (1+ next-arrival)
               (+ octets (len (fn-bpnf-held-wire h))))))))
         ((equal (car record) :bpnf-delivered)
          (mv-let (ok updated handoff)
            (fn-bpah-apply-delivery record held)
            (if (not ok) (list :fault :kind-seven-row)
              (fn-bphp-replay-rows
               (cdr rows) base updated
               (if handoff (cons handoff handoffs) handoffs)
               next next-arrival (fn-bpnf-held-octets updated)))))
         ((equal (car record) :bpnf-family)
          (let* ((st (fn-bpnf-state base held nil handoffs nil nil nil epoch op))
                 (applied (fn-bpnf-family-apply-at st record next-arrival)))
            (if (not (equal (car applied) :ready))
                (list :fault :kind-eighteen-row)
              (fn-bphp-replay-rows
               (cdr rows) base (fn-bpn-nth 1 applied)
               handoffs next (1+ next-arrival)
               (fn-bpnf-held-octets (fn-bpn-nth 1 applied))))))
         ((equal (car record) :bpnf-deleted)
          (mv-let (ok updated)
            (fn-bpn-report-apply-delete record held)
            (if (not ok) (list :fault :kind-ten-row)
              (fn-bphp-replay-rows
               (cdr rows) base updated handoffs next next-arrival
               (fn-bpnf-held-octets updated)))))
         ((equal (car record) :bpnf-dispatched)
          (let ((applied (fn-bpnp-dispatch-apply record held)))
            (if (not (equal (car applied) :ready))
                (list :fault :kind-six-row)
              (fn-bphp-replay-rows
               (cdr rows) base (fn-bpn-nth 1 applied)
               handoffs next next-arrival
               (fn-bpnf-held-octets (fn-bpn-nth 1 applied))))))
         ((equal (car record) :bpnf-attempting)
          (let ((applied (fn-bpnp-attempt-apply record held)))
            (if (not (equal (car applied) :ready))
                (list :fault :kind-eight-row)
              (fn-bphp-replay-rows
               (cdr rows) base (fn-bpn-nth 1 applied)
               handoffs next next-arrival
               (fn-bpnf-held-octets (fn-bpn-nth 1 applied))))))
         ((equal (car record) :bpnf-forwarded)
          (let ((applied (fn-bpnp-forward-result-apply record held)))
            (if (not (equal (car applied) :ready))
                (list :fault :kind-nine-row)
              (fn-bphp-replay-rows
               (cdr rows) base (fn-bpn-nth 1 applied)
               handoffs next next-arrival
               (fn-bpnf-held-octets (fn-bpn-nth 1 applied))))))
         ((equal (car record) :bpnf-deferred)
          ; Kind 20: the busy count, through the apply the live arm calls.
          (let ((applied (fn-bpnp-deferral-apply record held)))
            (if (not (equal (car applied) :ready))
                (list :fault :kind-twenty-row)
              (fn-bphp-replay-rows
               (cdr rows) base (fn-bpn-nth 1 applied)
               handoffs next next-arrival
               (fn-bpnf-held-octets (fn-bpn-nth 1 applied))))))
         ((equal (car record) :bpnf-conflict)
          (let ((applied (fn-bpnf-conflict-apply record held)))
            (if (not (equal (car applied) :ready))
                (list :fault :kind-fourteen-row)
              (fn-bphp-replay-rows
               (cdr rows) base held handoffs next next-arrival octets))))
         (t (list :fault :received-kind)))))))

(defthm fn-bphp-held-octets-of-cons
  (equal (fn-bpnf-held-octets (cons h held))
         (+ (len (fn-bpnf-held-wire h)) (fn-bpnf-held-octets held)))
  :hints (("Goal" :expand ((fn-bpnf-held-octets (cons h held)))
           :in-theory (union-theories '(car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

; Keystone: the carried projection is the fold's.  Under the relation
; OCTETS = (fn-bpnf-held-octets HELD) the projected replay is the spec.
(defthm fn-bphp-replay-rows-is-aux
  (implies (equal octets (fn-bpnf-held-octets held))
           (equal (fn-bphp-replay-rows rows base held handoffs prior
                                       next-arrival octets)
                  (fn-bpnf-family-replay-rows-aux rows base held handoffs
                                                  prior next-arrival)))
  :hints (("Goal" :induct (fn-bphp-replay-rows rows base held handoffs prior
                                               next-arrival octets)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (union-theories
                       '(fn-bphp-replay-rows fn-bpnf-family-replay-rows-aux
                         fn-bphp-held-octets-of-cons commutativity-of-+)
                       (theory 'minimal-theory)))))

; The open's entry: the relation holds at the start of the fold.
(defun fn-bphp-replay-from (ck rows base)
  (declare (xargs :guard (fn-bpn-machine-statep base)))
  (if (fn-bpnr-checkpointp ck)
      (fn-bphp-replay-rows
       rows base (fn-bpnr-checkpoint-held ck) (fn-bpnr-checkpoint-handoffs ck)
       (fn-bpnr-checkpoint-prior ck) (fn-bpnr-checkpoint-next-arrival ck)
       (fn-bpnf-held-octets (fn-bpnr-checkpoint-held ck)))
    (fn-bphp-replay-rows rows base nil nil nil 0 0)))

(defthm fn-bphp-replay-from-is-bpnr
  (equal (fn-bphp-replay-from ck rows base)
         (fn-bpnr-replay-from ck rows base))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bphp-replay-from fn-bpnr-replay-from
                         fn-bpnf-family-replay-rows fn-bphp-replay-rows-is-aux
                         (:executable-counterpart fn-bpnf-held-octets))
                       (theory 'minimal-theory)))))

; The event the host builds at open (fnn-bps-open).
(defun fn-bphp-recover-auto-event (st base-records sequence-ready rows plan)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))))
  (let* ((replay (if (equal (fn-cbor-ag-car plan) :damaged)
                     (list :fault :generation-authority)
                   (fn-bphp-replay-from (fn-bpnr-plan-checkpoint plan)
                                        rows (fn-bpnf-base st))))
         (prior (fn-bpn-nth 3 replay))
         (new-epoch (1+ (max (nfix (fn-bpnf-epoch st))
                             (nfix (and (consp prior) (car prior)))))))
    (list :recover-fnbs new-epoch base-records sequence-ready replay
          (len rows))))

(defthm fn-bphp-recover-auto-event-is-bpnr
  (equal (fn-bphp-recover-auto-event st base-records sequence-ready rows plan)
         (fn-bpnr-recover-auto-event st base-records sequence-ready rows plan))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bphp-recover-auto-event fn-bpnr-recover-auto-event
                         fn-bphp-replay-from-is-bpnr)
                       (theory 'minimal-theory)))))
