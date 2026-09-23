; Recovery observation for the A1 received-bundle subset of FNBS.
; Rows are bounded final-name/file-octet observations.  The codec owns
; their meaning; this fold checks byte/name authority and constructs the
; held projection that fn-bpnf-step installs at its recovery event.
(in-package "ACL2")
(include-book "bp-fnbs-codec")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-replay-rowp (row)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 2)
       (stringp (car row))
       (fn-cbor-octet-listp (cadr row))))

(defun fn-bpnf-replay-pair-afterp (epoch operation-id prior)
  (declare (xargs :guard t))
  (or (null prior)
      (< (car prior) epoch)
      (and (equal (car prior) epoch)
           (< (cdr prior) operation-id))))

(defun fn-bpnf-replay-rows-aux (rows held prior max-held max-octets)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (atom rows)
      (if (null rows) (list :ready held prior)
        (list :fault :improper-rows))
    (let* ((row (car rows))
           (record (and (fn-bpnf-replay-rowp row)
                        (fn-bpnf-stored-record-unframe (cadr row))))
           (epoch (and record (nth 1 record)))
           (operation-id (and record (nth 2 record)))
           (h (and record (nth 3 record))))
      (if (not (and record
                    (equal (car row)
                           (fn-bpnf-stored-record-name epoch operation-id))
                    (fn-bpnf-replay-pair-afterp epoch operation-id prior)
                    (equal (nth 3 h) (len held))
                    (equal (fn-bpnf-receive-decision
                            held (nth 4 h) (fn-bpnf-held-bundle h)) :fresh)
                    (natp max-held) (natp max-octets)
                    (< (len held) max-held)
                    (<= (+ (fn-bpnf-held-octets held)
                           (len (fn-bpnf-held-wire h))) max-octets)))
          (list :fault :kind-five-row)
        (fn-bpnf-replay-rows-aux
         (cdr rows) (cons h held) (cons epoch operation-id)
         max-held max-octets)))))

(defun fn-bpnf-replay-rows (rows max-held max-octets)
  (declare (xargs :guard t))
  (fn-bpnf-replay-rows-aux rows nil nil max-held max-octets))

; The host passes this ACL2-built event to the sole state transition,
; fn-bpnf-step.  It does not assemble a replay-result from Lisp objects.
(defun fn-bpnf-recover-event (st new-epoch base-records sequence-ready rows)
  (declare (xargs :guard t))
  (list :recover-fnbs new-epoch base-records sequence-ready
        (fn-bpnf-replay-rows
         rows
         (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
         (fn-bpn-machine-state-max-octets (fn-bpnf-base st)))))

; Select the fresh process epoch from the same exact byte replay supplied to
; the recovery event.  A terminal 64-bit epoch makes the step fault rather
; than wrapping or letting the host choose a reused epoch.
(defun fn-bpnf-recover-auto-event (st base-records sequence-ready rows)
  (declare (xargs :guard t))
  (let* ((replay
          (fn-bpnf-replay-rows
           rows
           (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))
           (fn-bpn-machine-state-max-octets (fn-bpnf-base st))))
         (prior (nth 2 replay))
         (new-epoch
          (1+ (max (nfix (fn-bpnf-epoch st))
                   (nfix (and (consp prior) (car prior)))))))
    (list :recover-fnbs new-epoch base-records sequence-ready replay)))

(defthm fn-bpnf-recover-auto-event-epoch-exceeds-current
  (implies (natp (fn-bpnf-epoch st))
           (< (fn-bpnf-epoch st)
              (nth 1 (fn-bpnf-recover-auto-event
                      st base-records sequence-ready rows))))
  :hints (("Goal" :in-theory
           (e/d (fn-bpnf-recover-auto-event)
                (fn-bpnf-replay-rows fn-bpnf-replay-rows-aux)))))
