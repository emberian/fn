; RET-010: finite Store transaction identities are an independent resource.
; A forward undertaking's actual continuation publishes one release record.
; Checkpoint/compact/reclaim publish no journal record and demand zero IDs.
; This gate is called immediately before the host's serialized reservation.
; It grants ONE imminent reservation, not a reusable maintenance capability.
(in-package "ACL2")
(include-book "store-node")

(defun fn-idr-next (frontier debt purpose)
  (declare (xargs :guard t))
  (cond ((not (and (natp frontier) (< frontier *fn-sf-max-uint*)))
         :identity-exhausted)
        ((not (member-eq purpose '(:ordinary :undertake :release)))
         :operation-refused)
        ((and (eq purpose :release) (not (posp debt)))
         :operation-refused)
        ((< (- *fn-sf-max-uint* frontier)
            (+ 1 (cond ((eq purpose :undertake) (+ 1 (nfix debt)))
                       ((eq purpose :release) (- (nfix debt) 1))
                       (t (nfix debt)))))
         :identity-reserve)
        (t (+ 1 frontier))))

; OPERATION is the ACL2-authored five-field retention publication, never a
; caller's purpose flag.  NIL denotes an ordinary reservation.  Invalid or
; no-longer-admissible retention operations cannot spend protected identities.
(defun fn-idr-retention-candidate (s operation)
  (declare (xargs :guard t))
  (let ((txid (fn-sf-frontier (fn-sn-files s))))
    (if (and (true-listp operation) (equal (len operation) 5))
        (list :retention
         (nth 0 operation) (fn-sn-identity-next s) txid txid
         (nth 1 operation) (nth 2 operation) (nth 3 operation)
         (nth 4 operation))
      nil)))

(defun fn-idr-purpose (s operation)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (null operation)
      (if (equal (fn-sf-phase (fn-sn-files s)) :ready) :ordinary :invalid)
    (let ((event (fn-idr-retention-candidate s operation)))
      (if (and (equal (fn-sf-phase (fn-sn-files s)) :ready)
               (fn-store-retention-event-p event)
               (eq (car (fn-cpe-projection-step
                         (fn-sn-consumer s) event (fn-sn-identity-next s))) :ok)
               (consp (fn-replay-apply-retention-event (fn-sn-node s) event)))
          (fn-store-event-kind event)
        :invalid))))

(verify-guards fn-idr-purpose
  :hints (("Goal" :in-theory (enable fn-sn-statep))))

(defun fn-idr-reservation (s debt operation)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (fn-idr-next (fn-sf-frontier (fn-sn-files s)) debt
               (fn-idr-purpose s operation)))

(verify-guards fn-idr-reservation)

(defun fn-idr-grant (s operation)
  (declare (xargs :guard t))
  (list :identity-grant (fn-sf-frontier (fn-sn-files s))
        (fn-idr-retention-candidate s operation)))

(defun fn-idr-grant-boundp (s event grant)
  (declare (xargs :guard t))
  (and (true-listp grant) (equal (len grant) 3)
       (eq (car grant) :identity-grant) (natp (nth 1 grant))
       (equal (fn-sf-phase (fn-sn-files s)) :reserved)
       (equal (fn-sf-frontier (fn-sn-files s)) (+ 1 (nth 1 grant)))
       (equal event (nth 2 grant))))

; The host calls this before preparation and installs REMAINING first, even
; when the prepare may throw.  Grants are consumed on a refused attempt too.
(defun fn-idr-consume-grant (s event grant)
  (declare (xargs :guard t))
  (mv (fn-idr-grant-boundp s event grant) nil))

(defthm fn-idr-consume-grant-unfolds
  (equal (fn-idr-consume-grant s event grant)
         (mv (fn-idr-grant-boundp s event grant) nil)))

; Ordinary requests, including a later semantic refusal, leave all promised
; release IDs.  The undertaking also pays for its new release before issuing.
(defthm fn-idr-ordinary-leaves-promised-release-identities
  (implies (natp (fn-idr-next frontier debt :ordinary))
           (<= (nfix debt)
               (- *fn-sf-max-uint* (nfix (fn-idr-next frontier debt :ordinary)))))
  :hints (("Goal" :in-theory (enable fn-idr-next))))

(defthm fn-idr-undertaking-leaves-its-own-release-identity
  (implies (natp (fn-idr-next frontier debt :undertake))
           (<= (+ 1 (nfix debt))
               (- *fn-sf-max-uint* (nfix (fn-idr-next frontier debt :undertake)))))
  :hints (("Goal" :in-theory (enable fn-idr-next))))

(defthm fn-idr-release-leaves-the-other-promised-identities
  (implies (natp (fn-idr-next frontier debt :release))
           (and (posp debt)
                (<= (- debt 1)
                    (- *fn-sf-max-uint* (nfix (fn-idr-next frontier debt :release))))))
  :hints (("Goal" :in-theory (enable fn-idr-next))))

(defthm fn-idr-grant-issues-exactly-one-fresh-identity
  (implies (natp (fn-idr-next frontier debt purpose))
           (and (natp frontier)
                (equal (fn-idr-next frontier debt purpose) (+ 1 frontier))
                (<= (fn-idr-next frontier debt purpose) *fn-sf-max-uint*)))
  :hints (("Goal" :in-theory (enable fn-idr-next))))

(defthm fn-idr-reservation-ordinary-leaves-promised-release-identities
  (implies (natp (fn-idr-reservation s debt nil))
           (<= (nfix debt)
               (- *fn-sf-max-uint* (nfix (fn-idr-reservation s debt nil)))))
  :hints (("Goal" :in-theory (enable fn-idr-reservation fn-idr-purpose
                                     fn-idr-next))))

; A failed publication has not discharged debt.  Its already issued identity
; is burned; no theorem above promises retry under arbitrary failures.  The
; next gate explicitly refuses if the remaining domain cannot fund that debt.
(in-theory (disable fn-idr-next fn-idr-retention-candidate fn-idr-purpose
                    fn-idr-reservation fn-idr-grant fn-idr-grant-boundp
                    fn-idr-consume-grant))
