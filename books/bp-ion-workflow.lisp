; Optional ION sender evidence on top of the existing FNWF application work.
; The BP workflow state remains the owner of attempts and receipts. This
; auxiliary state remembers a durable BP route and at most one real ION ID for
; each exact attempt; neither record releases an obligation.
(in-package "ACL2")
(include-book "bp-ion-observation")
(include-book "bp-release")

(defun fn-bpiw-key (record)
  (declare (xargs :guard t :verify-guards nil))
  (list (nth 1 record) (nth 2 record) (nth 3 record)))

(defun fn-bpiw-route-recordp (record)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp record) (equal (len record) 7)
       (equal (nth 0 record) :ion-route)
       (fn-bp-journal-textp (nth 1 record))
       (fn-bp-journal-textp (nth 2 record))
       (fn-bp-u64p (nth 3 record))
       (fn-bpio-eid-fieldp (nth 4 record))
       (fn-bpio-eid-fieldp (nth 5 record))
       (fn-bpio-eid-fieldp (nth 6 record))))

(defun fn-bpiw-find-key (key records)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count records)))
  (if (endp records) nil
    (if (equal key (fn-bpiw-key (car records)))
        (car records)
      (fn-bpiw-find-key key (cdr records)))))

; (routes observations), both lists newest first. The route record is durable
; before bp_send. Its application peer is checked against the exact ADU rather
; than copied from a host-computed route table.
(defun fn-bpiw-routes (ion) (declare (xargs :guard t :verify-guards nil)) (car ion))
(defun fn-bpiw-observations (ion) (declare (xargs :guard t :verify-guards nil)) (cadr ion))
(defun fn-bpiw-initial () (declare (xargs :guard t :verify-guards nil)) (list nil nil))

(defun fn-bpiw-route-admissiblep (bp ion record)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bpiw-route-recordp record)) nil
    (let ((request (fn-bpo-request-message
                    bp (nth 1 record) (nth 2 record) (nth 3 record))))
      (and (consp request)
           (not (fn-bpiw-find-key (fn-bpiw-key record)
                                   (fn-bpiw-routes ion)))
           (equal (nth 4 record)
                  (fn-bpa-request-destination-eid request))))))

(defun fn-bpiw-observation-admissiblep (bp ion record)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bpio-bound-recordp bp record)) nil
    (let ((route (fn-bpiw-find-key (fn-bpiw-key record)
                                    (fn-bpiw-routes ion))))
      (and (consp route)
           (not (fn-bpiw-find-key (fn-bpiw-key record)
                                   (fn-bpiw-observations ion)))
           (equal (nth 4 record) (nth 4 route))
           (equal (nth 5 record) (nth 5 route))
           (equal (nth 6 record) (nth 6 route))))))

(defun fn-bpiw-attempt-record (bp txid tx-generation work-id attempt-id)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((work (fn-bp-find-work work-id (fn-bp-state-works bp)))
         (config (fn-bp-state-config bp))
         (record (list :attempt txid tx-generation work-id attempt-id
                       (fn-bp-work-next-generation work)
                       (fn-bp-config-local-eid config)
                       (fn-bp-config-peer-eid config)
                       (fn-bp-config-policy-id config)
                       (fn-bp-config-lifetime config))))
    (if (and (fn-bp-journal-recordp record)
             (car (fn-bprl-apply-journal-record bp record)))
        record nil)))

(defun fn-bpiw-route-record (bp ion work-id attempt-id generation
                                bp-destination own-bp-eid)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((work (fn-bp-find-work work-id (fn-bp-state-works bp)))
         (record (list :ion-route work-id attempt-id generation
                       (fn-bp-work-peer-eid work)
                       bp-destination own-bp-eid)))
    (if (fn-bpiw-route-admissiblep bp ion record) record nil)))

(defun fn-bpiw-observation-record (bp ion work-id attempt-id generation
                                     bp-destination own-bp-eid line)
  (declare (xargs :guard t :verify-guards nil))
  (let ((result (fn-bpio-bound-observation
                 bp work-id attempt-id generation
                 bp-destination own-bp-eid line)))
    (if (and (equal (car result) :ok)
             (fn-bpiw-observation-admissiblep bp ion (cadr result)))
        (cadr result) nil)))

(defun fn-bpiw-status (ion work-id attempt-id generation)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((key (list work-id attempt-id generation))
         (observation (fn-bpiw-find-key key (fn-bpiw-observations ion)))
         (route (fn-bpiw-find-key key (fn-bpiw-routes ion))))
    (cond ((consp observation) (list :observed observation))
          ((consp route) (list :uncertain route))
          (t (list :absent)))))

; Result: (okp next-bp effects next-ion). Existing FNWF records use the
; unchanged application-work interpreter. Rejected ION records never mutate.
(defun fn-bpiw-apply (bp ion record)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((equal (car record) :ion-route)
    (if (fn-bpiw-route-admissiblep bp ion record)
        (list t bp nil
              (list (cons record (fn-bpiw-routes ion))
                    (fn-bpiw-observations ion)))
      (list nil bp nil ion)))
   ((equal (car record) :ion-observed)
    (if (fn-bpiw-observation-admissiblep bp ion record)
        (list t bp nil
              (list (fn-bpiw-routes ion)
                    (cons record (fn-bpiw-observations ion))))
      (list nil bp nil ion)))
   (t (let ((answer (fn-bprl-apply-journal-record bp record)))
        (list (car answer) (nth 1 answer) (nth 2 answer) ion)))))

; A recovery outcome is written only after a reopen, whose :restart fenced
; the pending intent.  The journal does not record that restart, so disk
; replay reconstructs the fence (an :indeterminate completion of the matching
; pending) immediately before the recovery outcome, exactly as
; fn-bp-replay-records does.  On any other record, and on a pending that does
; not match or is already fenced, this is the identity, and the recovery
; outcome itself still decides acceptance through fn-bpiw-apply.
(defun fn-bpiw-recovery-outcomep (record)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-bp-journal-nth 0 record) :outcome)
       (equal (fn-bp-journal-nth 3 record) :recovery)))

(defun fn-bpiw-replay-fence (bp record)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-bpiw-recovery-outcomep record)
      (fn-bp-result-state
       (fn-bp-step bp (fn-bp-storage-complete-event
                       (fn-bp-journal-nth 1 record)
                       (fn-bp-journal-nth 2 record) :indeterminate)))
    bp))

(defun fn-bpiw-replay-records (bp ion records effects)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count records)))
  (if (endp records)
      (let ((restarted (fn-bp-step bp (fn-bp-restart-event))))
        (list t (fn-bp-result-state restarted)
              (append effects (fn-bp-result-effects restarted)) ion))
    (let ((answer (fn-bpiw-apply (fn-bpiw-replay-fence bp (car records))
                                 ion (car records))))
      (if (not (car answer))
          (list nil bp effects ion)
        (fn-bpiw-replay-records
         (nth 1 answer) (nth 3 answer) (cdr records)
         (append effects (nth 2 answer)))))))

(defun fn-bpiw-replay-journal (node records)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (endp records) (not (fn-bp-config-recordp (car records))))
      (list nil nil nil (fn-bpiw-initial))
    (let ((bp (fn-bp-initial-state
               node (fn-bp-config-from-record (car records)))))
      (if (not (fn-bp-statep bp))
          (list nil nil nil (fn-bpiw-initial))
        (fn-bpiw-replay-records bp (fn-bpiw-initial) (cdr records) nil)))))

(defthm fn-bpiw-ion-record-keeps-bp-state
  (implies (member-equal (car record) '(:ion-route :ion-observed))
           (equal (nth 1 (fn-bpiw-apply bp ion record)) bp))
  :hints (("Goal" :in-theory
           (e/d (fn-bpiw-apply)
                (fn-bpiw-route-admissiblep
                 fn-bpiw-observation-admissiblep)))))

(defthm fn-bpiw-ion-record-emits-no-effects
  (implies (member-equal (car record) '(:ion-route :ion-observed))
           (equal (nth 2 (fn-bpiw-apply bp ion record)) nil))
  :hints (("Goal" :in-theory
           (e/d (fn-bpiw-apply)
                (fn-bpiw-route-admissiblep
                 fn-bpiw-observation-admissiblep)))))
