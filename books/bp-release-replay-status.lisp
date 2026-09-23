; Status of the actual native FNWF replay interpreter, including the
; append-only undertaking and release records.  Durable-fold is the history
; before the process-death restart; it applies the same ACL2 interpreter as
; the host, and never treats a carrier event as release authority.
(in-package "ACL2")
(include-book "bp-release-invariants")
(include-book "bp-workflow-replay-status")

(defun fn-bprl-durable-fold (s records)
  (declare (xargs :guard t :verify-guards nil
                  :measure (acl2-count records)))
  (if (endp records)
      s
    (let ((answer (fn-bprl-apply-journal-record s (car records))))
      (if (car answer)
          (fn-bprl-durable-fold (fn-bp-journal-nth 1 answer) (cdr records))
        s))))

(local
 (defthm fn-bprl-release-record-apply-preserves-state
   (implies (and (fn-bp-statep s) (fn-bprl-release-recordp r))
            (fn-bp-statep
             (fn-bp-journal-nth 1 (fn-bprl-apply-journal-record s r))))
   :hints (("Goal"
            :use ((:instance fn-bprl-release-preserves-state
                             (receipt-id (fn-bp-journal-nth 1 r))))
            :in-theory (e/d (fn-bprl-apply-journal-record fn-bp-journal-nth)
                            (fn-bp-statep fn-bprl-release-recordp
                             fn-bprl-release-decision fn-bprl-undertake
                             fn-bp-apply-journal-record))))))

(local
 (defthm fn-bprl-undertake-record-apply-preserves-state
   (implies (and (fn-bp-statep s)
                 (not (fn-bprl-release-recordp r))
                 (fn-bprl-undertake-recordp r))
            (fn-bp-statep
             (fn-bp-journal-nth 1 (fn-bprl-apply-journal-record s r))))
   :hints (("Goal"
            :use ((:instance fn-bprl-undertake-preserves-state
                             (work-id (fn-bp-journal-nth 1 r))
                             (charge (fn-bp-journal-nth 2 r))))
            :in-theory (e/d (fn-bprl-apply-journal-record fn-bp-journal-nth)
                            (fn-bp-statep fn-bprl-release-recordp
                             fn-bprl-undertake-recordp fn-bprl-undertake
                             fn-bp-apply-journal-record))))))

(local
 (defthm fn-bprl-ordinary-record-apply-preserves-state
   (implies (and (fn-bp-statep s)
                 (not (fn-bprl-release-recordp r))
                 (not (fn-bprl-undertake-recordp r)))
            (fn-bp-statep
             (fn-bp-journal-nth 1 (fn-bprl-apply-journal-record s r))))
   :hints (("Goal"
            :use ((:instance fn-bp-apply-journal-record-preserves-state))
            :in-theory (e/d (fn-bprl-apply-journal-record)
                            (fn-bp-statep fn-bp-journal-nth
                             fn-bprl-release-recordp
                             fn-bprl-undertake-recordp
                             fn-bp-apply-journal-record))))))

(local
 (defthm fn-bprl-undertake-is-not-release-record
   (implies (fn-bprl-undertake-recordp r)
            (not (fn-bprl-release-recordp r)))
   :hints (("Goal" :in-theory (enable fn-bprl-undertake-recordp
                                      fn-bprl-release-recordp)))))

(defthm fn-bprl-apply-journal-record-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep
            (fn-bp-journal-nth 1 (fn-bprl-apply-journal-record s r))))
  :hints (("Goal"
           :cases ((fn-bprl-release-recordp r)
                   (fn-bprl-undertake-recordp r))
           :in-theory (disable fn-bp-statep fn-bp-journal-nth
                               fn-bprl-apply-journal-record
                               fn-bprl-release-recordp
                               fn-bprl-undertake-recordp))))

(defthm fn-bprl-durable-fold-preserves-state
  (implies (fn-bp-statep s)
           (fn-bp-statep (fn-bprl-durable-fold s records)))
  :hints (("Goal" :induct (fn-bprl-durable-fold s records)
           :in-theory (e/d (fn-bprl-durable-fold)
                           (fn-bp-statep fn-bprl-apply-journal-record
                            fn-bp-journal-nth)))))

(local
 (defthm fn-bprl-restart-event-state
   (equal (fn-bp-result-state (fn-bp-step s (fn-bp-restart-event)))
          (fn-bp-restart s))
   :hints (("Goal" :in-theory
            (enable fn-bp-step fn-bp-restart-event fn-bp-event-kind
                    fn-bp-make-result fn-bp-result-state fn-bp-nth)))))

(local
 (defthm fn-bprl-restart-constant-state
   (equal (car (fn-bp-step s '(:restart))) (fn-bp-restart s))
   :hints (("Goal" :in-theory
            (enable fn-bp-step fn-bp-event-kind fn-bp-make-result
                    fn-bp-result-state fn-bp-nth)))))

(defthm fn-bprl-replay-records-state-is-restarted-fold
  (implies (car (fn-bprl-replay-records s records effects))
           (equal (fn-bp-journal-nth 1
                    (fn-bprl-replay-records s records effects))
                  (fn-bp-restart (fn-bprl-durable-fold s records))))
  :hints (("Goal" :induct (fn-bprl-replay-records s records effects)
           :in-theory (e/d (fn-bprl-replay-records fn-bprl-durable-fold)
                           (fn-bprl-apply-journal-record fn-bp-step
                            fn-bp-statep fn-bp-restart
                            fn-bp-configp fn-bp-workp
                            fn-bp-attemptp fn-bp-receiptp
                            fn-bp-pendingp)))))

; Host/workflow-host.lisp fn-workflow-install-replay calls this exact replay
; function.  On a successful replay, its installed work status equals the
; status of the durable ACL2 record fold after exactly one restart marking.
(local
 (defthm fn-bprl-replay-journal-ok-implies-initial-statep
   (implies (car (fn-bprl-replay-journal node records))
            (fn-bp-statep
             (fn-bp-initial-state
              node (fn-bp-config-from-record (car records)))))
   :hints (("Goal" :in-theory
            (e/d (fn-bprl-replay-journal)
                 (fn-bp-statep fn-bp-initial-state
                  fn-bp-config-recordp fn-bprl-replay-records
                  fn-bp-config-from-record))))))

(local
 (defthm fn-bprl-replay-journal-state-is-restarted-fold
   (implies (car (fn-bprl-replay-journal node records))
            (equal
             (fn-bp-journal-nth 1 (fn-bprl-replay-journal node records))
             (fn-bp-restart
              (fn-bprl-durable-fold
               (fn-bp-initial-state
                node (fn-bp-config-from-record (car records)))
               (cdr records)))))
   :hints (("Goal"
            :use ((:instance fn-bprl-replay-records-state-is-restarted-fold
                             (s (fn-bp-initial-state
                                 node (fn-bp-config-from-record (car records))))
                             (records (cdr records)) (effects nil)))
            :in-theory
            (e/d (fn-bprl-replay-journal)
                 (fn-bprl-replay-records fn-bprl-durable-fold
                  fn-bp-restart fn-bp-statep fn-bp-initial-state
                  fn-bp-config-recordp fn-bp-config-from-record))))))

(defthm fn-bprl-replay-work-status-is-durable-status-restarted
  (implies (car (fn-bprl-replay-journal node records))
           (equal
            (fn-bp-work-status
             id (fn-bp-state-works
                 (fn-bp-journal-nth 1
                  (fn-bprl-replay-journal node records))))
            (fn-bp-work-status-after-restart
             (fn-bp-work-status
              id (fn-bp-state-works
                  (fn-bprl-durable-fold
                   (fn-bp-initial-state
                    node (fn-bp-config-from-record (car records)))
                   (cdr records)))))))
  :hints (("Goal"
           :use ((:instance fn-bp-work-status-of-restart
                            (s (fn-bprl-durable-fold
                                (fn-bp-initial-state
                                 node (fn-bp-config-from-record (car records)))
                                (cdr records))))
                 (:instance fn-bprl-replay-journal-ok-implies-initial-statep)
                 (:instance fn-bprl-replay-journal-state-is-restarted-fold)
                 (:instance fn-bprl-durable-fold-preserves-state
                            (s (fn-bp-initial-state
                                node (fn-bp-config-from-record (car records))))
                            (records (cdr records)))
                 )
           :in-theory
           (disable fn-bprl-replay-journal fn-bprl-durable-fold
                    fn-bprl-replay-records fn-bp-restart
                    fn-bp-initial-state fn-bp-statep fn-bp-state-works
                    fn-bp-journal-nth fn-bp-work-status
                    fn-bp-work-status-after-restart
                    fn-bp-work-status-of-restart
                    fn-bprl-durable-fold-preserves-state))))

(in-theory (disable fn-bprl-durable-fold))
