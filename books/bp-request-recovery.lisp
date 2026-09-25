; Recovery of a fenced workflow attempt, live and at replay.
;
; `bp-obligation recover STORE WORKFLOW WORK ATTEMPT OUTCOME'
; (host/native/bp-obligation.lisp fnn-command-bpo-owner-recover) calls
; fn-bprq-recovery-plan through host/workflow-host.lisp's
; fn-workflow-recovery-plan on the image the journal's open installed
; (fn-bpiw-replay-journal, fn-workflow-install-replay), publishes the plan's
; record, and applies it with fn-bpiw-apply (fn-workflow-apply-record).
(in-package "ACL2")
(include-book "bp-request-plan")
(include-book "bp-ion-workflow-replay")

(local
 (defthm fn-bprq-bpiw-apply-of-recovery-outcome
   (implies (fn-bpiw-recovery-outcomep r)
            (equal (fn-bpiw-apply bp ion r)
                   (let ((a (fn-bp-apply-journal-record bp r)))
                     (list (car a) (nth 1 a) (nth 2 a) ion))))
   :hints (("Goal" :in-theory (e/d (fn-bpiw-apply fn-bprl-apply-journal-record
                                    fn-bprl-release-recordp
                                    fn-bprl-undertake-recordp
                                    fn-bpiw-recovery-outcomep fn-bp-journal-nth)
                                   (fn-bp-apply-journal-record))))))

(local
 (defthm fn-bprq-bpiw-apply-parts-of-recovery-outcome
   (implies (fn-bpiw-recovery-outcomep r)
            (and (equal (car (fn-bpiw-apply bp ion r))
                        (car (fn-bp-apply-journal-record bp r)))
                 (equal (nth 1 (fn-bpiw-apply bp ion r))
                        (nth 1 (fn-bp-apply-journal-record bp r)))
                 (equal (nth 3 (fn-bpiw-apply bp ion r)) ion)))
   :hints (("Goal" :in-theory (disable fn-bpiw-apply
                                       fn-bp-apply-journal-record)))))

(local
 (defthm fn-bprq-bprl-apply-of-recovery-outcome
   (implies (fn-bpiw-recovery-outcomep r)
            (equal (fn-bprl-apply-journal-record bp r)
                   (fn-bp-apply-journal-record bp r)))
   :hints (("Goal" :in-theory (e/d (fn-bprl-apply-journal-record
                                    fn-bprl-release-recordp
                                    fn-bprl-undertake-recordp
                                    fn-bpiw-recovery-outcomep fn-bp-journal-nth)
                                   (fn-bp-apply-journal-record))))))

; A recovery plan's record is a recovery outcome the image accepts.
(local
 (defthm fn-bprq-recovery-plan-record-is-accepted
   (implies (equal (car (fn-bprq-recovery-plan s work-id attempt-id outcome))
                   :recover)
            (let ((r (nth 1 (fn-bprq-recovery-plan s work-id attempt-id
                                                   outcome))))
              (and (fn-bpiw-recovery-outcomep r)
                   (equal r (fn-bprq-recovery-record s outcome))
                   (car (fn-bp-apply-journal-record s r)))))
   :hints (("Goal" :in-theory (e/d (fn-bprq-recovery-plan
                                    fn-bprq-recovery-record
                                    fn-bpiw-recovery-outcomep
                                    fn-bp-journal-nth)
                                   (fn-bp-apply-journal-record
                                    fn-bprl-apply-journal-record
                                    fn-bprq-recovery-refusal
                                    fn-bp-journal-recordp))))))

; An accepted recovery outcome leaves no pending and no fence: fn-bp-recover
; either applies the pending (:committed) or drops it (:absent), and the
; step that changes nothing is the refused one.
(local
 (defthm fn-bprq-recover-changes-only-to-unfenced
   (let ((n (fn-bp-result-state (fn-bp-recover s txid generation result))))
     (or (equal n s)
         (and (null (fn-bp-state-pending n))
              (not (fn-bp-state-fenced n)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-bp-recover fn-bp-apply-pending
                                    fn-bp-make-result fn-bp-result-state)
                                   (fn-bp-statep fn-bp-pending-matchesp
                                    fn-bp-recovery-pending
                                    fn-bp-effect-for-pending))))))

(local
 (defthm fn-bprq-bp-nth-of-cons
   (equal (fn-bp-nth n (cons a b))
          (if (and (integerp n) (< 0 n)) (fn-bp-nth (1- n) b) a))
   :hints (("Goal" :expand ((fn-bp-nth n (cons a b)))))))

(local
 (defthm fn-bprq-apply-recovery-outcome-is-recover
   (implies (and (fn-bpiw-recovery-outcomep r)
                 (car (fn-bp-apply-journal-record s r)))
            (equal (nth 1 (fn-bp-apply-journal-record s r))
                   (fn-bp-result-state
                    (fn-bp-recover s (fn-bp-journal-nth 1 r)
                                   (fn-bp-journal-nth 2 r)
                                   (fn-bp-journal-nth 4 r)))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bp-apply-journal-record
                                 fn-bpiw-recovery-outcomep fn-bp-journal-nth
                                 fn-bp-step fn-bp-event-kind
                                 fn-bp-storage-recover-event
                                 fn-bprq-bp-nth-of-cons
                                 (:e integerp) (:e <) (:e binary-+)
                                 (:e unary--)
                                 car-cons cdr-cons nth-0-cons nth-add1)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bprq-accepted-apply-changes-the-image
   (implies (car (fn-bp-apply-journal-record s r))
            (not (equal (nth 1 (fn-bp-apply-journal-record s r)) s)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bp-apply-journal-record nth
                                 car-cons cdr-cons (:e zp) (:e binary-+)
                                 (:e unary--))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bprq-accepted-recovery-unfences
   (implies (and (fn-bpiw-recovery-outcomep r)
                 (car (fn-bp-apply-journal-record s r)))
            (let ((next (nth 1 (fn-bp-apply-journal-record s r))))
              (and (null (fn-bp-state-pending next))
                   (not (fn-bp-state-fenced next)))))
   :hints (("Goal"
            :use ((:instance fn-bprq-recover-changes-only-to-unfenced
                             (txid (fn-bp-journal-nth 1 r))
                             (generation (fn-bp-journal-nth 2 r))
                             (result (fn-bp-journal-nth 4 r)))
                  fn-bprq-accepted-apply-changes-the-image)
            :in-theory (union-theories
                        '(fn-bprq-apply-recovery-outcome-is-recover)
                        (theory 'minimal-theory))))))

; Keystone.  Subject: fn-bprq-recovery-plan, which `bp-obligation recover'
; calls (fn-workflow-recovery-plan) on the image the journal's open installed.
; When that open succeeded and the plan answers :recover, the plan's record
; is accepted live (fn-bpiw-apply, what fn-workflow-apply-record calls); the
; live image has no pending and no fence, so the journal is no longer
; refused for it; the journal with the record appended replays (the history
; gate admits what the live gate admitted); and the next open installs
; exactly the live image after its one restart, ION state unchanged.
(defthm fn-bprq-recovery-plan-unfences-and-reopens-as-live
  (let* ((open (fn-bpiw-replay-journal node records))
         (plan (fn-bprq-recovery-plan (nth 1 open) work-id attempt-id outcome))
         (r (nth 1 plan))
         (live (fn-bpiw-apply (nth 1 open) (nth 3 open) r))
         (reopen (fn-bpiw-replay-journal node (append records (list r)))))
    (implies (and (car open)
                  (equal (car plan) :recover))
             (and (car live)
                  (null (fn-bp-state-pending (nth 1 live)))
                  (not (fn-bp-state-fenced (nth 1 live)))
                  (car reopen)
                  (equal (nth 1 reopen) (fn-bp-restart (nth 1 live)))
                  (equal (nth 3 reopen) (nth 3 live)))))
  :hints (("Goal"
           :use ((:instance fn-bprq-recovery-plan-record-is-accepted
                            (s (nth 1 (fn-bpiw-replay-journal node records))))
                 (:instance fn-bprq-accepted-recovery-unfences
                            (s (nth 1 (fn-bpiw-replay-journal node records)))
                            (r (nth 1 (fn-bprq-recovery-plan
                                       (nth 1 (fn-bpiw-replay-journal
                                               node records))
                                       work-id attempt-id outcome))))
                 (:instance fn-bpiw-reopen-after-live-recovery-is-the-live-image-restarted
                            (r (nth 1 (fn-bprq-recovery-plan
                                       (nth 1 (fn-bpiw-replay-journal
                                               node records))
                                       work-id attempt-id outcome)))))
           :in-theory (union-theories
                       '(fn-bprq-bpiw-apply-parts-of-recovery-outcome)
                       (theory 'minimal-theory)))))
