; Replay of the ION workflow journal against the live path that wrote it.
;
; host/workflow-host.lisp opens a journal with fn-bpiw-replay-journal
; (fn-workflow-install-replay) and gates every later publication on the same
; function over the history with the new record appended
; (fn-workflow-preflight-history), then applies the record to the installed
; image with fn-bpiw-apply (fn-workflow-apply-record).  A recovery outcome is
; only ever accepted live after a reopen, whose :restart fenced the pending
; intent; the journal records no restart, so replay reconstructs the fence
; (fn-bpiw-replay-fence).  The keystone below says the two gates agree on
; such a record and that a later reopen installs exactly the live image after
; the one restart every reopen performs.
(in-package "ACL2")
(include-book "bp-ion-workflow")
(include-book "bp-workflow-invariants")

; The successful prefix of a replay, before its trailing restart: the flag,
; the BP image and the ION state.
(defun fn-bpiw-durable-fold (bp ion records)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count records)))
  (if (endp records)
      (list t bp ion)
    (let ((answer (fn-bpiw-apply (fn-bpiw-replay-fence bp (car records))
                                 ion (car records))))
      (if (car answer)
          (fn-bpiw-durable-fold (nth 1 answer) (nth 3 answer) (cdr records))
        (list nil bp ion)))))

; Restart marks an in-flight attempt :restart-observed, which is retryable,
; so a second restart changes nothing, and it keeps each work's id.
(local
 (defthm fn-bpiw-restart-work-idempotent
   (equal (fn-bp-restart-work (fn-bp-restart-work w))
          (fn-bp-restart-work w))
   :hints (("Goal" :in-theory (enable fn-bp-restart-work fn-bp-work-with-status
                                      fn-bp-work-with-attempt fn-bp-make-work
                                      fn-bp-make-attempt fn-bp-nth)))))

(local
 (defthm fn-bpiw-restart-works-idempotent
   (equal (fn-bp-restart-works (fn-bp-restart-works ws))
          (fn-bp-restart-works ws))
   :hints (("Goal" :in-theory (e/d (fn-bp-restart-works)
                                   (fn-bp-restart-work))))))

(local
 (defthm fn-bpiw-work-id-of-restart-work
   (equal (fn-bp-work-id (fn-bp-restart-work w)) (fn-bp-work-id w))
   :hints (("Goal" :in-theory (enable fn-bp-restart-work fn-bp-work-with-status
                                      fn-bp-work-with-attempt fn-bp-make-work
                                      fn-bp-nth)))))

(local
 (defthm fn-bpiw-restart-works-of-replace-work
   (equal (fn-bp-restart-works (fn-bp-replace-work w ws))
          (fn-bp-replace-work (fn-bp-restart-work w) (fn-bp-restart-works ws)))
   :hints (("Goal" :in-theory (e/d (fn-bp-restart-works fn-bp-replace-work)
                                   (fn-bp-restart-work fn-bp-work-id))))))

(local
 (defthm fn-bpiw-unfenced-image-is-not-a-fenced-state
   (implies (fn-bp-nth 5 s)
            (not (equal (list node config works receipts pending nil used) s)))
   :hints (("Goal" :in-theory (enable fn-bp-nth)))))

(local
 (defthm fn-bpiw-statep-fenced-is-boolean
   (implies (fn-bp-statep s) (booleanp (fn-bp-nth 5 s)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-bp-statep fn-bp-state-fenced)))))

(local
 (defthm fn-bpiw-fenced-recovery-restarts-as-live-on-a-state
   (implies (and (fn-bp-statep f)
                 (fn-bpiw-recovery-outcomep r)
                 (car (fn-bp-apply-journal-record (fn-bp-restart f) r)))
            (and (car (fn-bp-apply-journal-record (fn-bpiw-replay-fence f r) r))
                 (equal (fn-bp-restart
                         (nth 1 (fn-bp-apply-journal-record
                                 (fn-bpiw-replay-fence f r) r)))
                        (fn-bp-restart
                         (nth 1 (fn-bp-apply-journal-record
                                 (fn-bp-restart f) r))))))
   :hints (("Goal"
            :use ((:instance fn-bp-restart-preserves-state (s f))
                  (:instance fn-bp-step-preserves-state (s f)
                             (event (fn-bp-storage-complete-event
                                     (fn-bp-journal-nth 1 r)
                                     (fn-bp-journal-nth 2 r) :indeterminate)))
                  (:instance fn-bp-recover-preserves-state
                             (s (fn-bp-restart f))
                             (txid (fn-bp-journal-nth 1 r))
                             (generation (fn-bp-journal-nth 2 r))
                             (result (fn-bp-journal-nth 4 r)))
                  (:instance fn-bp-recover-preserves-state
                             (s (fn-bp-result-state
                                 (fn-bp-step f (fn-bp-storage-complete-event
                                                (fn-bp-journal-nth 1 r)
                                                (fn-bp-journal-nth 2 r)
                                                :indeterminate))))
                             (txid (fn-bp-journal-nth 1 r))
                             (generation (fn-bp-journal-nth 2 r))
                             (result (fn-bp-journal-nth 4 r))))
            :in-theory (e/d (fn-bp-apply-journal-record fn-bpiw-replay-fence
                             fn-bpiw-recovery-outcomep)
                            (fn-bp-statep fn-bp-journal-recordp
                             fn-bp-restart-preserves-state
                             fn-bp-step-preserves-state
                             fn-bp-recover-preserves-state))))))

; The BP step of the keystone.  A recovery outcome the live image accepts
; after a restart is accepted by replay after the reconstructed fence, and the
; two images agree once restarted: the fence and the restart differ only in
; the restart marking of the works, which the next restart applies anyway.
; No state hypothesis: a live acceptance already needs a matching pending in
; a well-formed image.
(defthm fn-bpiw-fenced-recovery-restarts-as-live
  (implies (and (fn-bpiw-recovery-outcomep r)
                (car (fn-bp-apply-journal-record (fn-bp-restart f) r)))
           (and (car (fn-bp-apply-journal-record (fn-bpiw-replay-fence f r) r))
                (equal (fn-bp-restart
                        (nth 1 (fn-bp-apply-journal-record
                                (fn-bpiw-replay-fence f r) r)))
                       (fn-bp-restart
                        (nth 1 (fn-bp-apply-journal-record
                                (fn-bp-restart f) r))))))
  :hints (("Goal" :cases ((fn-bp-statep f)))
          ("Subgoal 2"
           :in-theory (e/d (fn-bp-restart fn-bp-apply-journal-record fn-bp-step
                            fn-bp-recover fn-bp-pending-matchesp)
                           (fn-bp-statep fn-bp-journal-recordp)))
          ("Subgoal 1"
           :use fn-bpiw-fenced-recovery-restarts-as-live-on-a-state
           :in-theory (disable fn-bpiw-fenced-recovery-restarts-as-live-on-a-state
                               fn-bp-restart fn-bp-apply-journal-record
                               fn-bpiw-replay-fence fn-bpiw-recovery-outcomep
                               fn-bp-statep))))

(local
 (defthm fn-bpiw-restart-event-is-restart
   (equal (fn-bp-result-state (fn-bp-step s (fn-bp-restart-event)))
          (fn-bp-restart s))
   :hints (("Goal" :in-theory
            (enable fn-bp-step fn-bp-restart-event fn-bp-event-kind
                    fn-bp-make-result fn-bp-result-state fn-bp-nth)))))

(local
 (defthm fn-bpiw-restart-constant-is-restart
   (equal (car (fn-bp-step s '(:restart))) (fn-bp-restart s))
   :hints (("Goal" :in-theory
            (enable fn-bp-step fn-bp-event-kind fn-bp-make-result
                    fn-bp-result-state fn-bp-nth)))))

; A replay is its durable fold followed by exactly one restart.
(defthm fn-bpiw-replay-records-is-restarted-fold
  (and (equal (car (fn-bpiw-replay-records bp ion records effects))
              (car (fn-bpiw-durable-fold bp ion records)))
       (implies (car (fn-bpiw-durable-fold bp ion records))
                (and (equal (nth 1 (fn-bpiw-replay-records bp ion records effects))
                            (fn-bp-restart
                             (nth 1 (fn-bpiw-durable-fold bp ion records))))
                     (equal (nth 3 (fn-bpiw-replay-records bp ion records effects))
                            (nth 2 (fn-bpiw-durable-fold bp ion records))))))
  :hints (("Goal" :induct (fn-bpiw-replay-records bp ion records effects)
           :in-theory (e/d (fn-bpiw-replay-records fn-bpiw-durable-fold)
                           (fn-bpiw-apply fn-bpiw-replay-fence fn-bp-step
                            fn-bp-restart fn-bp-restart-event)))))

(defthm fn-bpiw-durable-fold-of-append-one
  (equal (fn-bpiw-durable-fold bp ion (append records (list r)))
         (let ((prefix (fn-bpiw-durable-fold bp ion records)))
           (if (car prefix)
               (let ((answer (fn-bpiw-apply
                              (fn-bpiw-replay-fence (nth 1 prefix) r)
                              (nth 2 prefix) r)))
                 (if (car answer)
                     (list t (nth 1 answer) (nth 3 answer))
                   (list nil (nth 1 prefix) (nth 2 prefix))))
             prefix)))
  :hints (("Goal" :induct (fn-bpiw-durable-fold bp ion records)
           :in-theory (e/d (fn-bpiw-durable-fold)
                           (fn-bpiw-apply fn-bpiw-replay-fence)))))

(local
 (defthm fn-bpiw-apply-of-recovery-outcome
   (implies (fn-bpiw-recovery-outcomep r)
            (equal (fn-bpiw-apply bp ion r)
                   (let ((a (fn-bp-apply-journal-record bp r)))
                     (list (car a) (nth 1 a) (nth 2 a) ion))))
   :hints (("Goal" :in-theory (e/d (fn-bpiw-apply fn-bprl-apply-journal-record
                                    fn-bprl-release-recordp
                                    fn-bprl-undertake-recordp
                                    fn-bpiw-recovery-outcomep fn-bp-journal-nth)
                                   (fn-bp-apply-journal-record))))))

; Keystone.  Subject: fn-bpiw-replay-journal, which host/workflow-host.lisp
; calls at open (fn-workflow-install-replay) and before every publication
; (fn-workflow-preflight-history); fn-bpiw-apply is what
; fn-workflow-apply-record calls on the installed image.  If a journal opens
; and the opened image accepts a recovery outcome live, then the journal with
; that outcome appended replays -- so the history gate admits the record the
; live gate admits -- and a later reopen installs the live image after one
; restart, with the ION route/observation state unchanged.
(defthm fn-bpiw-reopen-after-live-recovery-is-the-live-image-restarted
  (let* ((open (fn-bpiw-replay-journal node records))
         (live (fn-bpiw-apply (nth 1 open) (nth 3 open) r))
         (reopen (fn-bpiw-replay-journal node (append records (list r)))))
    (implies (and (car open)
                  (fn-bpiw-recovery-outcomep r)
                  (car live))
             (and (car reopen)
                  (equal (nth 1 reopen) (fn-bp-restart (nth 1 live)))
                  (equal (nth 3 reopen) (nth 3 live)))))
  :hints (("Goal"
           :use ((:instance fn-bpiw-fenced-recovery-restarts-as-live
                            (f (nth 1 (fn-bpiw-durable-fold
                                       (fn-bp-initial-state
                                        node (fn-bp-config-from-record
                                              (car records)))
                                       (fn-bpiw-initial) (cdr records))))))
           :in-theory (e/d (fn-bpiw-replay-journal)
                           (fn-bpiw-apply fn-bpiw-replay-records
                            fn-bpiw-durable-fold
                            fn-bp-apply-journal-record fn-bpiw-replay-fence
                            fn-bp-restart fn-bp-initial-state fn-bp-statep
                            fn-bp-config-recordp fn-bp-config-from-record
                            fn-bpiw-recovery-outcomep fn-bpiw-initial
                            fn-bpiw-fenced-recovery-restarts-as-live)))))

(in-theory (disable fn-bpiw-durable-fold))
