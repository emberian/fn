; Teeth of books/bp-node-rotation-due (lane bp-rotation): the natural
; rotation a node verb's open drives (host/native/bp-node.lisp
; fnn-bps-rotate-when-due calls fn-bpnrd-due-rotation-event).
;
; The fixture is N16's (tests/acl2/bp-node-counterexamples-tests): the raw
; initial state, the real kind-5 row of bundle A (bpcx-n16-rows0), no
; selection file.  The host appends ACL2's clock-domain decision to the
; recovery event it drives; the state below is fn-bpnp-step's answer to
; that event.  Values that write or read a checkpoint file are zero-argument
; functions (the digest's attachment is ignored while a defconst evaluates).
(in-package "ACL2")
(include-book "bp-node-counterexamples-tests")
(include-book "../../books/bp-node-rotation-due")
(include-book "must-fail-checked")
(include-book "../../books/defkeystone")
(include-book "../../books/bp-node-job-offer")

;; Profile 3 with a threshold of one record, and with two.
(defconst *bprd-profile-1* '(8 1048576 65538 1048576 1))
(defconst *bprd-profile-2* '(8 1048576 65538 1048576 2))

(defun bprd-event ()
  (append (bpcx-n16-full0) (list '(:same (7 7 7 7)))))
(defun bprd-answer () (fn-bpnp-step *bpcx-raw-s0* (bprd-event)))
(defun bprd-st () (fn-bpnf-answer-state (bprd-answer)))
(defun bprd-rot (st profile)
  (fn-bpnrd-due-rotation-event st profile 0 '("lifecycle") (bprd-event)))
(defun bprd-eff (st profile)
  (car (fn-bpnf-answer-effects
        (fn-bpnp-rotate-step st (fn-bpn-nth 1 (bprd-rot st profile))
                             (fn-bpn-nth 2 (bprd-rot st profile))))))
(defun bprd-budget (st)
  (fn-bpnr-depth-budget (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))
(defun bprd-reopen (st profile suffix)
  (fn-bpnr-recover-auto-event
   *bpcx-raw-s0* nil :ready suffix
   (fn-bpnr-selection-plan
    t (fn-bpnr-checkpoint-octets (fn-bpn-nth 4 (bprd-eff st profile))
                                 (bprd-budget st))
    (bprd-budget st))))
(defun bprd-expected-empty ()
  (list :recover-fnbs 3 nil :ready
        (update-nth 3 '(2 . 0) (fn-bpn-nth 4 (bpcx-n16-full0))) 0))
(defun bprd-expected-later (suffix)
  (update-nth 5 (len suffix)
              (fn-bpnr-recover-auto-event
               *bpcx-raw-s0* nil :ready (append (bpcx-n16-rows0) suffix)
               '(:none))))

;; The recovery the open drives is ready, holds bundle A, and leaves a
;; quiescent state at the event's epoch with one record in the generation.
(assert-event
 (and (equal (car (car (fn-bpnf-answer-effects (bprd-answer)))) :restart-ready)
      (equal (fn-bpnf-epoch (bprd-st)) 2)
      (equal (fn-bpn-nth 1 (bpcx-n16-full0)) 2)
      (equal (fn-bpnp-used (bprd-st)) 1)
      (fn-bpnp-rotation-quiescentp (bprd-st))
      (equal (len (fn-bpnf-held-list (bprd-st))) 1)))

;; fn-bpnrd-due-rotation-event-by-definition.  Witness: threshold 1 is
;; reached (1 record), and the event is `bp-node checkpoint''s: generation
;; 1 over "lifecycle", the checkpoint of the recovery event.
(assert-event
 (equal (bprd-rot (bprd-st) *bprd-profile-1*)
        (list :rotate 1 (fn-bpnr-checkpoint-of-event (bprd-event) 1 (bprd-st)))))
;; Threshold 2 is not reached: no rotation.
(assert-event (null (bprd-rot (bprd-st) *bprd-profile-2*)))
;; Not quiescent (the rotation's own publication issued): no rotation.
(assert-event
 (null (bprd-rot (fn-bpnf-answer-state
                  (fn-bpnp-rotate-step (bprd-st) 1
                                       (fn-bpnr-checkpoint-of-event
                                        (bprd-event) 1 (bprd-st))))
                 *bprd-profile-1*)))
;; A profile that is not profile 3 (the four-field profile 2): no rotation.
(assert-event (null (bprd-rot (bprd-st) '(8 1048576 65538 1048576))))

;; fn-bpnrd-due-rotation-preserves-recovery.  Reachable witness, the whole
;; antecedent and both conclusions: the machine proposes the publication,
;; and the published file reopens to full recovery, with no later rows and
;; with row B (written at (3 . 0), after the rotation's (2 . 0)).
(assert-event
 (and (equal (car (bprd-eff (bprd-st) *bprd-profile-1*)) :persist-checkpoint)
      (equal (fn-bpnf-epoch (bprd-st)) (fn-bpn-nth 1 (bpcx-n16-full0)))
      (true-listp (bpcx-n16-rows0))
      (equal (car (fn-bpnr-replay-from nil (bpcx-n16-rows0)
                                       (fn-bpnf-base *bpcx-raw-s0*)))
             :ready)
      (fn-bpnr-rows-start-after nil '(2 . 0))
      (fn-bpnr-rows-start-after (list (bpcx-n16-row-b)) '(2 . 0))
      (equal (bprd-reopen (bprd-st) *bprd-profile-1* nil)
             (bprd-expected-empty))
      (equal (car (fn-bpn-nth 4 (bprd-reopen (bprd-st) *bprd-profile-1*
                                             (list (bpcx-n16-row-b)))))
             :ready)
      (equal (bprd-reopen (bprd-st) *bprd-profile-1* (list (bpcx-n16-row-b)))
             (bprd-expected-later (list (bpcx-n16-row-b))))))

;; Hypothesis "later rows start after (E . 0)" (reachable rows): row B2 at
;; the rotation's own id (2 . 0) is refused from the published checkpoint,
;; while full recovery over the old rows takes it.  Every other hypothesis
;; holds (the witness above).
(assert-event
 (not (fn-bpnr-rows-start-after (list (bpcx-n16-row-b2)) '(2 . 0))))
(must-fail-checked
 (assert-event
  (equal (bprd-reopen (bprd-st) *bprd-profile-1* (list (bpcx-n16-row-b2)))
         (bprd-expected-later (list (bpcx-n16-row-b2))))))

;; CORRUPTED-STATE witness, hypothesis "the machine proposes the
;; publication": a state whose held list is not the recovery's (held rows
;; dropped, index 2 of the foundation state, fn-bpnf-held-list) still has the record count
;; and quiescence, so the rotation is due; the machine refuses the
;; checkpoint, which is not its own projection, and nothing that reopens
;; is the full recovery.
(defun bprd-st-no-held () (update-nth 2 nil (bprd-st)))
(assert-event
 (and (null (fn-bpnf-held-list (bprd-st-no-held)))
      (bprd-rot (bprd-st-no-held) *bprd-profile-1*)
      (equal (fn-bpnf-epoch (bprd-st-no-held)) 2)
      (equal (car (bprd-eff (bprd-st-no-held) *bprd-profile-1*))
             :rotation-refused)))
(must-fail-checked
 (assert-event
  (equal (bprd-reopen (bprd-st-no-held) *bprd-profile-1* nil)
         (bprd-expected-empty))))

;; CORRUPTED-STATE witness, hypothesis "the state is at the recovery
;; event's epoch": the same state at epoch 5 is due and the machine
;; proposes, but the checkpoint carries frontier (5 . 0), so the reopen
;; takes epoch 6 where full recovery names 3.
(defun bprd-st-epoch-5 () (update-nth 8 5 (bprd-st)))
(assert-event
 (and (equal (fn-bpnf-epoch (bprd-st-epoch-5)) 5)
      (equal (car (bprd-eff (bprd-st-epoch-5) *bprd-profile-1*))
             :persist-checkpoint)))
(must-fail-checked
 (assert-event
  (equal (bprd-reopen (bprd-st-epoch-5) *bprd-profile-1* nil)
         (bprd-expected-empty))))

;; Not separated, and not claimed as teeth: "rows0 is a true list", "plan0
;; is not damaged" and "the replay is ready".  A non-ready replay (an
;; improper row list faults it, as does a damaged plan) gives a checkpoint
;; whose held field is the fault's reason, which the machine's own
;; admission (fn-bpnr-checkpoint-of-statep inside fn-bpnp-rotate-step)
;; refuses, so no witness satisfies the publication hypothesis without
;; them; they are kept because fn-bpnr-recover-from-checkpoint-equals-full-
;; recover needs them.  Its own teeth (bp-node-counterexamples-tests)
;; separate them at the replay.

;; ---------------------------------------------------------------------------
;; Rotation inside a running serve (lane bp-retention-leftovers).

;; fn-bpnrd-serve-rotation-due-p.  Witness: the recovered state is at a safe
;; point (nothing issued, no pending image, no outbound session) and has
;; reached threshold 1.  Threshold 2: not due.  With the rotation's own
;; publication issued: not a safe point, not due.
(assert-event (fn-bpnrd-serve-rotation-due-p (bprd-st) *bprd-profile-1*))
(assert-event (not (fn-bpnrd-serve-rotation-due-p (bprd-st) *bprd-profile-2*)))
(assert-event
 (not (fn-bpnrd-serve-rotation-due-p
       (fn-bpnf-answer-state
        (fn-bpnp-rotate-step (bprd-st) 1
                             (fn-bpnr-checkpoint-of-event (bprd-event) 1 (bprd-st))))
       *bprd-profile-1*)))
;; An outbound session open: not a safe point.
(assert-event
 (not (fn-bpnrd-serve-rotation-due-p (update-nth 14 '((:peer 1)) (bprd-st))
                                     *bprd-profile-1*)))

;; KEYSTONE fn-bpnrd-rotation-keeps-every-held-family.  Reachable witness,
;; the antecedent and every conclusion: the machine proposes, and the
;; reopen from the published file with no rows is :ready with bundle A's
;; held row, the handoffs and the arrival frontier the machine held, at the
;; rotation's frontier (2 . 0).
(defun bprd-keeps-replay (st profile)
  (fn-bpn-nth 4 (bprd-reopen st profile nil)))
(assert-event
 (let ((replay (bprd-keeps-replay (bprd-st) *bprd-profile-1*)))
   (and (equal (car (bprd-eff (bprd-st) *bprd-profile-1*)) :persist-checkpoint)
        (equal (car replay) :ready)
        (consp (fn-bpnf-held-list (bprd-st)))
        (equal (fn-bpn-nth 1 replay) (fn-bpnf-held-list (bprd-st)))
        (equal (fn-bpn-nth 2 replay) (fn-bpnf-handoffs (bprd-st)))
        (equal (fn-bpn-nth 3 replay) '(2 . 0))
        (equal (fn-bpn-nth 4 replay) (fn-bpnf-next-arrival (bprd-st))))))
;; Tooth, hypothesis "the machine proposes the publication": the state whose
;; held rows were dropped (the machine refuses, its checkpoint is not its
;; own projection) has no published file, and the reopen is not :ready with
;; its held list.
(assert-event
 (equal (car (bprd-eff (bprd-st-no-held) *bprd-profile-1*)) :rotation-refused))
(must-fail-checked
 (assert-event
  (let ((replay (bprd-keeps-replay (bprd-st-no-held) *bprd-profile-1*)))
    (and (equal (car replay) :ready)
         (equal (fn-bpn-nth 1 replay) (fn-bpnf-held-list (bprd-st-no-held)))))))

;; ---------------------------------------------------------------------------
;; Critical durability witness: a composed execution, with no state splice.
;; Boot, receive A and acknowledge persistence, enqueue, acknowledge token 0,
;; contact the named job, acknowledge token 1, report an uncertain transfer,
;; and acknowledge the :requeued record at token 2.  The job status becomes
;; :queued again.  Reopen the emitted lifecycle records and received row:
;; this resets the operation frontier to the host open's rotation safe point.
(defun bprd-trace-fresh ()
  (fn-bpnf-initial-state *bpcx-config* 8 1048576))
(defun bprd-trace-boot ()
  (fn-bpnf-answer-state
   (fn-bpnj-step (bprd-trace-fresh)
    (fn-bpnr-recover-auto-event (bprd-trace-fresh) nil :ready nil '(:none)))))
(defun bprd-trace-receive ()
  (fn-bpnj-step (bprd-trace-boot) (bpcx-receive-event *bpcx-a-wire*)))
(defun bprd-trace-held ()
  (let* ((answer (bprd-trace-receive))
         (effect (car (fn-bpnf-answer-effects answer))))
    (fn-bpnf-answer-state
     (fn-bpnj-step (fn-bpnf-answer-state answer)
      (list :persist-result (nth 1 effect) (nth 2 effect) :durable)))))
(defun bprd-trace-enqueue ()
  (fn-bpnj-step (bprd-trace-held) (list :base *bpcx-enqueue*)))
(defun bprd-trace-queued ()
  (fn-bpnf-answer-state
   (fn-bpnj-step (fn-bpnf-answer-state (bprd-trace-enqueue))
                '(:base (:persist-result 0 :durable)))))
(defun bprd-trace-key ()
  (fn-bpn-job-key (car (fn-bpn-machine-state-jobs
                        (fn-bpnf-base (bprd-trace-queued))))))
(defun bprd-trace-attempt ()
  (fn-bpnj-step (bprd-trace-queued)
               (list :contact-job *bpcx-dest* (bprd-trace-key))))
(defun bprd-trace-attempting ()
  (fn-bpnf-answer-state
   (fn-bpnj-step (fn-bpnf-answer-state (bprd-trace-attempt))
                '(:base (:persist-result 1 :durable)))))
(defun bprd-trace-uncertain ()
  (fn-bpnj-step (bprd-trace-attempting)
               (list :job-result (bprd-trace-key) 1 :uncertain)))
(defun bprd-trace-requeued ()
  (fn-bpnf-answer-state
   (fn-bpnj-step (fn-bpnf-answer-state (bprd-trace-uncertain))
                '(:base (:persist-result 2 :durable)))))
(defun bprd-trace-records ()
  (list (third (car (fn-bpnf-answer-effects (bprd-trace-enqueue))))
        (third (car (fn-bpnf-answer-effects (bprd-trace-attempt))))
        (third (car (fn-bpnf-answer-effects (bprd-trace-uncertain))))))
(defun bprd-trace-rows () (list (bpcx-n16-row (bprd-trace-receive))))
(defun bprd-trace-reopen-event ()
  (fn-bpnr-recover-auto-event (bprd-trace-fresh) (bprd-trace-records)
                             :ready (bprd-trace-rows) '(:none)))
(defun bprd-traced-q ()
  (fn-bpnf-answer-state
   (fn-bpnj-step (bprd-trace-fresh) (bprd-trace-reopen-event))))
(defun bprd-traced-ck ()
  (fn-bpnr-checkpoint-of-event (bprd-trace-reopen-event) 1 (bprd-traced-q)))
(defun bprd-trace-rotate ()
  (fn-bpnj-step (bprd-traced-q) (list :rotate 1 (bprd-traced-ck))))

(defun bprd-trace-selected ()
  (fn-bpnj-step (fn-bpnf-answer-state (bprd-trace-rotate))
               (list :persist-result (fn-bpnf-epoch (bprd-traced-q)) 0 :durable)))
(assert-event
 (and (equal (len (fn-bpnf-held-list (bprd-trace-held))) 1)
      (equal (fn-bpn-job-status
              (car (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-trace-attempting)))))
             :attempting)
      (equal (car (nth 2 (bprd-trace-records))) :requeued)
      (equal (len (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-traced-q)))) 1)
      (equal (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-traced-q)))
             (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-trace-requeued))))
      (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (bprd-traced-q))) 3)
      (fn-bpn-machine-invariantp (fn-bpnf-base (bprd-traced-q)))
      (fn-bpnp-rotation-quiescentp (bprd-traced-q))
      (equal (car (car (fn-bpnf-answer-effects (bprd-trace-rotate)))) :persist-checkpoint)
      (equal (fn-bpnf-answer-effects (bprd-trace-selected)) '((:generation-selected 1)))
      (equal (fn-bpn-machine-state-jobs
              (fn-bpnf-base (fn-bpnf-answer-state (bprd-trace-selected))))
             (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-traced-q))))))

;; The original spliced fixture below remains an extra and supplies the
;; existing hypothesis-removal and statement-mutation witnesses.

;; Rotation of a state that owes jobs (lane bp-rotation-c5, item
;; BP-ROTATION-REFUSES-OWED-JOBS).  The fixture is N16's recovered state with
;; the base machine one durable enqueue further: one queued job, token
;; counter 1.  Before the checkpoint carried the base machine's jobs, this
;; state was not quiescent and the machine refused the rotation for it.
(defun bprd-owed-base ()
  (fn-bpn-answer-state
   (fn-bpn-step (fn-bpn-answer-state
                 (fn-bpn-step (fn-bpnf-base *bpcx-n16-q*) *bpcx-enqueue*))
                '(:persist-result 0 :durable))))
(defun bprd-owed-q () (update-nth 1 (bprd-owed-base) *bpcx-n16-q*))
(defun bprd-owed-ck ()
  (fn-bpnr-checkpoint-of-event *bpcx-n16-event* 1 (bprd-owed-q)))
(defun bprd-owed-eff (ck)
  (car (fn-bpnf-answer-effects (fn-bpnp-rotate-step (bprd-owed-q) 1 ck))))
(defun bprd-owed-plan ()
  (fn-bpnr-selection-plan
   t (fn-bpnr-checkpoint-octets (fn-bpn-nth 4 (bprd-owed-eff (bprd-owed-ck)))
                                (bprd-budget (bprd-owed-q)))
   (bprd-budget (bprd-owed-q))))
(defun bprd-owed-seed ()
  (fn-bpnr-replay-base (fn-bpnr-plan-checkpoint (bprd-owed-plan))
                       (fn-bpnf-base *bpcx-raw-s0*)))

;; The state owes exactly one queued job and a nonzero token counter, and is
;; quiescent (S2: quiescence no longer asks for an empty queue).
(assert-event
 (and (equal (len (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-owed-q)))) 1)
      (equal (fn-bpn-job-status
              (car (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-owed-q)))))
             :queued)
      (equal (fn-bpn-machine-state-next-token (fn-bpnf-base (bprd-owed-q))) 1)
      (fn-bpnp-rotation-quiescentp (bprd-owed-q))))

;; S1.  The checkpoint of the owed state carries the jobs and the token, is
;; its own projection (S2), and the file the rotation publishes round-trips
;; them (fn-bpnr-checkpoint-decode-of-octets).
(assert-event
 (let* ((ck (bprd-owed-ck))
        (rck (fn-bpnr-rotation-checkpoint ck 2))
        (octets (fn-bpnr-checkpoint-octets rck (bprd-budget (bprd-owed-q)))))
   (and (equal (fn-bpnr-checkpoint-jobs ck)
               (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-owed-q))))
        (equal (fn-bpnr-checkpoint-next-token ck) 1)
        (fn-bpnr-checkpoint-of-statep ck (bprd-owed-q) 1)
        (consp octets)
        (equal (fn-bpnr-checkpoint-decode octets (bprd-budget (bprd-owed-q))) rck)
        (equal (fn-bpnr-checkpoint-jobs
                (fn-bpnr-checkpoint-decode octets (bprd-budget (bprd-owed-q))))
               (fn-bpnr-checkpoint-jobs ck)))))

;; S2 teeth.  A checkpoint whose jobs are NIL, or whose token counter is 0,
;; is not the owed state's projection, and the machine refuses it, so a
;; rotation that drops the owed job is refuted; the faithful one is proposed.
(assert-event
 (and (equal (car (bprd-owed-eff (bprd-owed-ck))) :persist-checkpoint)
      (not (fn-bpnr-checkpoint-of-statep (update-nth 7 nil (bprd-owed-ck))
                                         (bprd-owed-q) 1))
      (not (fn-bpnr-checkpoint-of-statep (update-nth 8 0 (bprd-owed-ck))
                                         (bprd-owed-q) 1))
      (equal (car (bprd-owed-eff (update-nth 7 nil (bprd-owed-ck))))
             :rotation-refused)
      (equal (car (bprd-owed-eff (update-nth 8 0 (bprd-owed-ck))))
             :rotation-refused)))
(must-fail-checked
 (assert-event
  (equal (car (bprd-owed-eff (update-nth 7 nil (bprd-owed-ck))))
         :persist-checkpoint)))

;; S3.  The replay from the published file is the replay it always was: the
;; reopen right after the owed state's rotation equals the reopen after the
;; same rotation with an empty queue.
(assert-event
 (equal (fn-bpnr-recover-auto-event *bpcx-raw-s0* nil :ready nil
                                    (bprd-owed-plan))
        (fn-bpnr-recover-auto-event *bpcx-raw-s0* nil :ready nil
                                    (bpcx-n16-plan))))

;; S4 witness.  The recovery's base machine owes the job and the token the
;; state held, while the base it started from owes nothing.
(assert-event
 (and (null (fn-bpn-machine-state-jobs (fn-bpnf-base *bpcx-raw-s0*)))
      (equal (fn-bpn-machine-state-jobs (bprd-owed-seed))
             (fn-bpn-machine-state-jobs (fn-bpnf-base (bprd-owed-q))))
      (consp (fn-bpn-machine-state-jobs (bprd-owed-seed)))
      (equal (fn-bpn-machine-state-next-token (bprd-owed-seed)) 1)))

(defteeth fn-bpnp-rotation-recovery-seeds-owed-jobs
  :claim (((proposes (equal (car (car (fn-bpnf-answer-effects (fn-bpnp-rotate-step st generation ck)))) :persist-checkpoint))
           (machine (fn-bpn-machine-statep base0)))
          (and (equal (fn-bpn-machine-state-jobs (fn-bpnr-replay-base (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan t (fn-bpnr-checkpoint-octets (fn-bpn-nth 4 (car (fn-bpnf-answer-effects (fn-bpnp-rotate-step st generation ck)))) (fn-bpnr-depth-budget (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))) (fn-bpnr-depth-budget (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))) base0))
                      (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
               (equal (fn-bpn-machine-state-next-token (fn-bpnr-replay-base (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan t (fn-bpnr-checkpoint-octets (fn-bpn-nth 4 (car (fn-bpnf-answer-effects (fn-bpnp-rotate-step st generation ck)))) (fn-bpnr-depth-budget (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))) (fn-bpnr-depth-budget (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))) base0))
                      (fn-bpn-machine-state-next-token (fn-bpnf-base st)))))
  :subject fn-bpnp-rotate-step
  :witness ((st (bprd-traced-q)) (generation 1) (ck (bprd-traced-ck))
            (base0 (fn-bpnf-base *bpcx-raw-s0*)))
  :breaks ((proposes ((st (bprd-owed-q)) (generation 1)
                      (ck (update-nth 7 nil (bprd-owed-ck)))
                      (base0 (fn-bpnf-base *bpcx-raw-s0*))))
           (machine ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck))
                     (base0 nil))))
  :mutations ((seeded-queue
               (:conclusion (equal (fn-bpn-machine-state-jobs (fn-bpnr-replay-base (fn-bpnr-plan-checkpoint (fn-bpnr-selection-plan t (fn-bpnr-checkpoint-octets (fn-bpn-nth 4 (car (fn-bpnf-answer-effects (fn-bpnp-rotate-step st generation ck)))) (fn-bpnr-depth-budget (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))) (fn-bpnr-depth-budget (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))) base0)) nil))
               ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck))
                (base0 (fn-bpnf-base *bpcx-raw-s0*)))
               :fault "a recovery that seeds an empty queue and loses the owed job")))

;; ---------------------------------------------------------------------------
;; Teeth of the rotation's restart (R1-R5, lane bp-rotation-c5, item
;; BP-ROTATION-RESTART-DROPS-CHECKPOINT-JOBS).  The fixture is the owed state
;; above: the recovered state after one durable enqueue (one queued job, token
;; 1), rotated at generation 1 and reopened from a fresh initial state.
(defun bprd-owed-fb () (fn-bpnf-base (bprd-owed-q)))
(defun bprd-owed-job () (car (fn-bpn-machine-state-jobs (bprd-owed-fb))))
(defun bprd-owed-seeded ()
  (fn-bpnr-seed-state *bpcx-raw-s0* (bprd-owed-plan)))
(defun bprd-owed-event ()
  (fn-bpnr-recover-auto-event (bprd-owed-seeded) nil :ready nil (bprd-owed-plan)))
;; The first lifecycle record of the reopened generation: the attempt a
;; contact would propose, named by the checkpoint's token counter.
(defun bprd-owed-r1 ()
  (third (car (fn-bpn-answer-effects
               (fn-bpn-step (bprd-owed-fb)
                            (list :contact (fn-bpn-job-peer (bprd-owed-job)) t))))))

;; S2.  The refusal direction: a checkpoint that drops the owed job (or the
;; token counter) is refused, whatever else it carries.
(defteeth fn-bpnp-rotate-step-refuses-checkpoint-dropping-owed-work
  :claim (((drops (or (not (equal (fn-bpnr-checkpoint-jobs ck)
                                  (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                      (not (equal (fn-bpnr-checkpoint-next-token ck)
                                  (fn-bpn-machine-state-next-token (fn-bpnf-base st)))))))
          (equal (car (car (fn-bpnf-answer-effects
                            (fn-bpnp-rotate-step st generation ck))))
                 :rotation-refused))
  :subject fn-bpnp-rotate-step
  :witness ((st (bprd-traced-q)) (generation 1)
            (ck (update-nth 7 nil (bprd-traced-ck))))
  :breaks ((drops ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck)))))
  :mutations ((proposes-the-dropping-rotation
               (:conclusion (equal (car (car (fn-bpnf-answer-effects
                                              (fn-bpnp-rotate-step st generation ck))))
                                   :persist-checkpoint))
               ((st (bprd-owed-q)) (generation 1)
                (ck (update-nth 7 nil (bprd-owed-ck))))
               :fault "a rotation that drops an owed job is proposed")))

;; S3.  The replay's base carries the checkpoint's jobs and token counter.
(defteeth fn-bpnr-replay-base-seeds-checkpoint
  :claim (((checkpoint (fn-bpnr-checkpointp ck))
           (machine (fn-bpn-machine-statep base)))
          (and (equal (fn-bpn-machine-state-jobs (fn-bpnr-replay-base ck base))
                      (fn-bpnr-checkpoint-jobs ck))
               (equal (fn-bpn-machine-state-next-token (fn-bpnr-replay-base ck base))
                      (fn-bpnr-checkpoint-next-token ck))))
  :witness ((ck (bprd-owed-ck)) (base (fn-bpnf-base *bpcx-raw-s0*)))
  :breaks ((checkpoint ((ck nil) (base (fn-bpnf-base *bpcx-raw-s0*))))
           (machine ((ck (bprd-owed-ck)) (base nil)) :logical "NIL is outside the guard domain of the machine-state accessors"))
  :mutations ((leaves-the-fresh-queue
               (:conclusion (equal (fn-bpn-machine-state-jobs (fn-bpnr-replay-base ck base)) nil))
               ((ck (bprd-owed-ck)) (base (fn-bpnf-base *bpcx-raw-s0*)))
               :fault "a replay base that keeps the fresh base's empty queue")))

;; R3.  A value with a damaged job list has a file no checkpoint decode takes.
(defteeth fn-bpnr-checkpoint-decode-of-damaged-jobs-is-nil
  :claim (((damaged (not (fn-bpn-job-listp (nth 7 x)))))
          (equal (fn-bpnr-checkpoint-decode (fn-bpnr-value-octets x budget) budget)
                 nil))
  :witness ((x (update-nth 7 '(not-a-job) (bprd-owed-ck)))
            (budget (bprd-budget (bprd-owed-q))))
  :breaks ((damaged ((x (bprd-owed-ck)) (budget (bprd-budget (bprd-owed-q))))))
  :mutations ((accepts-the-raw-value
               (:conclusion (equal (fn-bpnr-checkpoint-decode (fn-bpnr-value-octets x budget) budget)
                                   x))
               ((x (update-nth 7 '(not-a-job) (bprd-owed-ck)))
                (budget (bprd-budget (bprd-owed-q))))
               :fault "a decode that does not validate the job list and returns the raw value")))
;; The witness's file exists and its undamaged twin decodes: the nil above is
;; the decode's refusal, not an encoding that did not fit.
(assert-event
 (and (consp (fn-bpnr-value-octets (update-nth 7 '(not-a-job) (bprd-owed-ck))
                                   (bprd-budget (bprd-owed-q))))
      (equal (fn-bpnr-checkpoint-decode
              (fn-bpnr-value-octets (bprd-owed-ck) (bprd-budget (bprd-owed-q)))
              (bprd-budget (bprd-owed-q)))
             (bprd-owed-ck))))

(defun bprd-two-fb ()
  ;; two owed jobs: a second durable enqueue on top of the owed machine
  (fn-bpn-answer-state
   (fn-bpn-step
    (fn-bpn-answer-state
     (fn-bpn-step (bprd-owed-fb)
                  (list :enqueue '(120) '(97) 0 10 *bpcx-route* *bpcx-dest*
                        '(5 6 7) *bpcx-obs*)))
    '(:persist-result 1 :durable))))
(defun bprd-two-q () (update-nth 1 (bprd-two-fb) *bpcx-n16-q*))
(defun bprd-two-ck () (fn-bpnr-checkpoint-of-event *bpcx-n16-event* 1 (bprd-two-q)))

;; Fixtures for the breaks below.
(defun bprd-over-fb ()
  ;; the owed machine under a max-jobs it exceeds: not a machine state
  (fn-bpn-make-machine-state (fn-bpn-machine-state-config (bprd-owed-fb))
                             (fn-bpn-machine-state-jobs (bprd-owed-fb))
                             nil nil nil 1 0
                             (fn-bpn-machine-state-max-octets (bprd-owed-fb))))
(defun bprd-token-fb (token)
  (fn-bpn-state-with (bprd-owed-fb) (fn-bpn-machine-state-jobs (bprd-owed-fb))
                     (fn-bpn-machine-state-contacts (bprd-owed-fb)) nil nil token))
(defun bprd-fresh-with-limits (max-jobs max-octets)
  (update-nth 1 (fn-bpn-make-machine-state
                 (fn-bpn-machine-state-config (fn-bpnf-base *bpcx-raw-s0*))
                 nil nil nil nil 0 max-jobs max-octets)
              *bpcx-raw-s0*))
(defun bprd-fresh-not-a-machine ()
  ;; limits as the profile's, a token counter that is no u64: not a machine state
  (update-nth 1 (fn-bpn-make-machine-state
                 (fn-bpn-machine-state-config (fn-bpnf-base *bpcx-raw-s0*))
                 nil nil nil nil -1 8 1048576)
              *bpcx-raw-s0*))
(defun bprd-fresh-pending ()
  ;; the fresh machine with an enqueue proposed and not yet durable
  (update-nth 1 (fn-bpn-answer-state
                 (fn-bpn-step (fn-bpnf-base *bpcx-raw-s0*) *bpcx-enqueue*))
              *bpcx-raw-s0*))
(defun bprd-empty-fb ()
  ;; the owed machine with its queue gone: a record about its job has no job
  (fn-bpn-state-with (bprd-owed-fb) nil (fn-bpn-machine-state-contacts (bprd-owed-fb))
                     nil nil 1))
(defun bprd-token-q (token)
  (update-nth 1 (bprd-token-fb token) (bprd-owed-q)))

;; R1.  A restart over no records from a seed answers the seed's jobs and
;; token counter.
(defteeth fn-bpn-restart-step-from-of-no-records
  :claim (((fits (fn-bpn-machine-statep
                  (fn-bpn-seeded-machine-state (fn-bpn-machine-state-config st)
                                               (fn-bpn-machine-state-max-jobs st)
                                               (fn-bpn-machine-state-max-octets st)
                                               jobs token)))
           (bound (<= token *fn-bpn-machine-max-records*)))
          (and (equal (fn-bpn-machine-state-jobs
                       (fn-bpn-answer-state
                        (fn-bpn-restart-step-from st nil :ready jobs token)))
                      jobs)
               (equal (fn-bpn-machine-state-next-token
                       (fn-bpn-answer-state
                        (fn-bpn-restart-step-from st nil :ready jobs token)))
                      token)))
  :witness ((st (bprd-owed-fb)) (jobs (fn-bpn-machine-state-jobs (bprd-owed-fb)))
            (token 1))
  :breaks ((fits ((st (bprd-owed-fb)) (jobs '(not-a-job)) (token 1)))
           (bound ((st (bprd-owed-fb)) (jobs (fn-bpn-machine-state-jobs (bprd-owed-fb)))
                   (token 5000))))
  :mutations ((restarts-from-the-initial-machine
               (:conclusion (equal (fn-bpn-machine-state-jobs
                                    (fn-bpn-answer-state
                                     (fn-bpn-restart-step-from st nil :ready jobs token)))
                                   nil))
               ((st (bprd-owed-fb)) (jobs (fn-bpn-machine-state-jobs (bprd-owed-fb)))
                (token 1))
               :fault "a restart that replays over the initial machine and loses the seed")))

;; R2.  The namespace recovery and the replay agree from any START: the
;; reopened generation's first record is named by the checkpoint's token.
(defteeth fn-bpn-host-lifecycle-recovery-from-agrees-with-the-replayed-machine
  :claim (((invariant (fn-bpn-machine-invariantp base))
           (frontier (equal (fn-bpn-machine-state-next-token base) start))
           (recovered (equal (car (fn-bpn-lifecycle-recovery-from names records start))
                             :ready))
           (replayed (equal (car (fn-bpn-replay-records base records)) :ready)))
          (and (equal (fn-bpn-host-lifecycle-recovery-agrees-p
                       (fn-bpn-lifecycle-recovery-from names records start)
                       (nth 1 (fn-bpn-replay-records base records)))
                      t)
               (equal (fn-bpn-lifecycle-recovery-next-token
                       (fn-bpn-lifecycle-recovery-from names records start))
                      (+ start (len records)))
               (equal (fn-bpn-machine-state-next-token
                       (nth 1 (fn-bpn-replay-records base records)))
                      (+ start (len records)))))
  :witness ((base (bprd-owed-fb)) (start 1)
            (names (list (fn-bpn-lifecycle-record-name 1)))
            (records (list (bprd-owed-r1))))
  :breaks ((invariant ((base (bprd-over-fb)) (start 1)
                       (names (list (fn-bpn-lifecycle-record-name 1)))
                       (records (list (bprd-owed-r1))))
                      :logical "a machine under a max-jobs it exceeds is outside the guard domain of the replay")
           (frontier ((base (bprd-token-fb 2)) (start 1) (names nil) (records nil)))
           (recovered ((base (bprd-owed-fb)) (start 1)
                       (names (list (fn-bpn-lifecycle-record-name 2)))
                       (records (list (bprd-owed-r1)))))
           (replayed ((base (bprd-empty-fb)) (start 1)
                      (names (list (fn-bpn-lifecycle-record-name 1)))
                      (records (list (bprd-owed-r1))))))
  :mutations ((frontier-forgets-the-records
               (:conclusion (equal (fn-bpn-lifecycle-recovery-next-token
                                    (fn-bpn-lifecycle-recovery-from names records start))
                                   start))
               ((base (bprd-owed-fb)) (start 1)
                (names (list (fn-bpn-lifecycle-record-name 1)))
                (records (list (bprd-owed-r1))))
               :fault "a namespace frontier that does not count the records after START")))

;; R4.  The foundation's recovery step restarts the base from its own jobs
;; and token counter.
(defteeth fn-bpnf-recover-fnbs-step-of-no-base-records-keeps-owed-work
  :claim (((machine (fn-bpn-machine-statep (fn-bpnf-base st))))
          (and (equal (fn-bpn-machine-state-jobs
                       (fn-bpnf-base
                        (fn-bpnf-answer-state
                         (fn-bpnf-recover-fnbs-step st new-epoch nil :ready replay))))
                      (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
               (equal (fn-bpn-machine-state-next-token
                       (fn-bpnf-base
                        (fn-bpnf-answer-state
                         (fn-bpnf-recover-fnbs-step st new-epoch nil :ready replay))))
                      (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
               (fn-bpn-machine-statep
                (fn-bpnf-base
                 (fn-bpnf-answer-state
                  (fn-bpnf-recover-fnbs-step st new-epoch nil :ready replay))))))
  :witness ((st (bprd-owed-seeded)) (new-epoch (fn-bpn-nth 1 (bprd-owed-event)))
            (replay (fn-bpn-nth 4 (bprd-owed-event))))
  :breaks ((machine ((st (update-nth 1 nil (bprd-owed-seeded)))
                     (new-epoch (fn-bpn-nth 1 (bprd-owed-event)))
                     (replay (fn-bpn-nth 4 (bprd-owed-event))))
                    :logical "a state with no base machine is outside the guard domain of the recovery step"))
  :mutations ((restarts-the-initial-machine
               (:conclusion (equal (fn-bpn-machine-state-jobs
                                    (fn-bpnf-base
                                     (fn-bpnf-answer-state
                                      (fn-bpnf-recover-fnbs-step st new-epoch nil :ready replay))))
                                   nil))
               ((st (bprd-owed-seeded)) (new-epoch (fn-bpn-nth 1 (bprd-owed-event)))
                (replay (fn-bpn-nth 4 (bprd-owed-event))))
               :fault "a recovery step that restarts the base from the initial machine and loses the owed job")))

;; R5 (KEYSTONE).  Rotate, then restart: the reopened base keeps the owed
;; work.  The mutation reopens unseeded.
(defteeth fn-bpnp-rotation-restart-keeps-owed-work
  :claim (((proposes (equal (car (car (fn-bpnf-answer-effects
                          (fn-bpnp-rotate-step st generation ck))))
               :persist-checkpoint))
           (invariant (fn-bpn-machine-invariantp (fn-bpnf-base st)))
           (fresh-machine (fn-bpn-machine-statep (fn-bpnf-base fresh)))
           (fresh-no-pending (null (fn-bpn-machine-state-pending (fn-bpnf-base fresh))))
           (same-max-jobs (equal (fn-bpn-machine-state-max-jobs (fn-bpnf-base fresh))
               (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))
           (same-max-octets (equal (fn-bpn-machine-state-max-octets (fn-bpnf-base fresh))
               (fn-bpn-machine-state-max-octets (fn-bpnf-base st)))))
          (let* ((plan (fn-bpnr-selection-plan
                 t
                 (fn-bpnr-checkpoint-octets
                  (fn-bpn-nth 4 (car (fn-bpnf-answer-effects
                                      (fn-bpnp-rotate-step st generation ck))))
                  (fn-bpnr-depth-budget
                   (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))
                 (fn-bpnr-depth-budget
                  (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))))
          (seeded (fn-bpnr-seed-state fresh plan))
          (event (fn-bpnr-recover-auto-event seeded nil :ready nil plan))
          (answer (fn-bpnf-recover-fnbs-step
                   seeded (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                   (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))))
     (and (not (null seeded))
          (equal (fn-bpn-machine-state-jobs
                  (fn-bpnf-base (fn-bpnf-answer-state answer)))
                 (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
          (equal (fn-bpn-machine-state-next-token
                  (fn-bpnf-base (fn-bpnf-answer-state answer)))
                 (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
          (equal (fn-bpn-host-lifecycle-recovery-agrees-p
                  (fn-bpn-lifecycle-recovery-from
                   nil nil (fn-bpnr-plan-start-token plan))
                  (fn-bpnf-base (fn-bpnf-answer-state answer)))
                 t))))
  :subject fn-bpnr-seed-state
  :witness ((st (bprd-traced-q)) (generation 1) (ck (bprd-traced-ck))
            (fresh *bpcx-raw-s0*))
  :breaks ((proposes ((st (bprd-owed-q)) (generation 1)
                      (ck (update-nth 7 nil (bprd-owed-ck))) (fresh *bpcx-raw-s0*)))
           (invariant ((st (bprd-token-q 5000)) (generation 1)
                       (ck (update-nth 8 5000 (bprd-owed-ck))) (fresh *bpcx-raw-s0*)))
           (fresh-machine ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck))
                           (fresh (bprd-fresh-not-a-machine)))
                          :logical "a base machine that is not a machine state is outside the guard domain of the recovery")
           (fresh-no-pending ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck))
                              (fresh (bprd-fresh-pending)))
                             :logical "no seeded state exists to feed the recovery step's guard")
           (same-max-jobs ((st (bprd-two-q)) (generation 1) (ck (bprd-two-ck))
                           (fresh (bprd-fresh-with-limits 1 1048576)))
                          :logical "no seeded state exists to feed the recovery step's guard")
           (same-max-octets ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck))
                             (fresh (bprd-fresh-with-limits 8 1)))
                            :logical "no seeded state exists to feed the recovery step's guard"))
  :mutations ((reopens-unseeded
               (:conclusion (let* ((plan (fn-bpnr-selection-plan
                 t
                 (fn-bpnr-checkpoint-octets
                  (fn-bpn-nth 4 (car (fn-bpnf-answer-effects
                                      (fn-bpnp-rotate-step st generation ck))))
                  (fn-bpnr-depth-budget
                   (fn-bpn-machine-state-max-jobs (fn-bpnf-base st))))
                 (fn-bpnr-depth-budget
                  (fn-bpn-machine-state-max-jobs (fn-bpnf-base st)))))
          (seeded fresh)
          (event (fn-bpnr-recover-auto-event seeded nil :ready nil plan))
          (answer (fn-bpnf-recover-fnbs-step
                   seeded (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                   (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))))
     (and (not (null seeded))
          (equal (fn-bpn-machine-state-jobs
                  (fn-bpnf-base (fn-bpnf-answer-state answer)))
                 (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
          (equal (fn-bpn-machine-state-next-token
                  (fn-bpnf-base (fn-bpnf-answer-state answer)))
                 (fn-bpn-machine-state-next-token (fn-bpnf-base st)))
          (equal (fn-bpn-host-lifecycle-recovery-agrees-p
                  (fn-bpn-lifecycle-recovery-from
                   nil nil (fn-bpnr-plan-start-token plan))
                  (fn-bpnf-base (fn-bpnf-answer-state answer)))
                 t))))
               ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck))
                (fresh *bpcx-raw-s0*))
               :fault "a reopen that restarts from the fresh machine instead of the checkpoint's seed (jobs lost)")))
