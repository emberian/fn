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
  :witness ((st (bprd-owed-q)) (generation 1) (ck (bprd-owed-ck))
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
