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
(include-book "std/testing/must-fail" :dir :system)

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
        (list :rotate 1 (fn-bpnr-checkpoint-of-event (bprd-event) 1))))
;; Threshold 2 is not reached: no rotation.
(assert-event (null (bprd-rot (bprd-st) *bprd-profile-2*)))
;; Not quiescent (the rotation's own publication issued): no rotation.
(assert-event
 (null (bprd-rot (fn-bpnf-answer-state
                  (fn-bpnp-rotate-step (bprd-st) 1
                                       (fn-bpnr-checkpoint-of-event
                                        (bprd-event) 1)))
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
(must-fail
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
(must-fail
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
(must-fail
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
