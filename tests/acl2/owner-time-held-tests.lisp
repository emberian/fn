; Ground run of the held commit over the owner's scheduler value
; (books/owner-time-held.lisp, ruling 19).
(in-package "ACL2")
(include-book "../../books/owner-time-held")
(include-book "../../books/defkeystone")

(defun oth-s (s e)
  (declare (xargs :guard t))
  (mv-let (a s2) (fn-otm-held-event s e) (declare (ignore a)) s2))
(defun oth-a (s e)
  (declare (xargs :guard t))
  (mv-let (a s2) (fn-otm-held-event s e) (declare (ignore s2)) a))
(defun oth-next (s w)
  (declare (xargs :guard t))
  (mv-let (c s2) (fn-otm-next s w) (declare (ignore c)) s2))

(defconst *oth-w0* '(0 0 0 0 0 0))

; Quantum 1: START captured a batch for a caller holding its submission.
(defconst *oth-s1* (oth-s (fn-otm-init) :started-held))
(assert-event (equal (oth-a (fn-otm-init) :started-held) :sync))
(assert-event (and (fn-otm-held *oth-s1*) (equal (fn-otm-phase-of *oth-s1*) :staged)))

; Between the quanta the gate's entries keep the slot, the committer waits
; (even with a returned sync and queued members) and the caller collects
; only once the sync returned.
(assert-event (fn-otm-held (oth-next *oth-s1* *oth-w0*)))
(assert-event (equal (fn-otm-held-committer-wake *oth-s1* t t *oth-w0*) :wait))
(assert-event (equal (fn-otm-held-caller-wake *oth-s1* nil) :wait))
(assert-event (equal (fn-otm-held-caller-wake *oth-s1* t) :collect))

; Teeth: the same value without the slot wakes the committer to collect.
(assert-event (equal (fn-otm-committer-wake *oth-s1* t t *oth-w0*) :collect))

; Quantum 2: fenced, COMPLETE, then the held submission; the slot clears.
(defconst *oth-s2* (oth-s *oth-s1* :fenced))
(assert-event (equal (oth-a *oth-s1* :fenced) :complete))
(assert-event (equal (oth-a *oth-s2* :completed) :submit))
(assert-event (not (fn-otm-held (oth-s *oth-s2* :completed))))
(assert-event (equal (fn-otm-phase-of (oth-s *oth-s2* :completed)) :idle))

; A failed sync stops and takes no submission.
(assert-event (equal (oth-a *oth-s1* :failed) :stop))
(assert-event (equal (oth-a (oth-s *oth-s1* :failed)
                                                  :completed)
                     :none))

; fn-otm-held-quantum-2-answers-the-held-outcome: the host's quantum-2
; sequence (word, then :completed or :completed-stopping, then the caller's
; answer) on the batch quantum 1 held.
(defun oth-q2 (s word stopping)
  (declare (xargs :guard t))
  (mv-let (step s2) (fn-otm-held-event s word)
    (mv-let (a s3) (fn-otm-held-event s2 (if (and (equal step :complete) stopping)
                                              :completed-stopping
                                            :completed))
      (declare (ignore s3))
      (fn-och-caller-answer a))))
(assert-event (equal (oth-q2 *oth-s1* :fenced nil) :submitted))
(assert-event (equal (oth-q2 *oth-s1* :fenced t) :stopping))
(assert-event (equal (oth-q2 *oth-s1* :failed nil) :stopping))
(assert-event (equal (oth-q2 *oth-s1* :fenced nil) (fn-och-held-outcome :done nil)))
; Teeth: drop the held hypothesis.  The same :staged value without the slot
; is the committer's batch: :fenced completes it, but :completed answers
; :none, so the caller is told :stopping, not the held outcome :submitted.
(defconst *oth-unheld* (fn-otm-with-step (fn-otm-init) :staged nil nil))
(assert-event (and (not (fn-otm-held *oth-unheld*))
                   (equal (fn-otm-phase-of *oth-unheld*) :staged)))
(assert-event (equal (oth-q2 *oth-unheld* :fenced nil) :stopping))
(assert-event (not (equal (oth-q2 *oth-unheld* :fenced nil) (fn-och-held-outcome :done nil))))

; RULING19-MODEL-AWAITS-HOST: the complete model sequence, with each
; hypothesis independently removed while the other two remain true.
(defteeth fn-otm-held-quantum-2-answers-the-held-outcome
  :claim (((held (fn-otm-held s))
           (staged (equal (fn-otm-phase-of s) :staged))
           (job-word (member-equal word '(:fenced :failed))))
          (mv-let (step s2) (fn-otm-held-event s word)
            (equal (fn-och-caller-answer
                    (mv-nth 0 (fn-otm-held-event
                               s2 (if (and (equal step :complete) stopping)
                                      :completed-stopping
                                    :completed))))
                   (fn-och-held-outcome (if (equal word :fenced) :done :uncertain)
                                        stopping))))
  :witness ((s *oth-s1*) (word :fenced) (stopping nil))
  :breaks ((held ((s *oth-unheld*)))
           (staged ((s (fn-otm-with-step (fn-otm-init) :failed nil t))))
           (job-word ((word :completed))))
  :mutations ((ignore-stopping
               (:conclusion
                (mv-let (step s2) (fn-otm-held-event s word)
                  (declare (ignore step))
                  (equal (fn-och-caller-answer (mv-nth 0 (fn-otm-held-event s2 :completed)))
                         (fn-och-held-outcome (if (equal word :fenced) :done :uncertain)
                                              stopping))))
               ((s *oth-s1*) (word :fenced) (stopping t))
               :fault "quantum 2 submits even after COMPLETE finds the owner stopping")
              (failed-is-durable
               (:conclusion
                (equal (oth-q2 s word stopping) (fn-och-held-outcome :done stopping)))
               ((s *oth-s1*) (word :failed) (stopping nil))
               :fault "a failed batch is answered as a durable one")))



; PRF-267 / PRF-901: all new witnesses run the HOSTED plan from init.
(defun oth-plan-s (s event)
  (declare (xargs :guard t))
  (mv-let (action s2 effects) (fn-otm-held-plan s event)
    (declare (ignore action effects)) s2))
(defun oth-plan-a (s event)
  (declare (xargs :guard t))
  (mv-let (action s2 effects) (fn-otm-held-plan s event)
    (declare (ignore s2 effects)) action))

(defconst *oth-plan-started* (oth-plan-s (fn-otm-init) :started-held))
(defconst *oth-plan-fenced* (oth-plan-s *oth-plan-started* :fenced))
(defconst *oth-plan-completed* (oth-plan-s *oth-plan-fenced* :completed))
; plan-barrier-trace: START, no premature COMPLETE, barrier, COMPLETE.
(assert-event (and (equal (oth-plan-a *oth-plan-started* :completed) :fault)
                   (equal (fn-otm-phase-of *oth-plan-started*) :staged)
                   (equal (oth-plan-a *oth-plan-started* :fenced) :complete)
                   (equal (fn-otm-phase-of *oth-plan-fenced*) :fenced)
                   (equal (oth-plan-a *oth-plan-fenced* :completed) :submit)
                   (equal (fn-otm-phase-of *oth-plan-completed*) :idle)))
; The new completion words are genuine protocol completions, not a narrowed
; OCS claim: the whole-step theorem preserves OCS's invalid-event behavior.
(assert-event
 (and (equal (fn-otm-phase-of (oth-plan-s *oth-plan-fenced* :completed-stopping)) :idle)
      (equal (fn-otm-phase-of
              (oth-plan-s (oth-plan-s (fn-otm-init) :started-none-held)
                          :frames-fenced)) :idle)))

(defteeth fn-otm-held-plan-complete-only-after-the-barrier
  :claim (((complete (equal (mv-nth 0 (fn-otm-held-plan s event)) :complete)))
          (and (equal (fn-otm-phase-of s) :staged) (equal event :fenced)))
  :subject fn-otm-held-plan
  :witness ((s *oth-plan-started*) (event :fenced))
  :breaks ((complete ((s (fn-otm-init)) (event :started-held))))
  :mutations ((forged-barrier
               (:hypothesis complete
                (equal (mv-nth 0 (fn-otm-held-plan s :fenced)) :complete))
               ((s *oth-plan-started*) (event :completed))
               :fault "Complete by forging a barrier observation before the barrier")))

(defteeth fn-otm-held-plan-in-flight-until-completed
  :claim (((in-flight (fn-ocs-in-flight-p (fn-otm-phase-of s)))
           (not-completed (not (member-equal event
                                      '(:completed :completed-stopping :frames-fenced)))))
          (fn-ocs-in-flight-p
           (fn-otm-phase-of (mv-nth 1 (fn-otm-held-plan s event)))))
  :subject fn-otm-held-plan
  :witness ((s *oth-plan-fenced*) (event :unexpected))
  :breaks ((in-flight ((s *oth-plan-completed*) (event :unexpected)))
           (not-completed ((s *oth-plan-fenced*) (event :completed))))
  :mutations ((clear-before-completed
               (:conclusion
                (equal (fn-otm-phase-of (mv-nth 1 (fn-otm-held-plan s event))) :idle))
               ((s *oth-plan-fenced*) (event :unexpected))
               :fault "Clear the in-flight batch before COMPLETE reports completion")))

; plan-budget-trace: two pipelined batches, each with START-NEXT and a
; fenced COMPLETE, consume exactly four quanta while control waits.
(defconst *oth-plan-waiting* '(1 0 0 0 1 0))
(defun oth-plan-cycle (s)
  (declare (xargs :guard t))
  (oth-plan-s
   (oth-plan-s
    (oth-next (oth-plan-s (oth-next s *oth-plan-waiting*) :next-started)
              *oth-plan-waiting*)
    :fenced)
   :completed))
(defconst *oth-plan-pipeline* (oth-plan-s (fn-otm-init) :started))
(defconst *oth-plan-budget* (oth-plan-cycle (oth-plan-cycle *oth-plan-pipeline*)))
(assert-event (and (equal (fn-ocp-passes (fn-otm-ocp *oth-plan-budget*)) 4)
                   (equal (fn-otm-phase-of *oth-plan-budget*) :staged)
                   (not (fn-otm-next-of *oth-plan-budget*))
                   (equal (fn-otm-held-committer-wake
                           *oth-plan-budget* nil t *oth-plan-waiting*) :wait)
                   (equal (fn-otm-held-committer-wake
                           *oth-plan-budget* t t *oth-plan-waiting*) :collect)))

(defteeth fn-otm-held-wake-no-start-next-while-a-shut-out-class-waits
  :claim (((waiting (fn-ocp-excluded-waits-p w))
           (budget (<= *fn-ocp-pass-bound* (fn-ocp-passes (fn-otm-ocp s)))))
          (not (equal (fn-otm-held-committer-wake s returned queued w) :start-next)))
  :subject fn-otm-held-committer-wake
  :witness ((s *oth-plan-budget*) (returned nil) (queued t) (w *oth-plan-waiting*))
  :breaks ((waiting ((w *oth-w0*)))
           (budget ((s *oth-plan-pipeline*))))
  :mutations ((ignore-waiter-budget
               (:conclusion
                (equal (fn-otm-held-committer-wake s returned queued w) :start-next))
               ((s *oth-plan-budget*) (returned nil) (queued t) (w *oth-plan-waiting*))
               :fault "Start the next commit after a shut-out class spent its wait budget")))

(defteeth fn-otm-held-committer-wake-is-ocp-when-unheld
  :claim (((unheld (not (fn-otm-held s))))
          (equal (fn-ocp-committer-wake (fn-otm-ocp s) returned queued w)
                 (fn-otm-held-committer-wake s returned queued w)))
  :subject fn-otm-held-committer-wake
  :witness ((s *oth-plan-budget*) (returned t) (queued t) (w *oth-plan-waiting*))
  :breaks ((unheld ((s *oth-plan-fenced*))))
  :mutations ((lose-returned-barrier
               (:conclusion (equal (fn-otm-held-committer-wake s returned queued w) :wait))
               ((s *oth-plan-budget*) (returned t) (queued t) (w *oth-plan-waiting*))
               :fault "Lose the returned barrier instead of collecting it")))

(defteeth-check)
