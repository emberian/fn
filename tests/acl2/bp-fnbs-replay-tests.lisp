; Ordered, byte-decoded FNBS kind-5 recovery with inherited authority.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-replay-invariants")
(include-book "bp-fnbs-codec-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnfr-second*
  (fn-bpnf-stored-record
   9 1 (fn-bpnf-frame-held *bpnfc-anon-ingress* 1
                           *bpnfc-bundle* *bpnfc-wire*)))
(defun bpnfr-first-row ()
  (list (fn-bpnf-stored-record-name 9 0)
        (fn-bpnf-stored-record-frame *bpnfc-record*)))
(defun bpnfr-second-row ()
  (list (fn-bpnf-stored-record-name 9 1)
        (fn-bpnf-stored-record-frame *bpnfr-second*)))
(defun bpnfr-rows () (list (bpnfr-first-row) (bpnfr-second-row)))

(assert-event (equal (fn-bpnf-replay-rows nil 4 1048576)
                     '(:ready nil nil)))
(assert-event (fn-bpnf-replay-rowp (bpnfr-first-row)))
(assert-event (fn-bpnf-replay-rowp (bpnfr-second-row)))
(assert-event
 (equal (fn-bpnf-replay-rows (bpnfr-rows) 4 1048576)
        (list :ready (list (nth 3 *bpnfr-second*) (nth 3 *bpnfc-record*))
              (cons 9 1))))
; Two rows fill this fixture's exact max-held budget, and the byte replay
; returns the next arrival frontier 2. A third row is capacity-refused.
(assert-event
 (equal (fn-bpnf-held-arrival-frontier
         (cadr (fn-bpnf-replay-rows (bpnfr-rows) 2 1048576)))
        2))
; A second process crash/replay with zero newly published rows is a fixed
; point on the authoritative byte observation.
(assert-event
 (equal (fn-bpnf-replay-rows (bpnfr-rows) 4 1048576)
        (fn-bpnf-replay-rows (bpnfr-rows) 4 1048576)))

(assert-event
 (equal (car (fn-bpnf-replay-rows
              (list (list "9-0.fnb" (cadr (bpnfr-first-row)))) 4 1048576))
        :fault))
(assert-event
 (equal (car (fn-bpnf-replay-rows
              (list (bpnfr-second-row) (bpnfr-first-row)) 4 1048576))
        :fault))
(assert-event
 (equal (car (fn-bpnf-replay-rows
              (list (list (car (bpnfr-first-row)) '(1 2 3))) 4 1048576))
        :fault))
(assert-event
 (equal (car (fn-bpnf-replay-rows (bpnfr-rows) 1 1048576)) :fault))
(must-fail
 (assert-event
  (equal (fn-bpnf-replay-rows
          (list (list "9-0.fnb" (cadr (bpnfr-first-row)))) 4 1048576)
         (fn-bpnf-replay-rows (list (bpnfr-first-row)) 4 1048576))))

; The same actual byte replay result is the recovery-only step argument.
(defun bpnfr-recover (st epoch rows)
  (fn-bpnf-step
   st (fn-bpnf-recover-event st epoch nil :ready rows)))
(defun bpnfr-uncertain-state ()
  (fn-bpnf-answer-state
   (fn-bpnf-step (fn-bpnf-answer-state *bpnfc-proposal*)
                 '(:persist-result 9 0 :uncertain))))
; These two direct logical recovery values straddle the u64 frontier. They
; exercise the recovery-only defensive check, not a claim that a canonical
; byte replay can produce the overflow value.
(defconst *bpnfr-max-arrival-held*
  (update-nth 3 *fn-frame-max-nat* (nth 3 *bpnfc-record*)))
(defconst *bpnfr-overflow-arrival-held*
  (update-nth 3 (1+ *fn-frame-max-nat*) (nth 3 *bpnfc-record*)))
(assert-event
 (equal (fn-bpnf-held-arrival-frontier (list *bpnfr-max-arrival-held*))
        (1+ *fn-frame-max-nat*)))
(assert-event
 (equal (fn-bpnf-held-list
         (fn-bpnf-answer-state
          (fn-bpnf-step
           (bpnfr-uncertain-state)
           (list :recover-fnbs 10 nil :ready
                 (list :ready (list *bpnfr-max-arrival-held*) nil)))))
        (list *bpnfr-max-arrival-held*)))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step
          (bpnfr-uncertain-state)
          (list :recover-fnbs 10 nil :ready
                (list :ready (list *bpnfr-overflow-arrival-held*) nil))))
        (bpnfr-uncertain-state)))
(assert-event (equal (nth 5 (fn-bpnf-issued (bpnfr-uncertain-state)))
                     :uncertain))
(assert-event
 (equal (nth 1 (fn-bpnf-recover-auto-event
                (bpnfr-uncertain-state) nil :ready (bpnfr-rows)))
        10))
(assert-event
 (equal (nth 1 (fn-bpnf-recover-auto-event
                (bpnfr-uncertain-state) nil :ready nil))
        10))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step (bpnfr-uncertain-state)
                       (fn-bpnf-recover-auto-event
                        (bpnfr-uncertain-state) nil :ready (bpnfr-rows))))
        (fn-bpnf-answer-state
         (bpnfr-recover (bpnfr-uncertain-state) 10 (bpnfr-rows)))))
(defconst *bpnfr-terminal-epoch*
  (fn-bpnf-state *bpnfc-base* nil nil nil nil nil nil
                 *fn-frame-max-nat* 0))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step *bpnfr-terminal-epoch*
                       (fn-bpnf-recover-auto-event
                        *bpnfr-terminal-epoch* nil :ready nil)))
        *bpnfr-terminal-epoch*))
(assert-event
 (equal (fn-bpnf-held-list
         (fn-bpnf-answer-state (bpnfr-recover (bpnfr-uncertain-state)
                                             10 (bpnfr-rows))))
        (list (nth 3 *bpnfr-second*) (nth 3 *bpnfc-record*))))
(assert-event
 (null (fn-bpnf-issued
        (fn-bpnf-answer-state (bpnfr-recover (bpnfr-uncertain-state)
                                            10 (bpnfr-rows))))))
(assert-event
 (equal (fn-bpnf-epoch
         (fn-bpnf-answer-state (bpnfr-recover (bpnfr-uncertain-state)
                                             10 (bpnfr-rows)))) 10))
(assert-event
 (equal (fn-bpnf-answer-state
         (bpnfr-recover (bpnfr-uncertain-state) 9 (bpnfr-rows)))
        (bpnfr-uncertain-state)))
(assert-event
 (equal (fn-bpnf-answer-state
         (bpnfr-recover (bpnfr-uncertain-state) 10
                        (list (list "wrong.fnb" (cadr (bpnfr-first-row))))))
        (bpnfr-uncertain-state)))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step
          (fn-bpnf-answer-state
           (bpnfr-recover (bpnfr-uncertain-state) 10 (bpnfr-rows)))
          '(:persist-result 9 0 :durable)))
        (fn-bpnf-answer-state
         (bpnfr-recover (bpnfr-uncertain-state) 10 (bpnfr-rows)))))
