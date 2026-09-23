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
(assert-event (equal (nth 5 (fn-bpnf-issued (bpnfr-uncertain-state)))
                     :uncertain))
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
