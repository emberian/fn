; Teeth for books/consumer-replay-bound (PKT-370): the keystone's whole
; antecedent and conclusion on a log the served admission writes, its one
; hypothesis removed (a register past field 9 that the replay, which runs no
; admission bound, still applies), and a labelled mutation.
(in-package "ACL2")
(include-book "../../books/consumer-replay-bound")
(include-book "must-fail-checked")

; An opened profile whose field 9 admits two consumers.
(defconst *crbt-profile* (fn-bs-profile-put *fn-bs-pf-max-consumers* 2
                                            *fn-bs-profile-defaults*))
(assert-event (fn-bs-profile-validp *crbt-profile*))
(assert-event (equal (fn-bs-profile-max-consumers *crbt-profile*) 2))

(defconst *crbt-boot* (fn-cpe-make 0 0 0 '(:bootstrap (1) (2))))
(defun crbt-reg (seq consumer epoch)
  (fn-cpe-make seq seq seq (list :register consumer '(4) '(5) 1 1 epoch)))
(defun crbt-replay (records) (fn-cpe-projection-replay nil records 0))
(defun crbt-table-len (records) (len (fn-cp-nth 5 (fn-cp-nth 1 (crbt-replay records)))))
(defun crbt-within (records)
  (fn-crb-registers-within nil records 0 (fn-bs-profile-max-consumers *crbt-profile*)))

; fn-crb-replay-keeps-the-consumer-bound, REACHABLE positive: bootstrap,
; register A and B, unregister A, register C.
; Every register is the served admission's write under field 9 in the state
; replay reaches (C is admitted once A is gone), so the antecedent holds;
; the replayed table holds two entries, within the bound.
(defconst *crbt-log*
  (list *crbt-boot* (crbt-reg 1 '(3) 1) (crbt-reg 2 '(6) 2)
        (fn-cpe-make 3 3 3 '(:unregister (3) 1))
        (crbt-reg 4 '(7) 3)))
(assert-event (equal (car (crbt-replay *crbt-log*)) :ok))
(assert-event (crbt-within *crbt-log*))
(assert-event (equal (crbt-table-len *crbt-log*) 2))
(assert-event (<= (crbt-table-len *crbt-log*)
                  (nfix (fn-bs-profile-max-consumers *crbt-profile*))))
; The third register was admitted only because the unregister made room:
; against the table before the unregister, the served admission refuses it.
(assert-event (equal (fn-cp-register-within
                      (fn-cp-nth 1 (crbt-replay (take 3 *crbt-log*))) 2
                      '(4) '(7) '(5) 1 1)
                     '(:refused :max-consumers)))

; Hypothesis removal (REACHABLE log, no unregister): a third register while
; two are held.  The served admission would refuse it (:max-consumers), so
; the antecedent fails; the replay, which re-runs fn-cp-register without the
; bound, applies it, and the replayed table holds three, past field 9.
(defconst *crbt-past*
  (list *crbt-boot* (crbt-reg 1 '(3) 1) (crbt-reg 2 '(6) 2) (crbt-reg 3 '(7) 3)))
(assert-event (equal (car (crbt-replay *crbt-past*)) :ok))
(assert-event (not (crbt-within *crbt-past*)))
(assert-event (equal (crbt-table-len *crbt-past*) 3))
(assert-event (not (<= (crbt-table-len *crbt-past*)
                       (nfix (fn-bs-profile-max-consumers *crbt-profile*)))))
(must-fail-checked
 (defthm crbt-without-registers-within
   (<= (len (fn-cp-nth 5 (fn-cp-nth 1 (fn-cpe-projection-replay nil records 0))))
       (nfix (fn-bs-profile-max-consumers values)))
   :hints (("Goal" :in-theory (disable fn-cpe-projection-replay
                                       fn-bs-profile-max-consumers)))))

; MUTATION: the conclusion strengthened to strictly below field 9 fails at
; the positive, whose table is exactly at the bound.
(assert-event (not (< (crbt-table-len *crbt-log*)
                      (nfix (fn-bs-profile-max-consumers *crbt-profile*)))))
