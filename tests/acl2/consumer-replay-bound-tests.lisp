; Teeth for books/consumer-replay-bound (PKT-370).  The consumer log is
; written by the served producer (books/consumer-owner-local.lisp:
; fn-col-bootstrap, fn-col-register under MAX, fn-col-unregister) and
; committed through the Store (fn-sn-prepare-consumer, fn-sn-finish); the
; open replays the committed records (fn-cpe-projection-replay nil RECORDS
; 0).  Per the keystone: the whole antecedent and conclusion, its one
; hypothesis removed, and a labelled mutation.
(in-package "ACL2")
(include-book "../../books/consumer-replay-bound")
(include-book "../../books/consumer-owner-local")
(include-book "must-fail-checked")

; An opened profile whose max-consumers admits two consumers.
(defconst *crbt-profile* (fn-bs-profile-put *fn-bs-pf-max-consumers* 2
                                            *fn-bs-profile-defaults*))
(assert-event (fn-bs-profile-validp *crbt-profile*))
(assert-event (equal (fn-bs-profile-max-consumers *crbt-profile*) 2))

; The Store commit of one proposed consumer event (the reserve, prepare,
; record I/O and finish the owner drives).
(defun crbt-commit (s event)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare-consumer
                (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                              :frontier-file :ok)
                                    :frontier-replace :ok)
                          :frontier-directory :ok)
                event)
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
; The served proposal over the store, committed when it is a write.
(defun crbt-propose (s result)
  (if (eq (car result) :write) (crbt-commit s (cadr result)) s))
(defun crbt-owner (s) (fn-own-start s 2))
(defun crbt-id (k) (make-list 32 :initial-element k))
(defconst *crbt-group* '(102 110 46 116 101 115 116)) ; fn.test
(defun crbt-register (s max k)
  (crbt-propose s (fn-col-register (crbt-owner s) max (crbt-id k) *crbt-group*)))
(defun crbt-records (s) (fn-sf-records (fn-sn-files s)))
(defun crbt-replay (s) (fn-cpe-projection-replay nil (crbt-records s) 0))
(defun crbt-table-len (s) (len (fn-cp-nth 5 (fn-cp-nth 1 (crbt-replay s)))))
(defun crbt-within (s max) (fn-crb-registers-within nil (crbt-records s) 0 max))

; Bootstrap, then two registrations under the bound 2.
(defconst *crbt-s0*
  (crbt-propose (fn-sn-initial '("fn.test") 16)
                (fn-col-bootstrap (crbt-owner (fn-sn-initial '("fn.test") 16))
                                  (crbt-id 11) (crbt-id 12))))
(defconst *crbt-s2* (crbt-register (crbt-register *crbt-s0* 2 1) 2 2))
; A third registration under the bound 2 is refused by the producer and
; nothing is committed.
(assert-event (equal (fn-col-register (crbt-owner *crbt-s2*) 2 (crbt-id 3) *crbt-group*)
                     '(:refused :max-consumers)))
; Unregister the first, then the third is admitted.
(defconst *crbt-s3*
  (crbt-propose *crbt-s2* (fn-col-unregister (crbt-owner *crbt-s2*) (crbt-id 1))))
(defconst *crbt-s4* (crbt-register *crbt-s3* 2 3))
(assert-event (equal (len (crbt-records *crbt-s4*)) 5))

; fn-crb-replay-keeps-the-consumer-bound, REACHABLE positive: the log the
; producer wrote under max-consumers 2 satisfies the antecedent, the open's
; replay succeeds, and the replayed table holds two, at the bound.
(assert-event (crbt-within *crbt-s4* (fn-bs-profile-max-consumers *crbt-profile*)))
(assert-event (equal (car (crbt-replay *crbt-s4*)) :ok))
(assert-event (equal (crbt-table-len *crbt-s4*) 2))
(assert-event (<= (crbt-table-len *crbt-s4*)
                  (nfix (fn-bs-profile-max-consumers *crbt-profile*))))

; Hypothesis removal (REPLAY-REACHABLE: a log the producer wrote under the
; bound 3, replayed under max-consumers 2).  Three registrations commit; at
; the third, the admission under 2 would refuse, so the antecedent fails;
; the replay re-runs fn-cp-register without the bound and holds three.
(defconst *crbt-s-past* (crbt-register *crbt-s2* 3 3))
(assert-event (equal (len (crbt-records *crbt-s-past*)) 4))
(assert-event (not (crbt-within *crbt-s-past* (fn-bs-profile-max-consumers *crbt-profile*))))
(assert-event (crbt-within *crbt-s-past* 3))
(assert-event (equal (car (crbt-replay *crbt-s-past*)) :ok))
(assert-event (equal (crbt-table-len *crbt-s-past*) 3))
(assert-event (not (<= (crbt-table-len *crbt-s-past*)
                       (nfix (fn-bs-profile-max-consumers *crbt-profile*)))))
(must-fail-checked
 (defthm crbt-without-registers-within
   (<= (len (fn-cp-nth 5 (fn-cp-nth 1 (fn-cpe-projection-replay nil records 0))))
       (nfix (fn-bs-profile-max-consumers values)))
   :hints (("Goal" :in-theory (disable fn-cpe-projection-replay
                                       fn-bs-profile-max-consumers)))))

; MUTATION: the conclusion strengthened to strictly below max-consumers
; fails at the positive, whose table is exactly at the bound.
(assert-event (not (< (crbt-table-len *crbt-s4*)
                      (nfix (fn-bs-profile-max-consumers *crbt-profile*)))))
