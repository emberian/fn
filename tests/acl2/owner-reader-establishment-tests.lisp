(in-package "ACL2")
(include-book "../../books/owner-reader-establishment")
(include-book "must-fail-checked")
; Existing checkpoint fixture: two retention events and two configuration records.
(defconst *ock-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-ock" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-ock" "subject" "evidence" 0)))
(defconst *ock-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *ock-t-prefix* (list (car *ock-t-events*)))
(defconst *ock-t-suffix* (cdr *ock-t-events*))
(defconst *ock-t-full* (fn-ock-recover-full *ock-t-configs* 8 *ock-t-events* 4))
(defconst *ock-t-extended*
  (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                 *ock-t-configs* *ock-t-suffix*))


; Literal positive witness: both prefix and suffix are nonempty, recovery succeeds.
(defconst *orri-t-owner*
 (fn-ock-recover-extended
  (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                 *ock-t-configs* *ock-t-suffix*)
  *ock-t-configs* 8 4))
(assert-event (and (consp *ock-t-prefix*) (consp *ock-t-suffix*)
                   (not (equal *orri-t-owner* :fault))
                   (fn-ocri-relation *orri-t-owner*)))
; Hypothesis removal: refused recovery, no retained hypotheses, conclusion false.
(defconst *orri-t-fault*
 (fn-ock-recover-extended
  (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                 *ock-t-configs* *ock-t-suffix*)
  *ock-t-configs* 8 nil))
(assert-event (and (equal *orri-t-fault* :fault)
                   (not (fn-ocri-relation *orri-t-fault*))))
(must-fail-checked
 (defthm orri-t-without-success
  (fn-ocri-relation *orri-t-fault*)))
