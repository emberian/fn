; Witnesses and teeth for books/store-log-route-programs.lisp (lane log-2):
; the log route's remaining cuts at related states.  The states are
; tests/acl2/store-log-kernel-tests.lisp's (the recovered segment extended by
; zeros, the kernel it recovers, the batch appended).
(in-package "ACL2")
(include-book "../../books/store-log-route-programs")
(include-book "store-log-kernel-tests")

(defun slrp-related-run-p (bs ks program)
  (declare (xargs :verify-guards nil))
  (fn-lg-all-relp (fn-lg-run bs ks program nil 0) 0 (slk-genesis) (slk-max)))

; fn-lg-reserve-program-keeps-the-relation: a reachable related state, the
; kernel caught up to txid 9, the cut reached (one state) and related.
(assert-event
 (and (fn-lgk-relp (slk-bs-extended) (slk-ks0) 0 (slk-genesis) (slk-max))
      (equal (len (fn-lg-run (slk-bs-extended) (fn-olr-consume-to (slk-ks0) 9)
                             (fn-lg-reserve-program) nil 0))
             1)
      (slrp-related-run-p (slk-bs-extended) (fn-olr-consume-to (slk-ks0) 9)
                          (fn-lg-reserve-program))))
; Hypothesis removed (R): the appended store with the kernel before the
; append (a pending write the kernel does not hold) is not related at the cut.
(assert-event
 (and (not (fn-lgk-relp (slk-appended-bs) (slk-ks0) 0 (slk-genesis) (slk-max)))
      (not (slrp-related-run-p (slk-appended-bs) (fn-olr-consume-to (slk-ks0) 9)
                               (fn-lg-reserve-program)))))

; fn-lg-open-suffix-keeps-the-relation: from the recovered state all seven
; steps (recover-replayed and the three barriers with their cuts) run and
; every state is related.
(assert-event
 (and (fn-lgk-relp (slk-bs-extended) (slk-ks0) 0 (slk-genesis) (slk-max))
      (equal (len (fn-lg-run (slk-bs-extended) (slk-ks0) (fn-lg-open-suffix) nil 0)) 7)
      (slrp-related-run-p (slk-bs-extended) (slk-ks0) (fn-lg-open-suffix))))
; The same with a batch in flight (the hypothesis the five-barrier statement
; carried, removed): related at every cut, because no step of the suffix
; touches the segment.
(assert-event
 (and (fn-lgk-relp (slk-appended-bs) (slk-appended-ks) 0 (slk-genesis) (slk-max))
      (fn-lgk-inflight (slk-appended-ks))
      (slrp-related-run-p (slk-appended-bs) (slk-appended-ks) (fn-lg-open-suffix))))
; Hypothesis removed (R): the appended store with the kernel before the
; append is not related, and neither is any state of the suffix.
(assert-event
 (and (not (fn-lgk-relp (slk-appended-bs) (slk-ks0) 0 (slk-genesis) (slk-max)))
      (not (slrp-related-run-p (slk-appended-bs) (slk-ks0) (fn-lg-open-suffix)))))

; fn-lg-order-program-keeps-the-relation: a record taken into the open batch
; of the recovered kernel; the cut reached and related.
(defun slrp-taken ()
  (declare (xargs :verify-guards nil))
  (cadr (fn-olr-take (slk-ks0) (slk-r 3) (fn-lgk-next-txid (slk-ks0)) 0 0 64 16777216 (slk-unit))))
(assert-event
 (and (fn-lg-recordp (slk-r 3) (slk-max))
      (equal (fn-lgk-batch (slrp-taken)) (list (slk-r 3)))
      (slrp-related-run-p (slk-bs-extended) (slrp-taken) (fn-lg-order-program))))

; Audit packet G4-6 (lane audit-fixes): fn-lg-order-program-keeps-the-
; relation's complete antecedent at the witness, and its removals.
(assert-event
 (and (fn-lgk-relp (slk-bs-extended) (slk-ks0) 0 (slk-genesis) (slk-max))
      (fn-lg-recordp (slk-r 3) (slk-max))
      (slrp-related-run-p (slk-bs-extended) (slrp-taken) (fn-lg-order-program))))
; Removal of R: the appended store with the kernel before the append (a
; pending write the kernel does not hold); the record is a record, the take
; is made, and the cut is not related.
(assert-event
 (and (not (fn-lgk-relp (slk-appended-bs) (slk-ks0) 0 (slk-genesis) (slk-max)))
      (fn-lg-recordp (slk-r 3) (slk-max))
      (not (slrp-related-run-p (slk-appended-bs) (slrp-taken) (fn-lg-order-program)))))
; Removal of (fn-lg-recordp record max): a 5,000-octet record past MAX 4096.
; The take does not check the log's bound (it is :taken into the batch), R
; holds before it, and the cut is not related.
(assert-event
 (let* ((big (make-list 5000 :initial-element 7))
        (r (fn-olr-take (slk-ks0) big (fn-lgk-next-txid (slk-ks0)) 0 0 64 16777216 (slk-unit))))
   (and (fn-lgk-relp (slk-bs-extended) (slk-ks0) 0 (slk-genesis) (slk-max))
        (not (fn-lg-recordp big (slk-max)))
        (equal (car r) :taken)
        (equal (fn-lgk-batch (cadr r)) (list big))
        (not (slrp-related-run-p (slk-bs-extended) (cadr r) (fn-lg-order-program))))))

; -----------------------------------------------------------------------------
; fn-lg-open-program-keeps-the-relation-at-every-cut (lane host-model, P10):
; the WHOLE served open from the crashed store of store-log-kernel-tests (two
; records, a torn unit, two zero units; nothing pending).  The witness asserts
; every hypothesis, then the conclusion: the recover program completes (four
; states, log-recovered related), the open's run is the recover run followed
; by the suffix from the recovered state, every state from there on is
; related, and all eleven states are reached (every cut of the program).

(defun slrp-open-hyps (bs genesis)
  (declare (xargs :guard t :verify-guards nil))
  (list (posp (fn-bs-unit bs)) (and (assoc-equal 0 (fn-bs-inodes bs)) t)
        (true-listp (fn-bs-durable-content bs 0))
        (equal (mod (len (fn-bs-durable-content bs 0)) (fn-bs-unit bs)) 0)
        (fn-frame-digestp genesis)
        ;; the owner's sole-pending-writer obligation, asserted as its
        ;; executable twin (store-log-programs-tests does the same: the
        ;; constrained fn-assume-log-sole-pending-writer cannot be evaluated;
        ;; books/store-log-recover discharges it from this predicate)
        (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) 0))
        (not (fn-bs-ops-for-ino (fn-bs-pending bs) 0))))

(defun slrp-open-conclusion (bs genesis)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((ks (fn-lg-recovered-kernel bs 0 genesis (slk-max) 1))
         (recover (fn-lg-run bs ks (fn-lg-recover-program) nil 0))
         (recovered (car (last recover)))
         (run (fn-lg-run bs ks (fn-lg-open-program) nil 0)))
    (and (equal (len recover) 4)
         (fn-lgk-relp (car recovered) (cdr recovered) 0 genesis (slk-max))
         (equal run (append recover
                            (fn-lg-run (car recovered) (cdr recovered)
                                       (fn-lg-open-suffix) nil 0)))
         (fn-lg-all-relp (nthcdr 4 run) 0 genesis (slk-max)))))

; REACHABLE POSITIVE: the complete antecedent and the conclusion; and every
; one of the program's eleven states (six cuts) is reached.
(assert-event
 (let ((bs (slk-store (slk-content) nil)))
   (and (equal (slrp-open-hyps bs (slk-genesis)) '(t t t t t t t))
        (slrp-open-conclusion bs (slk-genesis))
        (equal (len (fn-lg-run bs (fn-lg-recovered-kernel bs 0 (slk-genesis) (slk-max) 1)
                               (fn-lg-open-program) nil 0))
               11))))

; HYPOTHESIS REMOVED (the owner's sole-pending-writer obligation, and with it
; "no operation of the segment pending"): the log's own write pending at the
; open.  The recover program still runs, and the state it leaves is NOT
; related, so neither is the suffix.
(assert-event
 (let ((bs (slk-store (slk-content) (list (list :write 0 (len (slk-content)) '(1 2 3 4))))))
   (and (equal (slrp-open-hyps bs (slk-genesis)) '(t t t t t nil nil))
        (not (slrp-open-conclusion bs (slk-genesis))))))

; HYPOTHESIS REMOVED (the content's length a multiple of the unit): a
; segment with a dangling octet.  No relation at the recovered state.
(assert-event
 (let ((bs (slk-store (append (slk-content) '(0)) nil)))
   (and (equal (slrp-open-hyps bs (slk-genesis)) '(t t t nil t t t))
        (not (slrp-open-conclusion bs (slk-genesis))))))
; The other hypotheses' removals are tests/acl2/store-log-programs-tests.lisp's
; for fn-lg-recover-program-establishes-the-relation, whose antecedent this
; theorem carries unchanged.
