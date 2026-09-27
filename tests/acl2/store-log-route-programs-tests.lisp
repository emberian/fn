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

; fn-lg-open-suffix-keeps-the-relation: from the recovered state (nothing in
; flight) all ten steps run and every state is related.
(assert-event
 (and (not (fn-lgk-inflight (slk-ks0)))
      (equal (len (fn-lg-run (slk-bs-extended) (slk-ks0) (fn-lg-open-suffix) nil 0)) 11)
      (slrp-related-run-p (slk-bs-extended) (slk-ks0) (fn-lg-open-suffix))))
; Hypothesis removed (nothing in flight): with a batch in flight the
; segment's barrier makes it durable but the open's kernel does not commit
; it, so the states after that barrier are not related.
(assert-event
 (and (fn-lgk-relp (slk-appended-bs) (slk-appended-ks) 0 (slk-genesis) (slk-max))
      (fn-lgk-inflight (slk-appended-ks))
      (not (slrp-related-run-p (slk-appended-bs) (slk-appended-ks) (fn-lg-open-suffix)))))

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
