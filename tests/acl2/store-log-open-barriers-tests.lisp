; Witnesses and teeth for books/store-log-open-barriers.lisp (lane
; log-recovery-2): the open's duplicate segment fence, and why one barrier is
; not enough.  The states are tests/acl2/store-log-kernel-tests.lisp's.
(in-package "ACL2")
(include-book "../../books/store-log-open-barriers")
(include-book "store-log-kernel-tests")

(defun slob-step (bs ks)
  (declare (xargs :verify-guards nil))
  (mv-let (r bs1 ks1) (fn-lg-step bs ks '(:fence :segment :tail) :ok 0)
    (list r bs1 ks1)))

(defun slob-identityp (bs ks)
  (declare (xargs :verify-guards nil))
  (equal (slob-step bs ks) (list :ok bs ks)))

; fn-lgob-duplicate-segment-fence-is-identity, reachable witness: the
; recovered segment (P-LOG-RECOVER run: zeroed and fenced) with its kernel;
; every hypothesis holds and the second fence is the identity.
(assert-event
 (and (fn-bs-shapep (slk-bs0))
      (fn-lgk-relp (slk-bs0) (slk-ks0) 0 (slk-genesis) (slk-max))
      (not (consp (fn-lgk-inflight (slk-ks0))))
      (slob-identityp (slk-bs0) (slk-ks0))))

; Hypothesis removed (fn-bs-shapep): a store with a seventh field, related and
; idle; the fence rebuilds a six-field store, not the one given.
(assert-event
 (let ((bs (append (slk-bs0) '(extra))))
   (and (not (fn-bs-shapep bs))
        (fn-lgk-relp bs (slk-ks0) 0 (slk-genesis) (slk-max))
        (not (consp (fn-lgk-inflight (slk-ks0))))
        (not (slob-identityp bs (slk-ks0))))))

; Hypothesis removed (R): a store with a pending write of its segment the
; kernel does not hold (not related); the fence lands it.
(assert-event
 (let ((bs (slk-write (slk-bs0) 0 0 '(1 1 1 1))))
   (and (fn-bs-shapep bs)
        (not (fn-lgk-relp bs (slk-ks0) 0 (slk-genesis) (slk-max)))
        (not (consp (fn-lgk-inflight (slk-ks0))))
        (not (slob-identityp bs (slk-ks0))))))

; Hypothesis removed (nothing in flight): the appended batch, related with its
; kernel in flight; the fence lands the batch's write.
(assert-event
 (and (fn-bs-shapep (slk-appended-bs))
      (fn-lgk-relp (slk-appended-bs) (slk-appended-ks) 0 (slk-genesis) (slk-max))
      (consp (fn-lgk-inflight (slk-appended-ks)))
      (not (slob-identityp (slk-appended-bs) (slk-appended-ks)))))

; fn-lgob-recovered-segment-fence-is-identity, reachable witness: the crashed
; content of the kernel tests (two records, a torn unit, zeros), the recovery
; program run to log-recovered, then the second fence: the identity.
(assert-event
 (let* ((bs (slk-store (slk-content) nil))
        (ks (fn-lg-recovered-kernel bs 0 (slk-genesis) (slk-max) 1))
        (run (fn-lg-run bs ks (fn-lg-recover-program) nil 0))
        (final (car (last run))))
   (and (equal (len run) 4)
        (fn-lgk-relp (car final) (cdr final) 0 (slk-genesis) (slk-max))
        (slob-identityp (car final) (cdr final)))))

; fn-lgob-file-fence-keeps-entry-operations, witness: the rotated store's
; pending create survives the segment's fence.
(assert-event
 (let* ((s (fn-lgob-rotated-store))
        (op '(:set-entry :journal "000002.log" 2)))
   (and (member-equal op (fn-bs-pending s))
        (member-equal op (fn-bs-pending (fn-bs-fence-file s 2))))))
; Hypothesis removed (not a write): a pending write of the fenced inode is
; drained.
(assert-event
 (let* ((s (fn-lgob-write (fn-lgob-rotated-store) 2 '(5 5 5 5)))
        (op '(:write 2 0 (5 5 5 5))))
   (and (member-equal op (fn-bs-pending s))
        (not (member-equal op (fn-bs-pending (fn-bs-fence-file s 2)))))))
; Hypothesis removed (pending): an operation never issued is not pending after.
(assert-event
 (let ((op '(:set-entry :journal "000003.log" 3)))
   (and (not (member-equal op (fn-bs-pending (fn-lgob-rotated-store))))
        (not (member-equal op (fn-bs-pending (fn-bs-fence-file (fn-lgob-rotated-store) 2)))))))

; The counterexample's control: the same run with journal/ fenced leaves
; nothing pending, and the one-barrier run leaves exactly the create.
(assert-event
 (and (null (fn-bs-pending (fn-lgob-acked-batch t)))
      (equal (fn-bs-pending (fn-lgob-acked-batch nil))
             '((:set-entry :journal "000002.log" 2)))
      (equal (fn-bs-durable-entry (fn-bs-crash (fn-lgob-acked-batch nil) '(:apply))
                                  :journal "000002.log")
             2)))
