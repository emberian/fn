; Actual second P-RECORD retention publication, including both possible
; transaction-directory EIO outcomes.  A failed fsync is not proof that the
; link was absent: recovery must distinguish the two physical images.
(in-package "ACL2")
(include-book "../../books/byte-store-retention-publication")
(include-book "byte-store-record-provenance-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bsrp-run ()
  (fn-bs-run (bsk6-start) (bsk6-retention-prepared)
             (fn-bs-record-program ".stage-k6-retention" (fn-bs-txn-name 1)
                                   (bsk6-retention-frame))
             nil *bsk5-groups* *bsk5-capacity*))

(assert-event
 (let* ((event (bsk6-retention-candidate))
        (ks (bsk6-retention-prepared))
        (bs (bsk6-start))
        (pair (nth 10 (bsrp-run))))
   (and (fn-store-retention-event-p event)
        (fn-bs-store-relation bs ks)
        (fn-bs-namep ".stage-k6-retention")
        (not (fn-bs-lookup bs :staging ".stage-k6-retention"))
        (equal (fn-sf-phase ks) :record-staged)
        (equal (fn-sf-record-candidate ks) event)
        (equal (fn-bs-record-of-octets (bsk6-retention-frame)) event)
        (fn-bs-record-inputp ks ".stage-k6-retention" (fn-bs-txn-name 1)
                             (bsk6-retention-frame))
        (fn-bs-store-relation (car pair) (cdr pair)))))

(defun bsrp-dir-eio-run (choice)
  (fn-bs-run (bsk6-start) (bsk6-retention-prepared)
             (fn-bs-record-program ".stage-k6-retention" (fn-bs-txn-name 1)
                                   (bsk6-retention-frame))
             (fn-bsrp-record-dir-error-outcomes choice)
             *bsk5-groups* *bsk5-capacity*))

; The public applied-branch theorem's exact conclusion at these fixed host
; arguments.  Its teeth below preserve the other two premises each time.
(defun bsrp-applied-exactp (bs ks stage name frame)
  (let* ((ok-run (fn-bs-run bs ks (fn-bs-record-program stage name frame)
                            nil *bsk5-groups* *bsk5-capacity*))
         (attempt (nth 10 ok-run))
         (run (fn-bs-run bs ks (fn-bs-record-program stage name frame)
                         (fn-bsrp-record-dir-error-outcomes :apply)
                         *bsk5-groups* *bsk5-capacity*))
         (failed (nth 11 run)))
    (and (equal (len run) 12)
         (fn-bs-store-relation (car failed) (cdr attempt))
         (equal (fn-bs-durable-records (car failed))
                (append (fn-bs-durable-records (car attempt))
                        (list (fn-sf-record-candidate (cdr attempt)))))
         (fn-bs-dir-quietp (car failed) :transactions)
         (fn-sf-fencedp
          (fn-sf-record-dir-result (cdr failed) :error)))))

(defun bsrp-existing-stage ()
  (mv-let (result bs)
    (fn-bs-create (bsk6-start) :staging ".stage-k6-retention" :ok)
    (declare (ignore result))
    bs))

(assert-event
 (let* ((applied (bsrp-dir-eio-run :apply))
        (dropped (bsrp-dir-eio-run :drop))
        (a (car (nth 11 applied)))
        (d (car (nth 11 dropped)))
        (ka (cdr (nth 11 applied)))
        (kd (cdr (nth 11 dropped)))
        (name (fn-bs-txn-name 1)))
   (and (equal (len applied) 12)
        (equal (len dropped) 12)
        (equal (fn-sf-phase ka) :record-attempted)
        (equal ka kd)
        (not (fn-bs-durable-entry (car (nth 10 applied))
                                  :transactions name))
        (fn-bs-lookup a :transactions name)
        (not (fn-bs-lookup d :transactions name))
        (fn-bs-dir-quietp a :transactions)
        (fn-bs-dir-quietp d :transactions)
        (fn-sf-fencedp (fn-sf-record-dir-result ka :error))
        (fn-bs-store-relation a ka)
        (equal (fn-bs-durable-records a)
               (list *bsk5-record* (bsk6-retention-candidate)))
        (equal (fn-bs-durable-records d) (list *bsk5-record*))
        (equal (fn-bs-scan-records (fn-bs-scan-store a))
               (list *bsk5-record* (bsk6-retention-candidate)))
        (equal (fn-bs-scan-records (fn-bs-scan-store d))
               (list *bsk5-record*)))))

(assert-event
 (bsrp-applied-exactp (bsk6-start) (bsk6-retention-prepared)
                      ".stage-k6-retention" (fn-bs-txn-name 1)
                      (bsk6-retention-frame)))

; The old set/delete pair is a reachable bad prehistory, not an arbitrary
; malformed state.  Typed input and freshness still hold.
(assert-event
 (let ((bs (bsk6-prior-final-set-and-delete))
       (ks (bsk6-retention-prepared)))
   (and (fn-bs-statep bs)
        (not (fn-bs-store-relation bs ks))
        (fn-bs-record-inputp ks ".stage-k6-retention" (fn-bs-txn-name 1)
                             (bsk6-retention-frame))
        (not (fn-bs-lookup bs :staging ".stage-k6-retention"))
        (not (bsrp-applied-exactp bs ks ".stage-k6-retention"
                                  (fn-bs-txn-name 1)
                                  (bsk6-retention-frame))))))
(must-fail
 (assert-event
  (bsrp-applied-exactp (bsk6-prior-final-set-and-delete)
                       (bsk6-retention-prepared) ".stage-k6-retention"
                       (fn-bs-txn-name 1) (bsk6-retention-frame))))

; An article frame at the retention candidate's name is not the candidate.
(assert-event
 (let ((bs (bsk6-start)) (ks (bsk6-retention-prepared)))
   (and (fn-bs-store-relation bs ks)
        (not (fn-bs-record-inputp ks ".stage-k6-retention"
                                  (fn-bs-txn-name 1) (bsk5-frame-2)))
        (not (fn-bs-lookup bs :staging ".stage-k6-retention"))
        (not (bsrp-applied-exactp bs ks ".stage-k6-retention"
                                  (fn-bs-txn-name 1) (bsk5-frame-2))))))
(must-fail
 (assert-event
  (bsrp-applied-exactp (bsk6-start) (bsk6-retention-prepared)
                       ".stage-k6-retention" (fn-bs-txn-name 1)
                       (bsk5-frame-2))))

; A visible orphan with the requested staging name makes create refuse;
; the byte relation and the correctly typed retention frame still hold.
(assert-event
 (let ((bs (bsrp-existing-stage)) (ks (bsk6-retention-prepared)))
   (and (fn-bs-store-relation bs ks)
        (fn-bs-record-inputp ks ".stage-k6-retention" (fn-bs-txn-name 1)
                             (bsk6-retention-frame))
        (fn-bs-lookup bs :staging ".stage-k6-retention")
        (not (bsrp-applied-exactp bs ks ".stage-k6-retention"
                                  (fn-bs-txn-name 1)
                                  (bsk6-retention-frame))))))
(must-fail
 (assert-event
  (bsrp-applied-exactp (bsrp-existing-stage) (bsk6-retention-prepared)
                       ".stage-k6-retention" (fn-bs-txn-name 1)
                       (bsk6-retention-frame))))

; If the error were treated as a known abort, this would falsely claim the
; new final name absent even when the directory applied the link.
(must-fail
 (assert-event
  (not (fn-bs-lookup (car (nth 11 (bsrp-dir-eio-run :apply)))
                     :transactions (fn-bs-txn-name 1)))))

; Conversely, the same error does not certify that the candidate landed.
(must-fail
 (assert-event
  (equal (fn-bs-durable-records
          (car (nth 11 (bsrp-dir-eio-run :drop))))
         (list *bsk5-record* (bsk6-retention-candidate)))))
