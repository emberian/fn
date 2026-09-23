; Actual second P-RECORD: the pending link is absent in an old crash image,
; while the transaction directory fence installs its name for every image.
(in-package "ACL2")
(include-book "../../books/byte-store-record-fence")
(include-book "byte-store-stable-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bsk8-attempted () (nth 10 (bsk5-record-2-run)))
(defun bsk8-fenced ()
  (fn-bs-fence-dir (car (bsk8-attempted)) :transactions))

(assert-event
 (let* ((pair (bsk8-attempted))
        (bs (car pair)) (ks (cdr pair))
        (fenced (bsk8-fenced)))
   (and (equal (fn-sf-phase ks) :record-attempted)
        (fn-bs-store-relation bs ks)
        (equal (fn-bs-durable-records bs) (list *bsk5-record*))
        (equal (fn-bs-durable-names fenced :transactions)
               (list (fn-bs-txn-name 0) (fn-bs-txn-name 1)))
        (equal (fn-bs-read-records fenced 0 2)
               (list *bsk5-record* *bsk5-record-2*))
        (equal (fn-bs-durable-records fenced)
               (list *bsk5-record* *bsk5-record-2*))
        (equal (fn-bs-scan-records (fn-bs-scan-store (fn-bs-crash fenced nil)))
               (list *bsk5-record* *bsk5-record-2*)))))

; Without the directory fence, the old image still lacks the candidate.
(must-fail
 (assert-event
  (let ((bs (car (bsk8-attempted))))
    (equal (fn-bs-scan-records (fn-bs-scan-store (fn-bs-crash bs nil)))
           (list *bsk5-record* *bsk5-record-2*)))))

; The actual second P-RECORD has issued a pending link.  ACL2's exact
; durable-record theorem binds the fenced directory to the same candidate
; the Store kernel is carrying, including the older durable record.
(assert-event
 (let* ((pair (bsk8-attempted)) (bs (car pair)) (ks (cdr pair)))
   (and (fn-bs-store-relation bs ks)
        (equal (fn-sf-phase ks) :record-attempted)
        (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
        (equal (fn-bs-durable-records (fn-bs-fence-dir bs :transactions))
               (append (fn-bs-durable-records bs)
                       (list (fn-sf-record-candidate ks)))))))

; Dropping the issued-link premise is a real failure, not a proof-search
; artifact.  The byte state is an actual pre-link program cut; only the
; logical :ok link result is advanced.  The existing relation admits this
; mismatched pair, so phase+relation alone cannot assert K8's conclusion.
(defun bsk8-no-link-but-attempted ()
  (let ((pair (nth 6 (bsk5-record-2-run))))
    (cons (car pair) (fn-sf-record-link-result (cdr pair) :ok))))
(assert-event
 (let* ((pair (bsk8-no-link-but-attempted))
        (bs (car pair)) (ks (cdr pair)))
   (and (fn-bs-store-relation bs ks)
        (equal (fn-sf-phase ks) :record-attempted)
        (not (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
        (equal (fn-bs-durable-records (fn-bs-fence-dir bs :transactions))
               (list *bsk5-record*)))))
(must-fail
 (assert-event
  (let* ((pair (bsk8-no-link-but-attempted))
         (bs (car pair)) (ks (cdr pair)))
    (equal (fn-bs-durable-records (fn-bs-fence-dir bs :transactions))
           (append (fn-bs-durable-records bs)
                   (list (fn-sf-record-candidate ks)))))))
