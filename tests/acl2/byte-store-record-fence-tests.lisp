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
