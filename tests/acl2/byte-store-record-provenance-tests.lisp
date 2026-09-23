; Teeth for the actual P-RECORD file-fence cut.  The second publication
; follows an earlier acknowledged record, so the retained Store is not empty.
(in-package "ACL2")
(include-book "../../books/byte-store-record-provenance")
(include-book "byte-store-stable-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bsk6-start () (car (bsk5-frontier-2)))
(defun bsk6-file-cut () (car (nth 5 (bsk5-record-2-run))))

(assert-event
 (and (fn-bs-statep (bsk6-start))
      (not (fn-bs-lookup (bsk6-start) :staging ".stage-k5-2"))
      (fn-bs-fencedp (bsk6-file-cut) (fn-bs-next-ino (bsk6-start)))
      (equal (fn-bs-durable-content
              (bsk6-file-cut) (fn-bs-next-ino (bsk6-start)))
             (bsk5-frame-2))
      (equal (fn-bs-durable-records (bsk6-file-cut))
             (list *bsk5-record*))))

; An already occupied staging name stops at O_EXCL, before any write/fence.
(assert-event
 (fn-bs-lookup (car (bsk5-linked-2)) :staging ".stage-k5-2"))
(must-fail
 (assert-event
  (let* ((bs (car (bsk5-linked-2)))
         (cut (car (nth 5 (fn-bs-run
                           bs (cdr (bsk5-linked-2))
                           (fn-bs-record-program ".stage-k5-2"
                                                 (fn-bs-txn-name 1)
                                                 (bsk5-frame-2))
                           nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content cut (fn-bs-next-ino bs))
           (bsk5-frame-2)))))

; A non-list is not an octet frame.  write-all accepts zero octets, so the
; file-fence cut cannot equal that malformed argument.
(must-fail
 (assert-event
  (let* ((bs (bsk6-start))
         (cut (car (nth 5 (fn-bs-run
                           bs (cdr (bsk5-frontier-2))
                           (fn-bs-record-program ".stage-k6-atom"
                                                 (fn-bs-txn-name 1) 65)
                           nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content cut (fn-bs-next-ino bs)) 65))))

; The state invariant excludes a stale pending write to the unallocated
; next inode.  If admitted, that write can leave trailing bytes after the
; shorter new frame even though the new write and fsync succeed.
(defun bsk6-invalid-pending-write ()
  (let ((bs (bsk6-start)))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (append (fn-bs-pending bs)
                        (list (list :write (fn-bs-next-ino bs) 0 '(99 88))))
                (fn-bs-next-ino bs))))
(assert-event
 (not (fn-bs-statep (bsk6-invalid-pending-write))))
(must-fail
 (assert-event
  (let* ((bs (bsk6-invalid-pending-write))
         (cut (car (nth 5 (fn-bs-run
                           bs (cdr (bsk5-frontier-2))
                           (fn-bs-record-program ".stage-k6-bad-state"
                                                 (fn-bs-txn-name 1) '(65))
                           nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content cut (fn-bs-next-ino bs)) '(65)))))
