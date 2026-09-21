(in-package "ACL2")
(include-book "../../books/byte-store-compaction-correspondence")
(include-book "../../books/byte-store-frame")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bscc-names*
  (list "00000000000000000001.txn" "00000000000000000003.txn" "00000000000000000004.txn"))
(assert-event
 (equal (fn-bs-pack-reclaim-plan *bscc-names* 8 4)
        (list "00000000000000000001.txn" "00000000000000000003.txn")))

; Total accessors keep malformed nested observations safe, and the public
; actual-call subject rejects a malformed nested namespace rather than
; returning any pathname for the host to unlink.
(assert-event
 (equal (fn-bs-pack-covered-names '((bad) nil atom) 4)
        '(nil nil nil)))
(assert-event
 (equal (fn-bs-pack-reclaim-plan
         (list (list "00000000000000000000.txn") "00000000000000000004.txn") 8 4)
        :invalid))
(assert-event
 (equal (fn-bs-pack-reclaim-program
         (list (list "00000000000000000000.txn") "00000000000000000004.txn") 8 4)
        nil))
(assert-event
 (equal (fn-bs-pack-reclaim-program *bscc-names* 8 4)
        (list (list :unlink :transactions "00000000000000000001.txn")
              (list :cut "pack-reclaim-unlink")
              (list :unlink :transactions "00000000000000000003.txn")
              (list :cut "pack-reclaim-unlink")
              (list :fsync-dir :transactions)
              (list :cut "pack-reclaim-directory"))))

; Concrete byte namespace with arbitrary already-missing covered names 0 and 2,
; exact surviving covered names 1 and 3, and the required suffix at 4.
(defconst *bscc-store*
  (fn-bs-make 4
             (list (cons 11 '(11)) (cons 13 '(13)) (cons 14 '(14)))
             (list (cons :transactions
                         (list (cons "00000000000000000001.txn" 11)
                               (cons "00000000000000000003.txn" 13)
                               (cons "00000000000000000004.txn" 14))))
             nil 15))
(defun fn-bs-test-reclaim-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-run *bscc-store* (fn-sf-initial-state)
             (fn-bs-pack-reclaim-program *bscc-names* 8 4)
             nil nil nil))

; First post-unlink cut: the view has removed name 1, while crash choice
; :drop retains it and :apply removes it.  Both preserve the suffix name 4.
(assert-event
 (let ((bs (car (nth 1 (fn-bs-test-reclaim-run)))))
   (and (member-equal "00000000000000000001.txn"
                      (fn-bs-durable-names bs :transactions))
        (not (member-equal "00000000000000000001.txn"
                           (fn-bs-names (fn-bs-crash bs '(:apply)) :transactions)))
        (member-equal "00000000000000000001.txn"
                      (fn-bs-names (fn-bs-crash bs '(:drop)) :transactions))
        (member-equal "00000000000000000004.txn"
                      (fn-bs-names (fn-bs-crash bs '(:apply)) :transactions)))))

; After the directory fence, no crash choice can restore either reclaimed
; covered name; the uncovered suffix remains.
(assert-event
 (let ((bs (car (nth 5 (fn-bs-test-reclaim-run)))))
   (and (fn-bs-dir-quietp bs :transactions)
        (not (member-equal "00000000000000000001.txn" (fn-bs-names bs :transactions)))
        (not (member-equal "00000000000000000003.txn" (fn-bs-names bs :transactions)))
        (member-equal "00000000000000000004.txn" (fn-bs-names bs :transactions)))))

; A conflicting surviving covered name is rejected by the selected-pack
; recovery subject rather than hidden by an otherwise valid suffix.
(assert-event
 (equal (fn-cc-recover-observation
         (fn-cc-make 2 2 '((10) (11)))
         '((0 (99)) (2 (12))) 3)
        '(:error :conflict)))

(must-fail
 (assert-event
  (equal (fn-bs-pack-reclaim-plan
          (list "00000000000000000001.txn" "00000000000000000005.txn") 8 4)
         (list "00000000000000000001.txn"))))

; A nonempty actual-plan prefix has issued the unlink of covered sequence 1.
; Both losing that unlink and applying it preserve uncovered sequence 4's
; inode and exact octets through the modeled crash.
(defun fn-bs-test-reclaim-cut (limit)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-prefix-state
   *bscc-store* (fn-sf-initial-state)
   (fn-bs-pack-reclaim-program *bscc-names* 8 4)
   limit nil nil))

(assert-event
 (let* ((before *bscc-store*)
        (cut (fn-bs-test-reclaim-cut 2))
        (ino (fn-bs-lookup before :transactions
                           "00000000000000000004.txn"))
        (drop (fn-bs-crash cut '(:drop)))
        (apply (fn-bs-crash cut '(:apply))))
   (and (equal (fn-bs-durable-entry drop :transactions
                                    "00000000000000000004.txn") ino)
        (equal (fn-bs-durable-entry apply :transactions
                                    "00000000000000000004.txn") ino)
        (equal (fn-bs-durable-content drop ino) (fn-bs-content before ino))
        (equal (fn-bs-durable-content apply ino) (fn-bs-content before ino)))))

; The unplanned-name premise has teeth: applying the issued unlink destroys
; covered sequence 1, so the same conclusion is false for that planned name.
(must-fail
 (assert-event
  (let* ((before *bscc-store*)
         (cut (fn-bs-test-reclaim-cut 2))
         (image (fn-bs-crash cut '(:apply))))
    (equal (fn-bs-durable-entry image :transactions
                                "00000000000000000001.txn")
           (fn-bs-lookup before :transactions
                         "00000000000000000001.txn")))))

; Writer ownership is essential.  With a pre-existing pending replacement of
; suffix 4, the process view names inode 13 while the drop crash restores the
; durable inode 14; reclaim itself did not target suffix 4.
(defconst *bscc-foreign-writer-store*
  (fn-bs-make 4
              (list (cons 13 '(13)) (cons 14 '(14)))
              (list (cons :transactions
                          (list (cons "00000000000000000004.txn" 14))))
              (list (list :set-entry :transactions
                          "00000000000000000004.txn" 13))
              15))

(must-fail
 (assert-event
  (let* ((before *bscc-foreign-writer-store*)
         (cut (fn-bs-prefix-state
               before (fn-sf-initial-state)
               (fn-bs-pack-reclaim-program
                (list "00000000000000000004.txn") 8 4)
               0 nil nil))
         (image (fn-bs-crash cut '(:drop))))
    (equal (fn-bs-durable-entry image :transactions
                                "00000000000000000004.txn")
           (fn-bs-lookup before :transactions
                         "00000000000000000004.txn")))))
