(in-package "ACL2")
(include-book "../../books/byte-store-compaction-correspondence")
(include-book "../../books/byte-store-frame")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bscc-names*
  (list (fn-bs-txn-name 1) (fn-bs-txn-name 3) (fn-bs-txn-name 4)))
(defconst *bscc-plan* (fn-bs-pack-reclaim-plan *bscc-names* 8 4))
(assert-event
 (equal *bscc-plan* (list (fn-bs-txn-name 1) (fn-bs-txn-name 3))))
(assert-event
 (equal (fn-bs-pack-reclaim-program *bscc-names* 8 4)
        (list (list :unlink :transactions (fn-bs-txn-name 1))
              (list :cut "pack-reclaim-unlink")
              (list :unlink :transactions (fn-bs-txn-name 3))
              (list :cut "pack-reclaim-unlink")
              (list :fsync-dir :transactions)
              (list :cut "pack-reclaim-directory"))))

; Concrete byte namespace with arbitrary already-missing covered names 0 and 2,
; exact surviving covered names 1 and 3, and the required suffix at 4.
(defconst *bscc-store*
  (fn-bs-make 4
             (list (cons 11 '(11)) (cons 13 '(13)) (cons 14 '(14)))
             (list (cons :transactions
                         (list (cons (fn-bs-txn-name 1) 11)
                               (cons (fn-bs-txn-name 3) 13)
                               (cons (fn-bs-txn-name 4) 14))))
             nil 15))
(defconst *bscc-run*
  (fn-bs-run *bscc-store* (fn-sf-initial-state)
             (fn-bs-pack-reclaim-program *bscc-names* 8 4)
             nil nil nil))

; First post-unlink cut: the view has removed name 1, while crash choice
; :drop retains it and :apply removes it.  Both preserve the suffix name 4.
(assert-event
 (let ((bs (car (nth 1 *bscc-run*))))
   (and (member-equal (fn-bs-txn-name 1)
                      (fn-bs-durable-names bs :transactions))
        (not (member-equal (fn-bs-txn-name 1)
                           (fn-bs-names (fn-bs-crash bs '(:apply)) :transactions)))
        (member-equal (fn-bs-txn-name 1)
                      (fn-bs-names (fn-bs-crash bs '(:drop)) :transactions))
        (member-equal (fn-bs-txn-name 4)
                      (fn-bs-names (fn-bs-crash bs '(:apply)) :transactions)))))

; After the directory fence, no crash choice can restore either reclaimed
; covered name; the uncovered suffix remains.
(assert-event
 (let ((bs (car (nth 5 *bscc-run*))))
   (and (fn-bs-dir-quietp bs :transactions)
        (not (member-equal (fn-bs-txn-name 1) (fn-bs-names bs :transactions)))
        (not (member-equal (fn-bs-txn-name 3) (fn-bs-names bs :transactions)))
        (member-equal (fn-bs-txn-name 4) (fn-bs-names bs :transactions)))))

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
          (list (fn-bs-txn-name 1) (fn-bs-txn-name 5)) 8 4)
         (list (fn-bs-txn-name 1)))))
