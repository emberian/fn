(in-package "ACL2")
(include-book "../../books/history-event-directory-refinement")
(defconst *hedt-leaf0* '(:history-leaf 0 11 0 1 0))
(defconst *hedt-leaf1* '(:history-leaf 1 12 0 1 256))
(defconst *hedt-leaf2* '(:history-leaf 2 13 0 1 512))
(defconst *hedt-forest3*
 (list (list :history-block 1 0 *hedt-leaf2*)
       (list :history-block 2 1 (list :history-branch *hedt-leaf0* *hedt-leaf1*))))
(defun hedt-read-result (cursor)
 (declare (xargs :guard t))
 (mv-let (word next leaf) (fn-hed-read-step cursor) (list word next leaf)))
; Actual growth witness: one merge/pop each call, then one final cons. Old
; captured forest remains the same object/value and chronological prefix.
(assert-event
 (let* ((leaf3 '(:history-leaf 3 14 0 1 768))
        (c0 (fn-hed-grow-begin *hedt-forest3* 3 1 leaf3))
        (c1 (fn-hed-grow-step c0)) (c2 (fn-hed-grow-step c1)) (c3 (fn-hed-grow-step c2)))
  (and (fn-hed-leafp leaf3) (natp 3) (natp 1)
       (fn-hed-fixedp c0 7) (eq (fn-hed-at 0 c0) :history-grow)
       (equal (fn-hed-at 3 c1) (cdr *hedt-forest3*))
       (equal (fn-hed-at 3 c2) nil)
       (eq (fn-hed-at 1 c2) :carry) (eq (fn-hed-at 1 c3) :done)
       (equal (fn-hed-grow-alpha c0) (append (fn-hed-forest-flat *hedt-forest3*) (list leaf3)))
       (equal (fn-hed-grow-alpha c1) (fn-hed-grow-alpha c0))
       (equal (fn-hed-grow-alpha c2) (fn-hed-grow-alpha c1))
       (equal (fn-hed-grow-alpha c3) (fn-hed-grow-alpha c2))
       (equal (fn-hed-forest-flat *hedt-forest3*) (list *hedt-leaf0* *hedt-leaf1* *hedt-leaf2*))
       (equal (fn-hed-at 1 (car (fn-hed-at 6 c3))) 4))))
; Lookup ordinal256 selects page1: skip newest block, convert newest offset
; to chronological offset, take newer branch, then exact leaf.
(assert-event
 (let* ((c0 (fn-hed-read-begin *hedt-forest3* 3 256))
        (r1 (hedt-read-result c0)) (c1 (mv-nth 1 r1))
        (r2 (hedt-read-result c1)) (c2 (mv-nth 1 r2))
        (r3 (hedt-read-result c2)) (c3 (mv-nth 1 r3))
        (r4 (hedt-read-result c3)))
  (and (fn-hed-fixedp c0 8) (eq (fn-hed-at 0 c0) :history-read)
       (eq (mv-nth 0 r1) :yield) (equal (fn-hed-at 2 c1) (cdr *hedt-forest3*))
       (eq (mv-nth 0 r2) :yield) (equal (fn-hed-at 5 c2) 1)
       (eq (mv-nth 0 r3) :yield) (equal (fn-hed-at 3 c3) *hedt-leaf1*)
       (equal (fn-hed-read-alpha c0) *hedt-leaf1*)
       (equal (fn-hed-read-alpha c1) (fn-hed-read-alpha c0))
       (equal (fn-hed-read-alpha c2) (fn-hed-read-alpha c1))
       (equal (fn-hed-read-alpha c3) (fn-hed-read-alpha c2))
       (equal (mv-nth 0 r4) :leaf) (fn-hed-leafp (mv-nth 2 r4))
       (equal (mv-nth 2 r4) (fn-hed-read-alpha c3)))))
; Corrupted metadata, not an ordinary exhaustion witness.
(assert-event
 (let ((cursor '(:history-read :tree nil (:history-branch :old :new) 3 1 0 0)))
  (equal (hedt-read-result cursor) (list :recovery-required cursor nil))))
(assert-event
 (let ((cursor (fn-hed-read-begin *hedt-forest3* 3 768)))
  (equal (hedt-read-result cursor) (list :range cursor nil))))
