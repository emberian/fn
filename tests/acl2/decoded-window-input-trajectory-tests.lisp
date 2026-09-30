; Complete literal teeth for actual refilled stored canonical answer.
; Fixed1024 and input64+6 positive exercises actual STORED-CHUNK guards.
; No installed native holder/provider, source authority or demand is inferred.
; Empty input is a logical wrapper case: actual controller BEGIN uses :drain.
; MORE removal forces refill afterFULL and discards unread source bytes.
; Zero-request removal is the general wrapper API, not a fixed1024 tick claim.
(in-package "ACL2")
(include-book "../../books/decoded-window-input-trajectory")

(defun-nx fn-pwie-refilled-canonical-case (dict a c n requested1 requested2)
  (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) nil nil nil))
         (compressed (len (append a c))) (budget (fn-pzd-budget compressed n))
         (r1 (fn-pzw-stored-chunk requested1 budget 0 (len a) compressed n
               (car init) a (mv-nth 1 init) (mv-nth 2 init) nil))
         (left (fn-pzw-budget-left requested1 budget (mv-nth 1 r1)))
         (r2 (fn-pzw-stored-chunk requested2 left 0 (len c) compressed n
               (mv-nth 3 r1) c (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
         (out (append (mv-nth 6 r1) (mv-nth 6 r2)))
         (old (fn-pzd-decode dict (append a c) n))
         (new (if (and (zp n) (atom (append a c))) (list :ok nil)
                (fn-pzd-answer (fn-zin-stored-status (car r2) compressed (mv-nth 3 r2)) out n))))
   (list r1 r2 out old new)))

(local
 (defthm pwd-input-fixed-quantum-refill-positive
  (let* ((wire (fn-pzd-stored (make-list 65 :initial-element 65)))
         (a (take 64 wire)) (c (nthcdr 64 wire))
         (case (fn-pwie-refilled-canonical-case '(65 66) a c 65 1024 1024))
         (r1 (car case)) (r2 (cadr case)))
   (and (equal (car r1) :more) (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (equal (nth 3 case) (nth 4 case))
        (equal (nth 4 case) (list :ok (make-list 65 :initial-element 65)))
        (equal (len a) 64) (equal (len c) 6) (equal (mv-nth 2 r1) 64) (equal (mv-nth 2 r2) 6)
        (equal (len (mv-nth 6 r1)) 59) (equal (len (mv-nth 6 r2)) 6)
        (equal (fn-zin-tin (mv-nth 3 r2)) 70) (equal (fn-zin-tout (mv-nth 3 r2)) 65)))
  :rule-classes nil))

(local
 (defthm pwd-input-header-cut-positive
  (let* ((wire (fn-pzd-stored '(65 66)))
         (case (fn-pwie-refilled-canonical-case nil (take 1 wire) (nthcdr 1 wire) 2 1024 1024))
         (r1 (car case)) (r2 (cadr case)))
   (and (equal (car r1) :more) (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (equal (nth 3 case) (nth 4 case)) (equal (nth 4 case) '(:ok (65 66)))))
  :rule-classes nil))

(local
 (defthm pwd-input-empty-wrapper-positive
  (let* ((case (fn-pwie-refilled-canonical-case nil nil nil 0 1024 1024))
         (r1 (car case)) (r2 (cadr case)))
   (and (equal (car r1) :more) (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (equal (nth 3 case) (nth 4 case)) (equal (nth 4 case) '(:ok nil))))
  :rule-classes nil))
(local
 (defthm fn-pwie-more-premise-complete-removal
  (let* ((case (fn-pwie-refilled-canonical-case nil '(115 116 164 16 0 0) nil 65 1024 1024))
         (r1 (car case)) (r2 (cadr case)))
   (and (not (equal (car r1) :more))
        (not (equal (car r2) :yield)) (not (equal (car r2) :full))
        (not (equal (nth 3 case) (nth 4 case)))))
  :rule-classes nil))

(local
 (defthm fn-pwie-nonyield-premise-complete-removal
  (let* ((wire (fn-pzd-stored (make-list 65 :initial-element 65)))
         (case (fn-pwie-refilled-canonical-case nil (take 64 wire) (nthcdr 64 wire) 65 1024 0))
         (r1 (car case)) (r2 (cadr case)))
   (and (equal (car r1) :more) (equal (car r2) :yield)
        (not (equal (car r2) :full)) (not (equal (nth 3 case) (nth 4 case)))))
  :rule-classes nil))

(local
 (defthm fn-pwie-nonfull-premise-complete-removal
  (let* ((wire (fn-pzd-stored (make-list 130 :initial-element 65)))
         (case (fn-pwie-refilled-canonical-case nil (take 64 wire) (take 64 (nthcdr 64 wire)) 130 1024 1024))
         (r1 (car case)) (r2 (cadr case)))
   (and (equal (car r1) :more) (not (equal (car r2) :yield))
        (equal (car r2) :full) (not (equal (nth 3 case) (nth 4 case)))))
  :rule-classes nil))
