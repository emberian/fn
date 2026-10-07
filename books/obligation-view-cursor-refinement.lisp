(in-package "ACL2")
(include-book "obligation-view-cursor")
(include-book "view-delta-cursor-refinement")

; Only the proof reads these whole denotations. The served step calls neither.
(defun fn-ovc-reference (op subject charge view)
 (declare (xargs :guard t))
 (let ((count (if (consp view) (nfix (car view)) 0))
       (trie (if (consp view) (cdr view) nil)))
  (cond ((eq op :same) view)
        ((eq op :arrival) (cons (+ 1 count) (fn-vdc-bump subject charge trie)))
        ((eq op :release) (cons (nfix (- count 1)) (fn-vdc-unbump subject charge trie)))
        (t nil))))
(defun fn-ovc-meaning (c)
 (declare (xargs :guard t))
 (if (eq (fn-vcu-at 0 c) :drive)
  (cons (fn-vcu-at 1 c) (fn-vcu-meaning (fn-vcu-at 2 c)))
  (fn-vcu-at 3 c)))
(local (defthm fn-ovc-child-done-meaning-by-definition
 (implies (eq (fn-vcu-at 0 c) :done)
  (equal (fn-vcu-meaning c) (fn-vcu-at 6 c)))
 :hints (("Goal" :in-theory (enable fn-vcu-meaning)))))
(defthm fn-ovc-step-preserves-full-view
 (equal (fn-ovc-meaning (fn-ovc-step c)) (fn-ovc-meaning c))
 :hints (("Goal" :in-theory (e/d (fn-ovc-step fn-ovc-meaning fn-vcu-at)
              (fn-vcu-step fn-vcu-meaning fn-vcu-step-preserves-complete-update))
          :use ((:instance fn-vcu-step-preserves-complete-update
                   (c (fn-vcu-at 2 c)))))))
(defthm fn-ovc-drive-preserves-full-view
 (equal (fn-ovc-meaning (mv-nth 0 (fn-ovc-drive c fuel))) (fn-ovc-meaning c))
 :hints (("Goal" :induct (fn-ovc-drive c fuel)
          :in-theory (e/d (fn-ovc-drive)
             (fn-ovc-step fn-vcu-at fn-ovc-meaning)))))
(local (defthm fn-ovc-begin-meaning-unfolds
 (equal (fn-ovc-meaning (fn-ovc-begin op subject charge view))
        (fn-ovc-reference op subject charge view))
 :hints (("Goal" :in-theory (e/d (fn-ovc-meaning fn-ovc-begin fn-ovc-reference fn-vcu-at)
            (fn-vcu-meaning fn-vcu-begin fn-vdc-bump fn-vdc-unbump))))))
(local (defthm fn-ovc-done-meaning-by-definition
 (implies (eq (fn-vcu-at 0 c) :done)
  (equal (fn-ovc-meaning c) (fn-vcu-at 3 c)))
 :hints (("Goal" :in-theory (enable fn-ovc-meaning)))))
(defthm fn-ovc-completed-is-full-view-delta
 (implies (eq (fn-vcu-at 0 (mv-nth 0 (fn-ovc-drive
                  (fn-ovc-begin op subject charge view) fuel))) :done)
  (equal (fn-ovc-result (mv-nth 0 (fn-ovc-drive
            (fn-ovc-begin op subject charge view) fuel)))
         (list :done (fn-ovc-reference op subject charge view))))
 :hints (("Goal" :in-theory (e/d (fn-ovc-result)
           (fn-ovc-drive fn-ovc-begin fn-vcu-at fn-ovc-meaning fn-ovc-reference
            fn-ovc-drive-preserves-full-view fn-ovc-begin-meaning-unfolds))
          :use ((:instance fn-ovc-drive-preserves-full-view
                  (c (fn-ovc-begin op subject charge view)))
                (:instance fn-ovc-begin-meaning-unfolds)))))
