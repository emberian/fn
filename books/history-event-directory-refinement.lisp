; Logical lookup model and the actual one-cell/one-branch cursor boundary.
; These model traversals are proof-only, never a served recognizer or guard.
(in-package "ACL2")
(include-book "history-event-directory")
(local (include-book "arithmetic-5/top" :dir :system))
(local (defthm fn-hed-at1-is-cadr (equal (fn-hed-at 1 x) (cadr x))))
(local (defthm fn-hed-at2-is-caddr (equal (fn-hed-at 2 x) (caddr x))))
(defun fn-hed-tree-select (tree width offset)
 (declare (xargs :guard t :measure (acl2-count tree)))
 (cond ((not (and (posp width) (natp offset) (< offset width))) nil)
       ((equal width 1) (if (fn-hed-leafp tree) tree nil))
       ((not (and (evenp width) (fn-hed-branchp tree))) nil)
       (t (let ((half (floor width 2)))
           (if (< offset half)
            (fn-hed-tree-select (cadr tree) half offset)
            (fn-hed-tree-select (caddr tree) half (- offset half)))))))
(defun fn-hed-forest-select (forest fromend)
 (declare (xargs :guard t))
 (if (not (and (consp forest) (fn-hed-blockp (car forest)) (natp fromend))) nil
  (let ((width (fn-hed-at 1 (car forest))))
   (if (<= width fromend) (fn-hed-forest-select (cdr forest) (- fromend width))
    (fn-hed-tree-select (fn-hed-at 3 (car forest)) width (- (- width 1) fromend))))))
(defun fn-hed-read-alpha (cursor)
 (declare (xargs :guard t))
 (case (fn-hed-at 1 cursor)
  (:forest (fn-hed-forest-select (fn-hed-at 2 cursor) (fn-hed-at 5 cursor)))
  ((:tree :leaf) (fn-hed-tree-select (fn-hed-at 3 cursor) (fn-hed-at 4 cursor)
                                    (fn-hed-at 5 cursor)))
  (otherwise nil)))
(defthm fn-hed-read-step-preserves-exact-selected-page
 (implies (and (fn-hed-fixedp cursor 8) (eq (fn-hed-at 0 cursor) :history-read))
  (equal (fn-hed-read-alpha (mv-nth 1 (fn-hed-read-step cursor)))
         (fn-hed-read-alpha cursor)))
 :rule-classes nil
 :hints (("Goal" :do-not '(generalize) :do-not-induct t
                :in-theory (enable fn-hed-read-step fn-hed-read-alpha
                         fn-hed-forest-select fn-hed-tree-select fn-hed-at
                         fn-hed-branchp fn-hed-fixedp))))
(defthm fn-hed-read-leaf-is-complete-selected-result
 (implies (equal (mv-nth 0 (fn-hed-read-step cursor)) :leaf)
  (and (equal (mv-nth 2 (fn-hed-read-step cursor)) (fn-hed-read-alpha cursor))
       (fn-hed-leafp (mv-nth 2 (fn-hed-read-step cursor)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hed-read-step fn-hed-read-alpha fn-hed-tree-select fn-hed-at))))
