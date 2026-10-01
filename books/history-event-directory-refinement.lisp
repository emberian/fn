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

(defun fn-hed-balanced-treep (tree width)
 (declare (xargs :guard t :measure (acl2-count tree)))
 (if (equal width 1) (fn-hed-leafp tree)
  (and (posp width) (< 1 width) (evenp width) (fn-hed-branchp tree)
       (fn-hed-balanced-treep (cadr tree) (floor width 2))
       (fn-hed-balanced-treep (caddr tree) (floor width 2)))))
(defun fn-hed-forest-widthsp (forest)
 (declare (xargs :guard t))
 (if (atom forest) (null forest)
  (and (fn-hed-blockp (car forest))
       (fn-hed-balanced-treep (fn-hed-at 3 (car forest)) (fn-hed-at 1 (car forest)))
       (fn-hed-forest-widthsp (cdr forest)))))
(local (defthm fn-hed-len-append
 (equal (len (append xs ys)) (+ (len xs) (len ys)))))
(local (defthm fn-hed-balanced-tree-flat-width
 (implies (fn-hed-balanced-treep tree width)
          (equal (len (fn-hed-tree-flat tree)) width))
 :hints (("Goal" :do-not '(generalize) :induct (fn-hed-balanced-treep tree width)
                 :in-theory (enable fn-hed-balanced-treep fn-hed-tree-flat
                                     fn-hed-leafp fn-hed-branchp fn-hed-at fn-hed-fixedp)))))
(local (defthm fn-hed-nth-append-before
 (implies (and (natp n) (< n (len xs)))
          (equal (nth n (append xs ys)) (nth n xs)))
 :hints (("Goal" :induct (nth n xs) :in-theory (enable nth binary-append len)))))
(local (defthm fn-hed-nth-append-after
 (implies (and (natp n) (<= (len xs) n))
          (equal (nth n (append xs ys)) (nth (- n (len xs)) ys)))
 :hints (("Goal" :induct (nth n xs) :in-theory (enable nth binary-append len)))))
(defthm fn-hed-tree-select-refines-chronological-flat
 (implies (and (fn-hed-balanced-treep tree width) (natp offset) (< offset width))
  (equal (fn-hed-tree-select tree width offset) (nth offset (fn-hed-tree-flat tree))))
 :hints (("Goal" :induct (fn-hed-tree-select tree width offset)
                 :in-theory (e/d (fn-hed-tree-select fn-hed-balanced-treep fn-hed-tree-flat
                                      fn-hed-leafp fn-hed-branchp fn-hed-fixedp)
                                 (nth binary-append len)))))
(defthm fn-hed-forest-select-refines-chronological-flat
 (implies (and (fn-hed-forest-widthsp forest) (natp fromend)
                (< fromend (len (fn-hed-forest-flat forest))))
  (equal (fn-hed-forest-select forest fromend)
         (nth (- (- (len (fn-hed-forest-flat forest)) 1) fromend)
              (fn-hed-forest-flat forest))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-hed-forest-select forest fromend) :do-not '(generalize)
                 :in-theory (e/d (fn-hed-forest-select fn-hed-forest-widthsp fn-hed-forest-flat)
                                  (fn-hed-tree-select fn-hed-balanced-treep nth binary-append len)))))
(defthm fn-hed-read-begin-refines-chronological-page
 (implies (and (fn-hed-forest-widthsp forest) (natp pagecount) (natp ordinal)
                (equal pagecount (len (fn-hed-forest-flat forest)))
                (< (floor ordinal 256) pagecount))
  (equal (fn-hed-read-alpha (fn-hed-read-begin forest pagecount ordinal))
         (nth (floor ordinal 256) (fn-hed-forest-flat forest))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-hed-forest-select-refines-chronological-flat
                        (fromend (- (- pagecount 1) (floor ordinal 256)))))
                 :in-theory (e/d (fn-hed-read-alpha fn-hed-read-begin fn-hed-at)
                                  (fn-hed-forest-select fn-hed-forest-flat fn-hed-forest-widthsp nth)))))
(defthm fn-hed-grow-merge-pops-one-forest-cell
 (implies (and (fn-hed-fixedp cursor 7) (eq (fn-hed-at 0 cursor) :history-grow)
                (eq (fn-hed-at 1 cursor) :carry)
                (eq (fn-hed-at 1 (fn-hed-grow-step cursor)) :carry))
  (equal (fn-hed-at 3 (fn-hed-grow-step cursor)) (cdr (fn-hed-at 3 cursor))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hed-grow-step fn-hed-at))))
(defun fn-hed-read-work (cursor)
 (declare (xargs :guard t))
 (if (eq (fn-hed-at 1 cursor) :forest) (acl2-count (fn-hed-at 2 cursor))
  (acl2-count (fn-hed-at 3 cursor))))
(defthm fn-hed-read-yield-makes-structural-progress
 (implies (equal (mv-nth 0 (fn-hed-read-step cursor)) :yield)
  (< (fn-hed-read-work (mv-nth 1 (fn-hed-read-step cursor))) (fn-hed-read-work cursor)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :do-not '(generalize)
                 :in-theory (enable fn-hed-read-step fn-hed-read-work fn-hed-at
                                     fn-hed-blockp fn-hed-branchp fn-hed-fixedp))))
