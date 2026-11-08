(in-package "ACL2")
(include-book "../books/arms")
(defcolumns fn2-view-fixture ((left :u32) (right :u32)))
(fn2-defview fn2-test-left-view :carrier fn2-view-fixture
  :select ((fn2-view-fixture :columns (left) :rows t :scalars (rows))))
(fn2-defview fn2-test-row-view :carrier fn2-view-fixture :parameters (row)
  :select ((fn2-view-fixture :columns (left right) :rows (:one row))))
(fn2-defview fn2-test-range-view :carrier fn2-view-fixture :parameters (start count)
  :select ((fn2-view-fixture :columns (left) :rows (:range start count))))
(assert-event (and (fn2-test-left-view '((1 2) (9 8) 2) '((1 2) (3 4) 2))
                   (not (fn2-test-left-view '((1 2) (9 8) 3) '((1 2) (3 4) 2)))))
(assert-event (and (fn2-footprint '((1 0)) '((1 2) (3 4) 2) '((1 2) (9 4) 2))
                   (fn2-view-protected '((0) (2)) '((1 0)))
                   (fn2-test-left-view '((1 2) (9 4) 2) '((1 2) (3 4) 2))))
(assert-event (and (fn2-test-row-view 1 '((9 2) (7 4) 2) '((1 2) (3 4) 2))
                   (fn2-test-range-view 1 1 '((9 2) (7 4) 2) '((1 2) (3 4) 2))
                   (not (fn2-test-range-view 0 2 '((9 2) (7 4) 2) '((1 2) (3 4) 2)))))
; Whole-child permission does not protect its cardinality or any of its cells.
(assert-event (and (not (fn2-view-path-protected '(0 2) '((0))))
                   (not (fn2-view-path-protected '(0) '((0 2))))
                   (fn2-view-path-protected '(1 2) '((0)))))

; A producer proves one footprint. Its consumers choose views independently.
(defthm fn2-test-right-footprint
  (fn2-footprint (list (list 1 i)) c (fn2-view-fixture-set-right i v c))
  :hints (("Goal" :in-theory (e/d (fn2-view-fixture-set-right update-fn2-view-fixture-right$ai
                                  update-nth-array fn2-footprint-write fn2-view-nth-nfix)
                                 (nth update-nth (:d nfix)))
           :use ((:instance fn2-footprint-of-write (path (list 1 i)) (value v) (core c))))))
(defthm fn2-test-left-consumer
  (fn2-test-left-view (fn2-view-fixture-set-right i v c) c)
  :hints (("Goal" :in-theory (enable fn2-view-protected fn2-view-path-protected fn2-view-path-disjoint)
           :use ((:instance fn2-test-left-view-of-footprint
                    (footprint (list (list 1 i))) (a c) (b (fn2-view-fixture-set-right i v c)))))))
(defun fn2-view-fixture-root (c)
  (declare (xargs :verify-guards nil))
  (if (< 0 (nth 2 c)) (list t (nfix (nth 0 (nth 0 c))) (nfix (nth 0 (nth 1 c))))
    (list nil 0 0)))
(fn2-defview fn2-test-root-view :carrier fn2-view-fixture
  :select ((fn2-view-fixture :columns (left right) :rows (:one 0) :scalars (rows)))
  :observe fn2-view-fixture-root :open (fn2-view-fixture-root))
; Observational equality is deliberately weaker than equality of raw cells.
(defthm fn2-test-root-normalization
  (and (fn2-test-root-view '((bad) (-1) 1) '((0) (0) 2))
       (not (fn2-test-row-view 0 '((bad) (-1) 1) '((0) (0) 2))))
  :hints (("Goal" :in-theory (enable fn2-test-root-view fn2-test-row-view fn2-view-equal
                                     fn2-view-project fn2-view-at))))

; A column footprint permits several rows, while retaining cardinality.
(assert-event
 (let ((a '(ctl ((1 2) (3 4) 2) old))
       (b '(ctl ((1 2) (8 9) 2) new)))
  (and (fn2-column-frame 1 '(1) '(2) a b)
       (fn2-view-columns-protected '((1 0) (1 2) (0)) 1 '(1) '(2))
       (equal (fn2-view-project '((1 0) (1 2) (0)) a)
              (fn2-view-project '((1 0) (1 2) (0)) b)))))
; Whole-child permission cannot preserve the table's row count.
(assert-event
 (let ((a '(ctl ((1 2) (3 4) 2) old))
       (b '(ctl ((1 2) (8 9) 3) new)))
  (and (fn2-column-frame 1 '(1) '(1 2) a b)
       (not (fn2-column-frame 1 '(1) '(2) a b))
       (not (fn2-view-columns-protected '((1 2)) 1 '(1) '(1 2))))))
; Intersect independent bounds: the row frame may permit extra children;
; the composed footprint proves those children did not change.
(assert-event
 (let ((a '(ctl ((1 2) (3 4) 2) old))
       (b '(ctl ((1 2) (8 4) 2) new)))
  (and (fn2-column-frame 1 '(1) '(1 2) a b)
       (fn2-arm-row-frame 1 0 '(1) '(2 55) a b)
       (not (member-equal 1 '(2 55))) (subsetp-equal '(1) '(1))
       (fn2-column-frame 1 '(1) '(2) a b))))
; Remove the row premise: the composed footprint alone permits an
; observed column to change, so the refined conclusion is false.
(assert-event
 (let ((a '(ctl ((1 2) (3 4) 2) old))
       (b '(ctl ((9 2) (3 4) 2) new)))
  (and (fn2-column-frame 1 '(1) '(1 2) a b)
       (not (fn2-arm-row-frame 1 0 '(1) '(2 55) a b))
       (not (fn2-column-frame 1 '(1) '(2) a b)))))
