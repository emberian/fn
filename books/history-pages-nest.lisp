; fn: block replacements nest and commute (lane arena-store-3, 2026-09-28).
; Prefix fn-hp-.  Generic facts over `fn-hp-rep' and `fn-hp-wreps' the
; placed writer (books/history-pages-placed-write.lisp) is proved from.
(in-package "ACL2")
(include-book "history-pages-placed")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite pgs-x-nfix-when-natp))))

(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; A. Replacements nest and commute.

(local
 (defthm fn-hp-nth-past-len
   (implies (and (natp k) (<= (len x) k)) (equal (nth k x) nil))
   :hints (("Goal" :in-theory (enable nth)))))

(defun fn-hp-agree-ind (a n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) (list a n) (fn-hp-agree-ind (+ 1 (nfix a)) (1- n))))

(defthm fn-hp-rep-nest-nth
  (implies (and (natp k) (natp j) (natp o) (<= (+ o (len d)) (len x)))
           (equal (nth k (fn-hp-rep w j (fn-hp-rep x o d)))
                  (nth k (fn-hp-rep (fn-hp-rep w j x) (+ j o) d))))
  :hints (("Goal" :in-theory (disable fn-hp-rep))))

(defthm fn-hp-rep-nest-agree
  (implies (and (natp a) (natp j) (natp o) (<= (+ o (len d)) (len x)))
           (fn-hp-agree a n (fn-hp-rep w j (fn-hp-rep x o d)) (fn-hp-rep (fn-hp-rep w j x) (+ j o) d)))
  :hints (("Goal" :induct (fn-hp-agree-ind a n) :in-theory (disable fn-hp-rep fn-hp-rep-nest-nth))
          ("Subgoal *1/2" :use ((:instance fn-hp-rep-nest-nth (k a))))))

(defthm fn-hp-rep-nest
  (implies (and (natp j) (natp o) (true-listp w) (<= (+ o (len d)) (len x)) (<= (+ j (len x)) (len w)))
           (equal (fn-hp-rep w j (fn-hp-rep x o d)) (fn-hp-rep (fn-hp-rep w j x) (+ j o) d)))
  :hints (("Goal" :use ((:instance fn-hp-equal-by-agree (x (fn-hp-rep w j (fn-hp-rep x o d)))
                                   (y (fn-hp-rep (fn-hp-rep w j x) (+ j o) d)))
                        (:instance fn-hp-rep-nest-agree (a 0) (n (len (fn-hp-rep w j (fn-hp-rep x o d))))))
           :in-theory (disable fn-hp-rep-nest-agree fn-hp-rep))))

(defthm fn-hp-rep-commute-nth
  (implies (and (natp k) (natp a) (natp b) (or (atom x) (atom y) (<= (+ a (len x)) b) (<= (+ b (len y)) a)))
           (equal (nth k (fn-hp-rep (fn-hp-rep w a x) b y))
                  (nth k (fn-hp-rep (fn-hp-rep w b y) a x))))
  :hints (("Goal" :in-theory (disable fn-hp-rep))))

(defthm fn-hp-rep-commute-agree
  (implies (and (natp i) (natp a) (natp b) (or (atom x) (atom y) (<= (+ a (len x)) b) (<= (+ b (len y)) a)))
           (fn-hp-agree i n (fn-hp-rep (fn-hp-rep w a x) b y) (fn-hp-rep (fn-hp-rep w b y) a x)))
  :hints (("Goal" :induct (fn-hp-agree-ind i n) :in-theory (disable fn-hp-rep fn-hp-rep-commute-nth))
          ("Subgoal *1/2" :use ((:instance fn-hp-rep-commute-nth (k i))))))

(defthm fn-hp-rep-commute
  (implies (and (natp a) (natp b) (true-listp w) (<= (+ a (len x)) (len w)) (<= (+ b (len y)) (len w))
                (or (atom x) (atom y) (<= (+ a (len x)) b) (<= (+ b (len y)) a)))
           (equal (fn-hp-rep (fn-hp-rep w a x) b y) (fn-hp-rep (fn-hp-rep w b y) a x)))
  :hints (("Goal" :use ((:instance fn-hp-equal-by-agree (x (fn-hp-rep (fn-hp-rep w a x) b y))
                                   (y (fn-hp-rep (fn-hp-rep w b y) a x)))
                        (:instance fn-hp-rep-commute-agree (i 0) (n (len (fn-hp-rep (fn-hp-rep w a x) b y)))))
           :in-theory (disable fn-hp-rep-commute-agree fn-hp-rep)))
  :rule-classes nil)

(defun fn-hp-wreps-ind (u a x blocks)
  (declare (xargs :verify-guards nil))
  (if (atom blocks) (list u a x)
    (fn-hp-wreps-ind (fn-hp-rep u (nfix (car (car blocks))) (true-list-fix (cdr (car blocks)))) a x (cdr blocks))))

(defthm fn-hp-wreps-commute
  (implies (and (natp a) (true-listp x) (true-listp u) (<= (+ a (len x)) (len u))
                (fn-hp-blocks-within blocks (len u))
                (fn-hp-block-apart (cons a x) blocks))
           (equal (fn-hp-wreps (fn-hp-rep u a x) blocks) (fn-hp-rep (fn-hp-wreps u blocks) a x)))
  :hints (("Goal" :induct (fn-hp-wreps-ind u a x blocks) :in-theory (disable fn-hp-rep))
          ("Subgoal *1/2" :use ((:instance fn-hp-rep-commute (w u) (y (true-list-fix (cdr (car blocks))))
                                           (b (nfix (car (car blocks)))))))))

; Triples (J X O D): a block X at J whose part at O becomes D.
(defun fn-hp-outer (ts)
  (declare (xargs :verify-guards nil))
  (if (atom ts) nil (cons (cons (nfix (nth 0 (car ts))) (true-list-fix (nth 1 (car ts)))) (fn-hp-outer (cdr ts)))))

(defun fn-hp-outer2 (ts)
  (declare (xargs :verify-guards nil))
  (if (atom ts) nil
    (cons (cons (nfix (nth 0 (car ts)))
                (fn-hp-rep (true-list-fix (nth 1 (car ts))) (nfix (nth 2 (car ts))) (true-list-fix (nth 3 (car ts)))))
          (fn-hp-outer2 (cdr ts)))))

(defun fn-hp-inner (ts)
  (declare (xargs :verify-guards nil))
  (if (atom ts) nil
    (cons (cons (+ (nfix (nth 0 (car ts))) (nfix (nth 2 (car ts)))) (true-list-fix (nth 3 (car ts))))
          (fn-hp-inner (cdr ts)))))

(defun fn-hp-triples-ok (ts n)
  ; each part inside its block, each block inside N words
  (declare (xargs :verify-guards nil))
  (if (atom ts) t
    (and (<= (+ (nfix (nth 2 (car ts))) (len (nth 3 (car ts)))) (len (nth 1 (car ts))))
         (<= (+ (nfix (nth 0 (car ts))) (len (nth 1 (car ts)))) (nfix n))
         (fn-hp-triples-ok (cdr ts) n))))

(defthm fn-hp-block-apart-sub
  (implies (and (fn-hp-block-apart (cons j x) blocks) (natp j) (natp o) (<= (+ o (len d)) (len x)))
           (fn-hp-block-apart (cons (+ j o) d) blocks))
  :hints (("Goal" :induct (fn-hp-block-apart (cons j x) blocks) :in-theory (disable fn-hp-rep))))

(defthm fn-hp-within-outer
  (implies (fn-hp-triples-ok ts n) (fn-hp-blocks-within (fn-hp-outer ts) n)))

(defthm fn-hp-len-tlf (equal (len (true-list-fix x)) (len x)))

(defun fn-hp-nest-ind (w ts)
  (declare (xargs :verify-guards nil))
  (if (atom ts) (list w)
    (fn-hp-nest-ind (fn-hp-rep w (nfix (nth 0 (car ts)))
                               (fn-hp-rep (true-list-fix (nth 1 (car ts))) (nfix (nth 2 (car ts)))
                                          (true-list-fix (nth 3 (car ts)))))
                    (cdr ts))))

(defthm fn-hp-nest-step
  (implies (and (natp j) (natp o) (true-listp w) (true-listp x) (true-listp d)
                (<= (+ o (len d)) (len x)) (<= (+ j (len x)) (len w))
                (fn-hp-blocks-within blocks (len w)) (fn-hp-block-apart (cons j x) blocks))
           (equal (fn-hp-wreps (fn-hp-rep w j (fn-hp-rep x o d)) blocks)
                  (fn-hp-rep (fn-hp-wreps (fn-hp-rep w j x) blocks) (+ j o) d)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-rep-nest)
                 (:instance fn-hp-wreps-commute (u (fn-hp-rep w j x)) (a (+ j o)) (x d))
                 (:instance fn-hp-block-apart-sub))
           :in-theory (disable fn-hp-rep-nest fn-hp-wreps-commute fn-hp-block-apart-sub fn-hp-wreps fn-hp-rep
                               fn-hp-block-apart fn-hp-blocks-within))))

(defthm fn-hp-wreps-nest
  (implies (and (true-listp w) (fn-hp-triples-ok ts (len w)) (fn-hp-blocks-apart (fn-hp-outer ts)))
           (equal (fn-hp-wreps w (fn-hp-outer2 ts))
                  (fn-hp-wreps (fn-hp-wreps w (fn-hp-outer ts)) (fn-hp-inner ts))))
  :hints (("Goal" :induct (fn-hp-nest-ind w ts)
           :in-theory (disable fn-hp-rep fn-hp-block-apart fn-hp-rep-nest fn-hp-wreps-commute nth
                               list-fix-when-true-listp))))

