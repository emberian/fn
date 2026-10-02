; catalog-wbv-trie.lisp -- the paged catalog's withdrawals-by-version set.
;
; A version's withdrawn rows, as a binary trie over the row numbers, most
; significant bit first: a value is (D . TREE) with every member below 2^D;
; at depth 0 a TREE is a count (the member's multiplicity), at depth D > 0
; it is NIL (empty) or (LOW . HIGH), LOW the members below 2^(D-1) and HIGH
; the rest less 2^(D-1).  NIL is the empty set.
;
; Bounded both ways for EVERY arrival order (D27; a hostile cancel storm can
; withdraw in any order):
;   the writer (fn-cpt-add) copies one root-to-leaf path: D conses, plus one
;   a level of growth when the number is past the root's range -- O(log N);
;   the reader (fn-cpt-list's exec, fn-cpt-walk) visits each non-empty node
;   once, right subtree first onto an accumulator, so its only allocation is
;   the answer's own conses, and its recursion depth is D.  Its TIME is the
;   nodes visited: O(k * D) for k members at the worst (a sparse bucket, one
;   member per path), O(k + D) when the members share paths; D is the bit
;   length of the largest number ever added to the bucket (Codex r35: a
;   bucket holding only 2^64 walks 65 nodes for one answer).  Not O(k): a
;   patricia trie (single-child chains collapsed) would make it O(k) in the
;   bucket's members, at the price of a path-compression writer.
;
; KEYSTONE fn-cpt-list-of-add: the trie's ascending list after an add is the
; ascending insertion of the number into the list before it (fn-cpt-insert,
; the logic of the old foundation's fn-cat-insert-asc), for ANY natural --
; leaves are counts, so a multiset is modelled exactly and no distinctness
; invariant is needed.  books/catalog-paged.lisp equates fn-cpt-insert with
; fn-cat-insert-asc and uses this as its withdrawals table.

(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

; The ascending insertion (the logic of books/catalog-logic.lisp
; fn-cat-insert-asc, restated so this book stays a leaf).
(defun fn-cpt-insert (s l)
  (declare (xargs :guard t))
  (if (and (consp l) (< (nfix (car l)) (nfix s)))
      (cons (car l) (fn-cpt-insert s (cdr l)))
    (cons s l)))

(defun fn-cpt-copies (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons x (fn-cpt-copies (1- n) x))))

(defun fn-cpt-elems (d base tr)
  (declare (xargs :guard (and (natp d) (natp base)) :verify-guards nil))
  (cond ((zp d) (fn-cpt-copies (nfix tr) base))
        ((atom tr) nil)
        (t (append (fn-cpt-elems (1- d) base (car tr))
                   (fn-cpt-elems (1- d) (+ base (expt 2 (1- d))) (cdr tr))))))

(defun fn-cpt-rep (n x acc)
  (declare (xargs :guard (natp n)))
  (if (zp n) acc (fn-cpt-rep (1- n) x (cons x acc))))

(defun fn-cpt-walk (d base tr acc)
  (declare (xargs :guard (and (natp d) (natp base))))
  (cond ((zp d) (fn-cpt-rep (nfix tr) base acc))
        ((atom tr) acc)
        (t (fn-cpt-walk (1- d) base (car tr)
                        (fn-cpt-walk (1- d) (+ base (expt 2 (1- d))) (cdr tr) acc)))))

(local
 (defthm fn-cpt-copies-shift
   (equal (append (fn-cpt-copies n x) (cons x acc))
          (cons x (append (fn-cpt-copies n x) acc)))))

(local
 (defthm fn-cpt-rep-is-append
   (equal (fn-cpt-rep n x acc) (append (fn-cpt-copies n x) acc))
))

(defthm fn-cpt-walk-is-elems
  (equal (fn-cpt-walk d base tr acc) (append (fn-cpt-elems d base tr) acc)))

(defthm fn-cpt-true-listp-of-elems
  (true-listp (fn-cpt-elems d base tr))
  :rule-classes :type-prescription)

(verify-guards fn-cpt-elems)

(defun fn-cpt-d (v)
  (declare (xargs :guard t))
  (if (consp v) (nfix (car v)) 0))

(defun fn-cpt-tr (v)
  (declare (xargs :guard t))
  (if (consp v) (cdr v) nil))

; The reader: the version's rows, ascending.
(defun fn-cpt-list (v)
  (declare (xargs :guard t))
  (mbe :logic (fn-cpt-elems (fn-cpt-d v) 0 (fn-cpt-tr v))
       :exec (fn-cpt-walk (fn-cpt-d v) 0 (fn-cpt-tr v) nil)))

(defun fn-cpt-ins (d s tr)
  (declare (xargs :guard (and (natp d) (natp s))))
  (cond ((zp d) (+ 1 (nfix tr)))
        ((< s (expt 2 (1- d)))
         (cons (fn-cpt-ins (1- d) s (if (consp tr) (car tr) nil)) (if (consp tr) (cdr tr) nil)))
        (t (cons (if (consp tr) (car tr) nil)
                 (fn-cpt-ins (1- d) (- s (expt 2 (1- d))) (if (consp tr) (cdr tr) nil))))))

(local
 (defun fn-cpt-pow2 (d)
   (if (zp d) 1 (* 2 (fn-cpt-pow2 (1- d))))))

(local
 (defthm fn-cpt-pow2-is-expt
   (implies (natp d) (equal (fn-cpt-pow2 d) (expt 2 d)))))

(local
 (defthm fn-cpt-d-below-pow2
   (implies (natp d) (<= (+ 1 d) (fn-cpt-pow2 d)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-cpt-pow2-is-expt) :induct (fn-cpt-pow2 d)))))

(local
 (defthm fn-cpt-d-below-expt
   (implies (natp d) (<= (+ 1 d) (expt 2 d)))
   :rule-classes :linear
   :hints (("Goal" :use (fn-cpt-d-below-pow2 fn-cpt-pow2-is-expt)
            :in-theory (disable fn-cpt-pow2-is-expt)))))

(defun fn-cpt-grow (d tr s)
  (declare (xargs :guard (and (natp d) (natp s))
                  :measure (nfix (- (+ 1 (nfix s)) (nfix d)))))
  (if (and (natp d) (natp s) (<= (expt 2 d) s))
      (fn-cpt-grow (+ 1 d) (cons tr nil) s)
    (cons (nfix d) tr)))

(defthm fn-cpt-grow-depth-natp
  (natp (car (fn-cpt-grow d tr s)))
  :rule-classes :type-prescription)

; The writer: one number into a version's set.
(defun fn-cpt-add (s v)
  (declare (xargs :guard (natp s)))
  (let ((g (fn-cpt-grow (fn-cpt-d v) (fn-cpt-tr v) s)))
    (cons (car g) (fn-cpt-ins (car g) s (cdr g)))))

; ---------------------------------------------------------------------------
; The proof.

(local
 (defun fn-cpt-all-ge (l x)
   (if (consp l) (and (<= (nfix x) (nfix (car l))) (fn-cpt-all-ge (cdr l) x)) t)))

(local
 (defun fn-cpt-all-lt (l x)
   (if (consp l) (and (< (nfix (car l)) (nfix x)) (fn-cpt-all-lt (cdr l) x)) t)))

(local
 (defthm fn-cpt-all-ge-of-append
   (equal (fn-cpt-all-ge (append a b) x) (and (fn-cpt-all-ge a x) (fn-cpt-all-ge b x)))))

(local
 (defthm fn-cpt-all-lt-of-append
   (equal (fn-cpt-all-lt (append a b) x) (and (fn-cpt-all-lt a x) (fn-cpt-all-lt b x)))))

(local
 (defthm fn-cpt-all-ge-of-repeat
   (implies (<= (nfix x) (nfix y)) (fn-cpt-all-ge (fn-cpt-copies n y) x))
))

(local
 (defthm fn-cpt-all-lt-of-repeat
   (implies (< (nfix y) (nfix x)) (fn-cpt-all-lt (fn-cpt-copies n y) x))
))

(local
 (defthm fn-cpt-all-ge-weaken
   (implies (and (fn-cpt-all-ge l y) (<= (nfix x) (nfix y))) (fn-cpt-all-ge l x))))

(local
 (defthm fn-cpt-all-lt-weaken
   (implies (and (fn-cpt-all-lt l y) (<= (nfix y) (nfix x))) (fn-cpt-all-lt l x))))

; Every member of a subtree lies in [base, base + 2^d).
(local
 (defthm fn-cpt-elems-bounds
   (implies (and (natp d) (natp base))
            (and (fn-cpt-all-ge (fn-cpt-elems d base tr) base)
                 (fn-cpt-all-lt (fn-cpt-elems d base tr) (+ base (expt 2 d)))))
   :hints (("Goal" :induct (fn-cpt-elems d base tr))
           ("Subgoal *1/2" :use ((:instance fn-cpt-all-ge-weaken
                                            (l (fn-cpt-elems (1- d) (+ base (expt 2 (1- d))) (cdr tr)))
                                            (y (+ base (expt 2 (1- d)))) (x base))
                                 (:instance fn-cpt-all-lt-weaken
                                            (l (fn-cpt-elems (1- d) base (car tr)))
                                            (y (+ base (expt 2 (1- d)))) (x (+ base (expt 2 d)))))
            :in-theory (disable fn-cpt-all-ge-weaken fn-cpt-all-lt-weaken)))))

(local
 (defthm fn-cpt-insert-into-left
   (implies (and (true-listp a) (fn-cpt-all-ge b x))
            (equal (fn-cpt-insert x (append a b)) (append (fn-cpt-insert x a) b)))
   :hints (("Goal" :expand ((fn-cpt-insert x b))))))

(local
 (defthm fn-cpt-insert-into-right
   (implies (fn-cpt-all-lt a x)
            (equal (fn-cpt-insert x (append a b)) (append a (fn-cpt-insert x b))))))

(local
 (defthm fn-cpt-insert-of-repeat
   (implies (natp x)
            (equal (fn-cpt-insert x (fn-cpt-copies n x)) (fn-cpt-copies (+ 1 (nfix n)) x)))
))

(local
 (defthm fn-cpt-elems-of-atom
   (implies (atom tr) (equal (fn-cpt-elems d base tr) (fn-cpt-copies (if (zp d) (nfix tr) 0) base)))
))

(local
 (defun fn-cpt-ins-ind (d base s tr)
   (cond ((zp d) (list base s tr))
         ((< (nfix s) (expt 2 (1- d))) (fn-cpt-ins-ind (1- d) base s (car tr)))
         (t (fn-cpt-ins-ind (1- d) (+ (nfix base) (expt 2 (1- d))) (- (nfix s) (expt 2 (1- d))) (cdr tr))))))

(local
 (defthm fn-cpt-elems-of-ins
   (implies (and (natp d) (natp base) (natp s) (< s (expt 2 d)))
            (equal (fn-cpt-elems d base (fn-cpt-ins d s tr))
                   (fn-cpt-insert (+ base s) (fn-cpt-elems d base tr))))
   :hints (("Goal" :induct (fn-cpt-ins-ind d base s tr)
            :expand ((fn-cpt-elems d base tr)
                     (fn-cpt-elems d base (fn-cpt-ins d s tr))))
           ("Subgoal *1/3" :use ((:instance fn-cpt-elems-bounds (d (1- d)) (tr (car tr)))
                                 (:instance fn-cpt-all-lt-weaken
                                            (l (fn-cpt-elems (1- d) base (car tr)))
                                            (y (+ base (expt 2 (1- d)))) (x (+ base s))))
            :in-theory (disable fn-cpt-elems-bounds fn-cpt-all-lt-weaken))
           ("Subgoal *1/2" :use ((:instance fn-cpt-elems-bounds (d (1- d)) (base (+ base (expt 2 (1- d)))) (tr (cdr tr)))
                                 (:instance fn-cpt-all-ge-weaken
                                            (l (fn-cpt-elems (1- d) (+ base (expt 2 (1- d))) (cdr tr)))
                                            (y (+ base (expt 2 (1- d)))) (x (+ base s))))
            :in-theory (disable fn-cpt-elems-bounds fn-cpt-all-ge-weaken)))))

(local
 (defthm fn-cpt-elems-of-wrap
   (implies (natp d)
            (equal (fn-cpt-elems (+ 1 d) base (cons tr nil)) (fn-cpt-elems d base tr)))
   :hints (("Goal" :expand ((fn-cpt-elems (+ 1 d) base (cons tr nil)))))))

(local
 (defthm fn-cpt-grow-fields
   (implies (natp d)
            (and (natp (car (fn-cpt-grow d tr s)))
                 (equal (fn-cpt-elems (car (fn-cpt-grow d tr s)) 0 (cdr (fn-cpt-grow d tr s)))
                        (fn-cpt-elems d 0 tr))
                 (implies (natp s) (< s (expt 2 (car (fn-cpt-grow d tr s)))))))))

; KEYSTONE: the reader's answer after an add is the ascending insertion.
(defthm fn-cpt-list-of-add
  (implies (natp s)
           (equal (fn-cpt-list (fn-cpt-add s v))
                  (fn-cpt-insert s (fn-cpt-list v))))
  :hints (("Goal" :in-theory (disable fn-cpt-grow))))

(defthm fn-cpt-list-of-nil
  (equal (fn-cpt-list nil) nil))

(defthm fn-cpt-true-listp-of-list
  (true-listp (fn-cpt-list v))
  :rule-classes :type-prescription)

(in-theory (disable fn-cpt-list fn-cpt-add))
