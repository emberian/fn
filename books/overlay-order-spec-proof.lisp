; The overlay's specification order, for any key. The key order is a strict
; order on entries (it flips under exchange and :lt is transitive), so
; inserting distinct-keyed entries one at a time in arrival order yields
; fn2-ov-sort-spec, which is sorted and as long as its input; and the place
; an insertion takes is the lower bound of the inserted entry.
(in-package "ACL2")
(include-book "overlay")

(defun fn2-ov-order-flip (o)
  (declare (xargs :guard t))
  (case o (:lt :gt) (:gt :lt) (otherwise :eq)))

(local
 (defthm fn2-run-octets-order-spec-cases
   (member-eq (fn2-run-octets-order-spec a b) '(:lt :eq :gt))
   :rule-classes nil))

(local
 (defthm fn2-run-octets-order-spec-exchange
   (equal (fn2-run-octets-order-spec b a) (fn2-ov-order-flip (fn2-run-octets-order-spec a b)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-run-octets-order-spec a b)))))

(local
 (defthm fn2-run-octets-order-spec-flips
   (implies (syntaxp (and (term-order a b) (not (equal a b))))
            (equal (fn2-run-octets-order-spec b a) (fn2-ov-order-flip (fn2-run-octets-order-spec a b))))
   :hints (("Goal" :use fn2-run-octets-order-spec-exchange))))

; One key field's comparison, the step of the key order.
(defun fn2-ov-field-order (k x y)
  (declare (xargs :verify-guards nil))
  (cond ((eq k :digest) (fn2-run-octets-order-spec (cdr x) (cdr y)))
        ((and (consp k) (eq (car k) :octets)) (fn2-run-octets-order-spec x y))
        ((< (nfix x) (nfix y)) :lt) ((< (nfix y) (nfix x)) :gt) (t :eq)))

(local
 (defthm fn2-run-key-order-spec-by-field
  (equal (fn2-run-key-order-spec key a b)
         (if (atom key) :eq
           (let ((o (fn2-ov-field-order (cadar key) (car a) (car b))))
             (if (eq o :eq) (fn2-run-key-order-spec (cdr key) (cdr a) (cdr b)) o))))
  :rule-classes ((:definition :controller-alist ((fn2-run-key-order-spec t nil nil))))
  :hints (("Goal" :expand ((fn2-run-key-order-spec key a b))))))

(local
 (defthm fn2-ov-field-order-cases
   (member-eq (fn2-ov-field-order k x y) '(:lt :eq :gt))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-octets-order-spec-cases (a x) (b y))
                         (:instance fn2-run-octets-order-spec-cases (a (cdr x)) (b (cdr y))))))))

(local
 (defthm fn2-ov-field-order-exchange
   (equal (fn2-ov-field-order k y x) (fn2-ov-order-flip (fn2-ov-field-order k x y)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-octets-order-spec-exchange (a x) (b y))
                         (:instance fn2-run-octets-order-spec-exchange (a (cdr x)) (b (cdr y))))))))

(local (in-theory (disable fn2-ov-field-order (:definition fn2-run-key-order-spec))))

(local
 (defun fn2-ov-key-walk (key a b)
   (if (atom key) (list a b) (fn2-ov-key-walk (cdr key) (cdr a) (cdr b)))))

(defthm fn2-run-key-order-spec-cases
  (member-eq (fn2-run-key-order-spec key a b) '(:lt :eq :gt))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ov-key-walk key a b))
          (and stable-under-simplificationp
               '(:use ((:instance fn2-ov-field-order-cases (k (cadar key)) (x (car a)) (y (car b))))))))

(defthm fn2-run-key-order-spec-exchange
  (equal (fn2-run-key-order-spec key b a) (fn2-ov-order-flip (fn2-run-key-order-spec key a b)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ov-key-walk key a b))
          ("Subgoal *1/2"
           :expand ((fn2-run-key-order-spec key a b) (fn2-run-key-order-spec key b a))
           :use ((:instance fn2-ov-field-order-exchange (k (cadar key)) (x (car a)) (y (car b)))
                 (:instance fn2-ov-field-order-cases (k (cadar key)) (x (car a)) (y (car b)))
                 (:instance fn2-run-key-order-spec-cases (key (cdr key)) (a (cdr a)) (b (cdr b)))))))

(defthm fn2-run-key-order-spec-flips
  (implies (syntaxp (and (term-order a b) (not (equal a b))))
           (equal (fn2-run-key-order-spec key b a) (fn2-ov-order-flip (fn2-run-key-order-spec key a b))))
  :hints (("Goal" :use fn2-run-key-order-spec-exchange)))

(local
 (defthm fn2-run-octets-order-spec-transitive
   (implies (and (eq (fn2-run-octets-order-spec a b) :lt) (eq (fn2-run-octets-order-spec b c) :lt))
            (eq (fn2-run-octets-order-spec a c) :lt))))

(local
 (defthm fn2-run-octets-order-spec-eq-left
   (implies (eq (fn2-run-octets-order-spec a b) :eq)
            (equal (fn2-run-octets-order-spec a c) (fn2-run-octets-order-spec b c)))))

(local
 (defthm fn2-run-octets-order-spec-eq-right
   (implies (eq (fn2-run-octets-order-spec b c) :eq)
            (equal (fn2-run-octets-order-spec a b) (fn2-run-octets-order-spec a c)))
   :hints (("Goal" :use ((:instance fn2-run-octets-order-spec-eq-left (a c) (b b) (c a)))
            :in-theory (disable fn2-run-octets-order-spec-eq-left)))))

(local
 (defthm fn2-ov-field-order-transitive
   (implies (and (eq (fn2-ov-field-order k x y) :lt) (eq (fn2-ov-field-order k y z) :lt))
            (eq (fn2-ov-field-order k x z) :lt))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-ov-field-order)
            :cases ((eq k :digest) (and (consp k) (eq (car k) :octets))))
           (and stable-under-simplificationp
                '(:use ((:instance fn2-run-octets-order-spec-transitive (a x) (b y) (c z))
                        (:instance fn2-run-octets-order-spec-transitive (a (cdr x)) (b (cdr y)) (c (cdr z)))))))))

(local
 (defthm fn2-ov-field-order-eq-left
   (implies (eq (fn2-ov-field-order k x y) :eq)
            (equal (fn2-ov-field-order k x z) (fn2-ov-field-order k y z)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-ov-field-order)
            :cases ((eq k :digest) (and (consp k) (eq (car k) :octets))))
           (and stable-under-simplificationp
                '(:use ((:instance fn2-run-octets-order-spec-eq-left (a (cdr x)) (b (cdr y)) (c (cdr z)))
                        (:instance fn2-run-octets-order-spec-eq-left (a x) (b y) (c z))))))))

(local
 (defthm fn2-ov-field-order-eq-right
   (implies (eq (fn2-ov-field-order k y z) :eq)
            (equal (fn2-ov-field-order k x y) (fn2-ov-field-order k x z)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-ov-field-order)
            :cases ((eq k :digest) (and (consp k) (eq (car k) :octets))))
           (and stable-under-simplificationp
                '(:use ((:instance fn2-run-octets-order-spec-eq-right (a (cdr x)) (b (cdr y)) (c (cdr z)))
                        (:instance fn2-run-octets-order-spec-eq-right (a x) (b y) (c z))))))))

(local
 (defun fn2-ov-key-walk3 (key a b c)
   (if (atom key) (list a b c) (fn2-ov-key-walk3 (cdr key) (cdr a) (cdr b) (cdr c)))))

(defthm fn2-run-key-order-spec-transitive
  (implies (and (eq (fn2-run-key-order-spec key a b) :lt) (eq (fn2-run-key-order-spec key b c) :lt))
           (eq (fn2-run-key-order-spec key a c) :lt))
  :hints (("Goal" :induct (fn2-ov-key-walk3 key a b c))
          ("Subgoal *1/2"
           :expand ((fn2-run-key-order-spec key a b) (fn2-run-key-order-spec key b c) (fn2-run-key-order-spec key a c))
           :use ((:instance fn2-ov-field-order-transitive (k (cadar key)) (x (car a)) (y (car b)) (z (car c)))
                 (:instance fn2-ov-field-order-eq-left (k (cadar key)) (x (car a)) (y (car b)) (z (car c)))
                 (:instance fn2-ov-field-order-eq-right (k (cadar key)) (x (car a)) (y (car b)) (z (car c)))))))

(local (in-theory (disable fn2-run-key-order-spec-by-field fn2-run-key-order-spec)))

; Insertion commutes for entries whose keys differ.
(local
 (defthm fn2-ov-sort-insert-commutes
   (implies (not (eq (fn2-run-key-order-spec key a b) :eq))
            (equal (fn2-ov-sort-insert-spec key a (fn2-ov-sort-insert-spec key b s))
                   (fn2-ov-sort-insert-spec key b (fn2-ov-sort-insert-spec key a s))))
   :hints (("Goal" :induct (fn2-ov-sort-insert-spec key a s))
           (and stable-under-simplificationp
                '(:use ((:instance fn2-run-key-order-spec-cases)
                        (:instance fn2-run-key-order-spec-transitive (a (car s)) (b a) (c b))
                        (:instance fn2-run-key-order-spec-transitive (a (car s)) (b b) (c a))))))))

; Insertion in arrival order, the order the adapter inserts in.
(defun fn2-ov-insert-all-spec (key entries sorted)
  (declare (xargs :verify-guards nil))
  (if (atom entries) sorted
    (fn2-ov-insert-all-spec key (cdr entries) (fn2-ov-sort-insert-spec key (car entries) sorted))))

(local
 (defun fn2-ov-insert-right (key entries sorted)
   (if (atom entries) sorted
     (fn2-ov-sort-insert-spec key (car entries) (fn2-ov-insert-right key (cdr entries) sorted)))))

(local
 (defthm fn2-ov-insert-right-absorbs
   (implies (fn2-ov-key-absent-spec key e entries)
            (equal (fn2-ov-insert-right key entries (fn2-ov-sort-insert-spec key e s))
                   (fn2-ov-sort-insert-spec key e (fn2-ov-insert-right key entries s))))
   :hints (("Goal" :induct (fn2-ov-insert-right key entries s))
           (and stable-under-simplificationp
                '(:in-theory (disable fn2-ov-sort-insert-commutes)
                  :use ((:instance fn2-ov-sort-insert-commutes (a (car entries)) (b e)
                                   (s (fn2-ov-insert-right key (cdr entries) s)))
                        (:instance fn2-run-key-order-spec-cases (a e) (b (car entries)))
                        (:instance fn2-run-key-order-spec-exchange (a e) (b (car entries)))))))))

(local
 (defthm fn2-ov-insert-all-is-right
   (implies (fn2-ov-distinct-spec key entries)
            (equal (fn2-ov-insert-all-spec key entries s) (fn2-ov-insert-right key entries s)))
   :hints (("Goal" :induct (fn2-ov-insert-all-spec key entries s)))))

(local
 (defthm fn2-ov-sort-spec-is-right
   (equal (fn2-ov-sort-spec key entries) (fn2-ov-insert-right key entries nil))))

(defthm fn2-ov-insert-all-sorts
  (implies (fn2-ov-distinct-spec key entries)
           (equal (fn2-ov-insert-all-spec key entries nil) (fn2-ov-sort-spec key entries))))

(local (in-theory (disable fn2-ov-sort-spec-is-right)))

; The place an insertion takes is the inserted entry's lower bound.
(defun fn2-ov-insert-place (key e s)
  (declare (xargs :verify-guards nil))
  (if (and (consp s) (eq (fn2-run-key-order-spec key (car s) e) :lt))
      (+ 1 (fn2-ov-insert-place key e (cdr s)))
    0))

(defthm fn2-ov-insert-place-is-lower-bound
  (implies (acl2-numberp i)
           (equal (cadr (fn2-run-lower-bound-spec key s e i)) (+ i (fn2-ov-insert-place key e s)))))

(defthmd fn2-ov-sort-insert-at-place
  (let ((p (fn2-ov-insert-place key e s)))
    (implies (true-listp s)
             (equal (fn2-ov-sort-insert-spec key e s)
                    (append (take p s) (cons e (nthcdr p s)))))))

(defthm fn2-ov-insert-place-bound
  (<= (fn2-ov-insert-place key e s) (len s))
  :rule-classes :linear)

(defthm fn2-ov-sort-insert-len
  (equal (len (fn2-ov-sort-insert-spec key e s)) (+ 1 (len s)))
  :hints (("Goal" :induct (fn2-ov-sort-insert-spec key e s) :in-theory (disable fn2-run-key-order-spec-flips))))

(defthm fn2-ov-sort-spec-len
  (equal (len (fn2-ov-sort-spec key entries)) (len entries))
  :hints (("Goal" :in-theory (disable fn2-run-key-order-spec-flips fn2-ov-sort-insert-spec))))

; Sortedness, given distinct keys.
(defthm fn2-ov-key-absent-after-insert
  (implies (and (fn2-ov-key-absent-spec key x s) (not (eq (fn2-run-key-order-spec key x e) :eq)))
           (fn2-ov-key-absent-spec key x (fn2-ov-sort-insert-spec key e s)))
  :hints (("Goal" :induct (fn2-ov-sort-insert-spec key e s) :in-theory (disable fn2-run-key-order-spec-flips))))

(local
 (defthm fn2-ov-key-absent-of-sort
   (implies (fn2-ov-key-absent-spec key x entries)
            (fn2-ov-key-absent-spec key x (fn2-ov-sort-spec key entries)))))

(local
 (defthm fn2-ov-sort-insert-head
   (implies (and (eq (fn2-run-key-order-spec key c e) :lt)
                 (or (atom s) (eq (fn2-run-key-order-spec key c (car s)) :lt)))
            (eq (fn2-run-key-order-spec key c (car (fn2-ov-sort-insert-spec key e s))) :lt))
   :hints (("Goal" :expand ((fn2-ov-sort-insert-spec key e s)) :in-theory (disable fn2-run-key-order-spec-flips)))))

(local
 (defthm fn2-ov-sorted-insert
   (implies (and (fn2-run-sorted-spec key s) (fn2-ov-key-absent-spec key e s))
            (fn2-run-sorted-spec key (fn2-ov-sort-insert-spec key e s)))
   :hints (("Goal" :induct (fn2-ov-sort-insert-spec key e s)
            :in-theory (e/d ((:induction fn2-ov-sort-insert-spec)) (fn2-run-key-order-spec-flips (:definition fn2-ov-sort-insert-spec)))
            :expand ((fn2-ov-sort-insert-spec key e s) (fn2-run-sorted-spec key s)
                     (fn2-ov-key-absent-spec key e s)
                     (:free (a b) (fn2-run-sorted-spec key (cons a b)))))
           (and stable-under-simplificationp
                '(:use ((:instance fn2-run-key-order-spec-cases (a (car s)) (b e))
                        (:instance fn2-run-key-order-spec-exchange (a (car s)) (b e))
                        (:instance fn2-ov-sort-insert-head (c (car s)) (s (cdr s)))))))))

(defthm fn2-ov-sort-spec-sorted
  (implies (fn2-ov-distinct-spec key entries)
           (fn2-run-sorted-spec key (fn2-ov-sort-spec key entries)))
  :hints (("Goal" :induct (fn2-ov-sort-spec key entries) :in-theory (disable fn2-ov-sort-spec-is-right))))
