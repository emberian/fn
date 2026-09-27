; fn prototype (lane proto-adt-2, 2026-09-27): the KEYED-SET constructor of
; the persistent ADT backend (books/proto/adt-lib.lisp).  NOT on a served
; path; no host calls it.
;
; The logical value is a true list of records whose KEY field (index J) is
; unique, with the model's own operations:
;   adt-kfind     the first record with key K       (fn-cp-find's shape)
;   adt-kremove   remove the first record with key K (fn-cp-remove's shape)
;   adt-kinsert   cons at the FRONT (:stack) or append at the back (:append)
;   adt-kreplace  replace the record with this key, else insert
;                 (fn-cfg-row-replace-key's shape, in :append order)
;   adt-kupdate   update one non-key field of the record with key K
; so a model's table functions are these at its key index, by a one-line
; induction each, and its theorems carry to the stobj's logical value.
;
; The executable is the sequence constructor over the PHYSICAL schema
; (:bool) . S: one slot per record ever inserted, a live column, and an
; index (a stobj hash table from a hash of the key to the slots whose key
; has that hash).  Insert appends a slot; remove clears its live bit and
; drops it from its bucket (a tombstone); a lookup walks the bucket and
; compares every candidate EXACTLY (its live bit and its key), so no answer
; depends on the hash.  The logical value is the live records in slot
; order (:append) or reversed (:stack), so cons-at-front is an O(1) append.
; Dead slots and their pool octets are reclaimed by compaction
; (books/proto/adt-compact-lib.lisp), which rebuilds the canonical image.
;
; Every definition and lemma is universally quantified over the schema and
; the key index; `defadt-keyed' (books/proto/adt-keyed.lisp) instantiates
; them and proves nothing by hand.

(in-package "ACL2")
(include-book "adt-lib")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth update-nth resize-list)))

; -----------------------------------------------------------------------------
; A. The abstraction function: the records a column image holds.  Under the
; sequence correspondence it IS the corresponding value (adt-abs-of-corr),
; so a correspondence may name "the records of c" without a quantifier.

(defun adt-row-aux (s j n i c)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      nil
    (cons (adt-get-c s j i c) (adt-row-aux s (1+ (nfix j)) (1- n) i c))))

(defun adt-rows (s i n c)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      nil
    (cons (adt-row-aux s 0 (len s) i c) (adt-rows s (1+ (nfix i)) (1- n) c))))

(defun adt-abs (s c)
  (declare (xargs :verify-guards nil))
  (adt-rows s 0 (nfix (adt-count-c s c)) c))

(defthm adt-len-when-rec-p
  (implies (adt-rec-p s r) (equal (len r) (len s)))
  :hints (("Goal" :in-theory (enable adt-rec-p))))

(defthm adt-car-nthcdr
  (equal (car (nthcdr j r)) (nth j r))
  :hints (("Goal" :in-theory (enable nth nthcdr))))

(defthm adt-cdr-nthcdr
  (implies (natp j) (equal (cdr (nthcdr j r)) (nthcdr (1+ j) r)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm adt-consp-nthcdr
  (implies (and (natp j) (< j (len r))) (consp (nthcdr j r)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(local
 (defthm adt-take-open
   (implies (and (posp n) (consp x))
            (equal (take n x) (cons (car x) (take (1- n) (cdr x)))))))

(local
 (defthm adt-take-nthcdr-open
   (implies (and (natp j) (posp n) (< j (len r)))
            (equal (take n (nthcdr j r))
                   (cons (nth j r) (take (1- n) (nthcdr (1+ j) r)))))
   :hints (("Goal" :in-theory (disable take)
            :use ((:instance adt-take-open (x (nthcdr j r))))))))

(local
 (defthm adt-take-all-true-listp
   (implies (true-listp r) (equal (take (len r) r) r))))

(defthm adt-seq-p-when-corr
  (implies (adt-corr s c a) (adt-seq-p s a))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable adt-corr))))

(defthm adt-take-len-schema-of-rec
  (implies (adt-rec-p s r) (equal (take (len s) r) r))
  :hints (("Goal" :use ((:instance adt-len-when-rec-p) (:instance adt-take-all-true-listp))
           :in-theory (disable adt-len-when-rec-p adt-take-all-true-listp))))

(defthm adt-row-aux-of-corr
  (implies (and (adt-corr s c a) (natp i) (< i (len a)) (natp j) (<= (+ j (nfix n)) (len s)))
           (equal (adt-row-aux s j n i c) (take n (nthcdr j (nth i a)))))
  :hints (("Goal" :induct (adt-row-aux s j n i c))))

(defthm adt-row-of-corr
  (implies (and (adt-corr s c a) (natp i) (< i (len a)))
           (equal (adt-row-aux s 0 (len s) i c) (nth i a)))
  :hints (("Goal" :use ((:instance adt-row-aux-of-corr (j 0) (n (len s)))
                        (:instance adt-take-len-schema-of-rec (r (nth i a))))
           :in-theory (disable adt-row-aux-of-corr adt-take-len-schema-of-rec))))

(defthm adt-rows-of-corr
  (implies (and (adt-corr s c a) (natp i) (<= (+ i (nfix n)) (len a)))
           (equal (adt-rows s i n c) (take n (nthcdr i a))))
  :hints (("Goal" :induct (adt-rows s i n c) :in-theory (disable adt-row-aux))))

(defthm adt-abs-of-corr
  (implies (adt-corr s c a) (equal (adt-abs s c) a))
  :hints (("Goal" :use ((:instance adt-rows-of-corr (i 0) (n (len a))))
           :in-theory (e/d (adt-abs) (adt-rows-of-corr)))))

(in-theory (disable adt-abs))

; -----------------------------------------------------------------------------
; B. Keys and the logical keyed operations (the model's shapes).

(defun adt-keys (j a)
  (declare (xargs :guard (and (natp j) (true-list-listp a))))
  (if (atom a) nil (cons (nth j (car a)) (adt-keys j (cdr a)))))

(defun adt-kunique (j a)
  (declare (xargs :guard (and (natp j) (true-list-listp a))))
  (no-duplicatesp-equal (adt-keys j a)))

(defun adt-kmem (j k a)
  (declare (xargs :guard (and (natp j) (true-list-listp a))))
  (if (member-equal k (adt-keys j a)) t nil))

(defun adt-kfind (j k a)
  (declare (xargs :guard (and (natp j) (true-list-listp a))))
  (if (atom a) nil
    (if (equal (nth j (car a)) k) (car a) (adt-kfind j k (cdr a)))))

(defun adt-kremove (j k a)
  (declare (xargs :guard (and (natp j) (true-list-listp a))))
  (if (atom a) nil
    (if (equal (nth j (car a)) k) (cdr a) (cons (car a) (adt-kremove j k (cdr a))))))

(defun adt-kinsert (dir r a)
  (declare (xargs :guard (true-listp a)))
  (if (eq dir :stack) (cons r a) (append a (list r))))

(defun adt-kreplace-found (j r a)
  (declare (xargs :guard (and (natp j) (true-listp r) (true-list-listp a))))
  (if (atom a) nil
    (if (equal (nth j (car a)) (nth j r))
        (cons r (cdr a))
      (cons (car a) (adt-kreplace-found j r (cdr a))))))

(defun adt-kreplace (dir j r a)
  (declare (xargs :guard (and (natp j) (true-listp r) (true-list-listp a))))
  (if (adt-kmem j (nth j r) a)
      (adt-kreplace-found j r a)
    (adt-kinsert dir r a)))

(defun adt-kupdate (j k f v a)
  (declare (xargs :guard (and (natp j) (natp f) (true-list-listp a))))
  (if (atom a) nil
    (if (equal (nth j (car a)) k)
        (cons (update-nth f v (car a)) (cdr a))
      (cons (car a) (adt-kupdate j k f v (cdr a))))))

; Facts over the logical value.
(defthm adt-kmem-when-kfind
  (implies (adt-kfind j k a) (adt-kmem j k a)))

(defthm adt-kfind-when-not-kmem
  (implies (not (adt-kmem j k a)) (equal (adt-kfind j k a) nil)))

(defthm adt-kremove-when-not-kmem
  (implies (not (adt-kmem j k a)) (equal (adt-kremove j k a) (true-list-fix a))))

(defthm adt-keys-append
  (equal (adt-keys j (append a b)) (append (adt-keys j a) (adt-keys j b))))

(defun adt-rev (x)
  (declare (xargs :guard t))
  (if (atom x) nil (append (adt-rev (cdr x)) (list (car x)))))

(defthm adt-true-listp-rev (true-listp (adt-rev x)) :rule-classes :type-prescription)

(defthm adt-rev-append
  (equal (adt-rev (append x y)) (append (adt-rev y) (adt-rev x))))

(defthm adt-keys-rev
  (equal (adt-keys j (adt-rev a)) (adt-rev (adt-keys j a))))

(local
 (defthm adt-member-rev
   (iff (member-equal x (adt-rev l)) (member-equal x l))))

(local
 (defthm adt-member-append
   (iff (member-equal e (append x y)) (or (member-equal e x) (member-equal e y)))))

(local
 (defthm adt-intersectp-cons-right-member
   (implies (member-equal e x) (intersectp-equal x (cons e y)))))

(local
 (defthm adt-no-dup-append
   (equal (no-duplicatesp-equal (append x y))
          (and (no-duplicatesp-equal x) (no-duplicatesp-equal y)
               (not (intersectp-equal x y))))))

(local
 (defthm adt-intersectp-singleton
   (equal (intersectp-equal x (list e)) (if (member-equal e x) t nil))))

(local
 (defthm adt-intersectp-cons-right
   (implies (not (intersectp-equal x y))
            (equal (intersectp-equal x (cons e y)) (if (member-equal e x) t nil)))))

(local
 (defthm adt-no-dup-rev
   (equal (no-duplicatesp-equal (adt-rev x)) (no-duplicatesp-equal x))))

(defthm adt-kunique-rev
  (equal (adt-kunique j (adt-rev a)) (adt-kunique j a)))

(defthm adt-kmem-rev
  (equal (adt-kmem j k (adt-rev a)) (adt-kmem j k a)))

(defthm adt-kfind-append
  (equal (adt-kfind j k (append x y))
         (if (adt-kmem j k x) (adt-kfind j k x) (adt-kfind j k y)))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kreplace-found-append
  (equal (adt-kreplace-found j r (append x y))
         (if (adt-kmem j (nth j r) x)
             (append (adt-kreplace-found j r x) y)
           (append (true-list-fix x) (adt-kreplace-found j r y))))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kupdate-append
  (equal (adt-kupdate j k f v (append x y))
         (if (adt-kmem j k x)
             (append (adt-kupdate j k f v x) y)
           (append (true-list-fix x) (adt-kupdate j k f v y))))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kmem-cons
  (equal (adt-kmem j k (cons e a)) (or (equal (nth j e) k) (adt-kmem j k a)))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kmem-nil
  (not (adt-kmem j k nil))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kunique-cons
  (equal (adt-kunique j (cons e a))
         (and (not (adt-kmem j (nth j e) a)) (adt-kunique j a)))
  :hints (("Goal" :in-theory (enable adt-kmem adt-kunique))))

(defthm adt-kfind-rev
  (implies (adt-kunique j a)
           (equal (adt-kfind j k (adt-rev a)) (adt-kfind j k a))))

(defun adt-kremove-all (j k a)
  (if (atom a) nil
    (if (equal (nth j (car a)) k)
        (adt-kremove-all j k (cdr a))
      (cons (car a) (adt-kremove-all j k (cdr a))))))

(defthm adt-kremove-all-when-not-kmem
  (implies (not (adt-kmem j k a)) (equal (adt-kremove-all j k a) (true-list-fix a))))

(defthm adt-kremove-is-all-when-unique
  (implies (and (adt-kunique j a) (true-listp a)) (equal (adt-kremove j k a) (adt-kremove-all j k a))))

(defthm adt-keys-kremove-all-sub
  (implies (not (member-equal x (adt-keys j a)))
           (not (member-equal x (adt-keys j (adt-kremove-all j k a))))))

(defthm adt-kunique-kremove-all
  (implies (adt-kunique j a) (adt-kunique j (adt-kremove-all j k a)))
  :hints (("Goal" :in-theory (enable adt-kunique))))

(defthm adt-kremove-all-append
  (equal (adt-kremove-all j k (append a b))
         (append (adt-kremove-all j k a) (adt-kremove-all j k b))))

(defthm adt-kremove-all-rev
  (equal (adt-kremove-all j k (adt-rev a)) (adt-rev (adt-kremove-all j k a))))

(defthm adt-kremove-rev
  (implies (and (adt-kunique j a) (true-listp a))
           (equal (adt-kremove j k (adt-rev a)) (adt-rev (adt-kremove j k a))))
  :hints (("Goal" :in-theory (disable adt-kunique))))

(defthm adt-keys-kremove-sub
  (implies (not (member-equal x (adt-keys j a)))
           (not (member-equal x (adt-keys j (adt-kremove j k a))))))

(defthm adt-kunique-kremove
  (implies (adt-kunique j a) (adt-kunique j (adt-kremove j k a))))

(defthm adt-kunique-insert
  (implies (and (adt-kunique j a) (not (adt-kmem j (nth j r) a)))
           (adt-kunique j (adt-kinsert dir r a))))

(defthm adt-keys-kreplace-found
  (equal (adt-keys j (adt-kreplace-found j r a)) (adt-keys j a)))

(defthm adt-kunique-kreplace
  (implies (adt-kunique j a) (adt-kunique j (adt-kreplace dir j r a))))

(defthm adt-keys-kupdate
  (implies (not (equal (nfix f) (nfix j)))
           (equal (adt-keys j (adt-kupdate j k f v a)) (adt-keys j a)))
  :hints (("Goal" :in-theory (enable nth update-nth))))

(defthm adt-kunique-kupdate
  (implies (and (adt-kunique j a) (not (equal (nfix f) (nfix j))))
           (adt-kunique j (adt-kupdate j k f v a))))

(defthm adt-true-list-fix-when-true-listp
  (implies (true-listp x) (equal (true-list-fix x) x)))

(defthm adt-kreplace-found-when-not-kmem
  (implies (not (adt-kmem j (nth j r) a))
           (equal (adt-kreplace-found j r a) (true-list-fix a)))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kupdate-when-not-kmem
  (implies (not (adt-kmem j k a))
           (equal (adt-kupdate j k f v a) (true-list-fix a)))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kreplace-found-rev
  (implies (adt-kunique j a)
           (equal (adt-kreplace-found j r (adt-rev a)) (adt-rev (adt-kreplace-found j r a))))
  :hints (("Goal" :induct (adt-rev a))))

(defthm adt-kupdate-rev
  (implies (adt-kunique j a)
           (equal (adt-kupdate j k f v (adt-rev a)) (adt-rev (adt-kupdate j k f v a))))
  :hints (("Goal" :induct (adt-rev a))))

(in-theory (disable adt-kunique adt-kmem))

; -----------------------------------------------------------------------------
; C. The physical side: slots (LIVE . RECORD) and the view.

(defun adt-pschema (s)
  (declare (xargs :guard t))
  (cons '(:bool) s))

(defthm adt-pschema-facts
  (and (equal (len (adt-pschema s)) (+ 1 (len s)))
       (consp (adt-pschema s))
       (equal (car (adt-pschema s)) '(:bool))
       (equal (cdr (adt-pschema s)) s)
       (equal (nth 0 (adt-pschema s)) '(:bool))
       (implies (natp j) (equal (nth (+ 1 j) (adt-pschema s)) (nth j s)))
       (equal (adt-schemap (adt-pschema s)) (adt-schemap s))
       (equal (adt-ncols (adt-pschema s)) (+ 1 (adt-ncols s)))
       (equal (adt-rec-p (adt-pschema s) r)
              (and (consp r) (booleanp (car r)) (adt-rec-p s (cdr r)))))
  :hints (("Goal" :in-theory (enable nth adt-rec-p))))

(in-theory (disable adt-pschema))

(defun adt-live-recs (p)
  (declare (xargs :guard t))
  (if (atom p) nil
    (if (and (consp (car p)) (car (car p)))
        (cons (cdr (car p)) (adt-live-recs (cdr p)))
      (adt-live-recs (cdr p)))))

(defun adt-kview (dir p)
  (declare (xargs :guard t))
  (if (eq dir :stack) (adt-rev (adt-live-recs p)) (adt-live-recs p)))

(defun adt-kslot-p (j k p i)
  ; slot I of P is live and its key is K
  (declare (xargs :guard t :verify-guards nil))
  (and (natp i) (< i (len p)) (consp (nth i p)) (car (nth i p))
       (equal (nth j (cdr (nth i p))) k)))

(local
 (defun adt-slot-induct (p i)
   (if (or (atom p) (zp i)) (list p i) (adt-slot-induct (cdr p) (1- i)))))

(local
 (defthm adt-nth-open-local
   (and (equal (nth 0 x) (car x))
        (implies (posp i) (equal (nth i x) (nth (1- i) (cdr x)))))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm adt-update-nth-open-local
   (and (equal (update-nth 0 v x) (cons v (cdr x)))
        (implies (posp i) (equal (update-nth i v x) (cons (car x) (update-nth (1- i) v (cdr x))))))
   :hints (("Goal" :in-theory (enable update-nth)))))

(defthm adt-kmem-of-kslot
  (implies (adt-kslot-p j k p i) (adt-kmem j k (adt-live-recs p)))
  :hints (("Goal" :induct (adt-slot-induct p i))))

(defun adt-first-kslot (j k p)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom p) nil
    (if (and (consp (car p)) (car (car p)) (equal (nth j (cdr (car p))) k))
        0
      (let ((r (adt-first-kslot j k (cdr p))))
        (if r (+ 1 r) nil)))))

(defthm adt-kslot-of-first-kslot
  (implies (adt-kmem j k (adt-live-recs p))
           (adt-kslot-p j k p (adt-first-kslot j k p))))

(defthm adt-live-recs-append
  (equal (adt-live-recs (append p q)) (append (adt-live-recs p) (adt-live-recs q))))

(defthm adt-true-listp-live-recs
  (true-listp (adt-live-recs p))
  :rule-classes :type-prescription)

(defthm adt-kfind-of-kslot
  (implies (and (adt-kslot-p j k p i) (adt-kunique j (adt-live-recs p)))
           (equal (adt-kfind j k (adt-live-recs p)) (cdr (nth i p))))
  :hints (("Goal" :induct (adt-slot-induct p i))
          ("Subgoal *1/2" :use ((:instance adt-kmem-of-kslot (p (cdr p)) (i (1- i)))))))

(defthm adt-kremove-of-kslot
  (implies (and (adt-kslot-p j k p i) (adt-kunique j (adt-live-recs p)))
           (equal (adt-live-recs (update-nth i (update-nth 0 nil (nth i p)) p))
                  (adt-kremove j k (adt-live-recs p))))
  :hints (("Goal" :induct (adt-slot-induct p i))
          ("Subgoal *1/2" :use ((:instance adt-kmem-of-kslot (p (cdr p)) (i (1- i)))))))

(defthm adt-kreplace-of-kslot
  (implies (and (adt-kslot-p j k p i) (adt-kunique j (adt-live-recs p))
                (equal (nth j r) k))
           (equal (adt-live-recs (update-nth i (cons t r) p))
                  (adt-kreplace-found j r (adt-live-recs p))))
  :hints (("Goal" :induct (adt-slot-induct p i))
          ("Subgoal *1/2" :use ((:instance adt-kmem-of-kslot (p (cdr p)) (i (1- i)))))))

(defthm adt-kupdate-of-kslot
  (implies (and (adt-kslot-p j k p i) (adt-kunique j (adt-live-recs p)) (natp f))
           (equal (adt-live-recs (update-nth i (update-nth (+ 1 f) v (nth i p)) p))
                  (adt-kupdate j k f v (adt-live-recs p))))
  :hints (("Goal" :induct (adt-slot-induct p i))
          ("Subgoal *1/2" :use ((:instance adt-kmem-of-kslot (p (cdr p)) (i (1- i)))))))

; -----------------------------------------------------------------------------
; D. The index: a hash of the key to the slots whose key has that hash.
; COVERS is the one invariant: every live slot is in its key's bucket.
; Buckets may hold anything else (dead slots, strangers); a lookup
; compares every candidate exactly.

(defun adt-fnv (l h)
  (declare (xargs :guard t))
  (if (atom l)
      (nfix h)
    (adt-fnv (cdr l) (mod (* (logxor (nfix h) (nfix (car l))) 16777619) 4294967296))))

(defun adt-khash (kd v)
  (declare (xargs :guard t))
  (if (adt-octets-kind-p kd) (adt-fnv v 2166136261) (nfix (adt-enc kd v))))

(defthm adt-natp-khash
  (natp (adt-khash kd v))
  :rule-classes :type-prescription)

(defun adt-bucket (h idx)
  (declare (xargs :guard t))
  (cdr (hons-assoc-equal h idx)))

(defthm adt-bucket-of-cons
  (equal (adt-bucket h (cons (cons h2 b) idx))
         (if (equal h h2) b (adt-bucket h idx))))

(defthm adt-member-remove-equal
  (iff (member-equal x (remove-equal y l))
       (and (member-equal x l) (not (equal x y)))))

(defthm adt-member-true-list-fix
  (iff (member-equal x (true-list-fix l)) (member-equal x l)))

(in-theory (disable adt-bucket adt-khash))

(defun adt-kcovers (kd j p i idx)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom p) t
    (and (implies (and (consp (car p)) (car (car p)))
                  (member-equal i (adt-bucket (adt-khash kd (nth j (cdr (car p)))) idx)))
         (adt-kcovers kd j (cdr p) (+ 1 (nfix i)) idx))))

(local
 (defun adt-covers-induct (p i m)
   (if (or (atom p) (zp m)) (list p i m) (adt-covers-induct (cdr p) (+ 1 (nfix i)) (1- m)))))

(defthm adt-kcovers-member
  (implies (and (adt-kcovers kd j p i idx) (natp i) (natp m) (< m (len p))
                (consp (nth m p)) (car (nth m p)))
           (member-equal (+ i m) (adt-bucket (adt-khash kd (nth j (cdr (nth m p)))) idx)))
  :hints (("Goal" :induct (adt-covers-induct p i m))))

(defthm adt-kcovers-append
  (implies (natp i)
           (equal (adt-kcovers kd j (append p q) i idx)
                  (and (adt-kcovers kd j p i idx) (adt-kcovers kd j q (+ i (len p)) idx)))))

(defthm adt-kcovers-put-cons
  (implies (adt-kcovers kd j p i idx)
           (adt-kcovers kd j p i (cons (cons h (cons n (adt-bucket h idx))) idx))))

(defthm adt-kcovers-remove-below
  (implies (and (adt-kcovers kd j p i idx) (natp i) (natp m) (< m i))
           (adt-kcovers kd j p i (cons (cons h (remove-equal m (true-list-fix (adt-bucket h idx)))) idx))))

(defthm adt-kcovers-kill
  (implies (and (adt-kcovers kd j p i idx) (natp i) (natp m) (< m (len p))
                (equal h (adt-khash kd (nth j (cdr (nth m p))))))
           (adt-kcovers kd j (update-nth m (update-nth 0 nil (nth m p)) p) i
                        (cons (cons h (remove-equal (+ i m) (true-list-fix (adt-bucket h idx)))) idx)))
  :hints (("Goal" :induct (adt-covers-induct p i m))))

(defthm adt-kcovers-same-key
  (implies (and (adt-kcovers kd j p i idx) (natp m) (< m (len p))
                (consp y) (consp (nth m p))
                (iff (car y) (car (nth m p)))
                (equal (nth j (cdr y)) (nth j (cdr (nth m p)))))
           (adt-kcovers kd j (update-nth m y p) i idx))
  :hints (("Goal" :induct (adt-covers-induct p i m))))

(local (in-theory (disable adt-nth-open-local adt-update-nth-open-local)))

(defthm adt-nth-1+
  (implies (natp j) (equal (nth (+ 1 j) x) (nth j (cdr x))))
  :hints (("Goal" :in-theory (enable nth))))

(defthm adt-nth-0
  (equal (nth 0 x) (car x))
  :hints (("Goal" :in-theory (enable nth))))

; The lookup: walk the key's bucket; a candidate answers only when its slot
; is in range, live, and its key is EXACTLY K.
(defun adt-kgood (s j k i c)
  (declare (xargs :verify-guards nil))
  (and (natp i) (< i (nfix (adt-count-c s c)))
       (adt-get-okp s 0 i c) (adt-get-c s 0 i c)
       (adt-get-okp s (+ 1 (nfix j)) i c)
       (equal (adt-get-c s (+ 1 (nfix j)) i c) k)))

(defthm adt-natp-when-kgood
  (implies (adt-kgood s j k i c) (natp i))
  :rule-classes :forward-chaining)

(defun adt-kwalk (s j k b c)
  (declare (xargs :verify-guards nil))
  (if (atom b) nil
    (if (adt-kgood s j k (car b) c) (car b) (adt-kwalk s j k (cdr b) c))))

(defthm adt-kwalk-sound
  (implies (adt-kwalk s j k b c)
           (and (adt-kgood s j k (adt-kwalk s j k b c) c)
                (member-equal (adt-kwalk s j k b c) b)))
  :hints (("Goal" :induct (adt-kwalk s j k b c))))

(defthm adt-kwalk-complete
  (implies (and (member-equal i b) (adt-kgood s j k i c))
           (adt-kwalk s j k b c)))

(defthm adt-kgood-of-corr
  (implies (and (adt-corr (adt-pschema s) c p) (natp j) (< j (len s)))
           (iff (adt-kgood (adt-pschema s) j k i c) (adt-kslot-p j k p i)))
  :hints (("Goal" :in-theory (enable adt-corr-count adt-kgood)
           :use ((:instance adt-corr-get (s (adt-pschema s)) (a p) (j 0))
                 (:instance adt-corr-get (s (adt-pschema s)) (a p) (j (+ 1 j)))
                 (:instance adt-rec-p-of-nth (s (adt-pschema s)) (a p))))))

(in-theory (disable adt-kgood))

; -----------------------------------------------------------------------------
; E. Flat-level helpers: fields above the fill are not the sequence's, a
; whole record is written field by field, a row is read with every read
; checked.

(defthm adt-nth-above-of-put-field
  (implies (and (natp m) (natp ci) (natp p) (<= (+ ci (adt-kind-width kd)) p) (< (+ 2 p) m))
           (equal (nth m (adt-put-field kd ci p n v c)) (nth m c)))
  :hints (("Goal" :in-theory (enable adt-put-field adt-pool-push adt-pool-room adt-poolw-is-pool-writes))))

(defthm adt-nth-above-of-append-fields
  (implies (and (natp m) (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p) (< (+ 2 p) m))
           (equal (nth m (adt-append-fields s ci p n rec c)) (nth m c)))
  :hints (("Goal" :in-theory (enable adt-append-fields)
           :induct (adt-append-fields s ci p n rec c))))

(defthm adt-nth-above-of-set-fields
  (implies (and (natp m) (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p) (< (+ 2 p) m))
           (equal (nth m (adt-set-fields s j ci p i v c)) (nth m c)))
  :hints (("Goal" :in-theory (enable adt-set-fields)
           :induct (adt-set-fields s j ci p i v c))))

(defthm adt-nth-above-of-append-c
  (implies (and (natp m) (< (+ 2 (adt-ncols s)) m))
           (equal (nth m (adt-append-c s rec c)) (nth m c)))
  :hints (("Goal" :in-theory (enable adt-append-c))))

(defthm adt-nth-above-of-set-c
  (implies (and (natp m) (< (+ 2 (adt-ncols s)) m))
           (equal (nth m (adt-set-c s j i v c)) (nth m c)))
  :hints (("Goal" :in-theory (enable adt-set-c))))

(local
 (defthm adt-cols-shape-of-update-above
   (implies (and (adt-cols-shape s ci c) (natp ci) (natp m) (<= (+ ci (adt-ncols s)) m))
            (adt-cols-shape s ci (update-nth m x c)))
   :hints (("Goal" :in-theory (enable adt-cols-shape)))))

(local
 (defthm adt-fill-okp-of-update-other
   (implies (and (natp m) (natp p) (not (equal m p)) (not (equal m (+ 2 p))))
            (equal (adt-fill-okp p (update-nth m x c)) (adt-fill-okp p c)))
   :hints (("Goal" :in-theory (enable adt-fill-okp)))))

(defthm adt-corr-of-update-above
  (implies (and (adt-corr s c a) (natp m) (< (+ 2 (adt-ncols s)) m))
           (adt-corr s (update-nth m x c) a))
  :hints (("Goal" :in-theory (e/d (adt-corr adt-shape-p)
                                  (adt-fields-corr adt-cols-shape adt-fill-okp adt-seq-p
                                   adt-schemap adt-ncols adt-all-elt-p)))))

(defun adt-set-rec-c (s m r i c)
  ; write fields M, M+1, ... of row I from R
  (declare (xargs :measure (nfix (- (len s) (nfix m))) :verify-guards nil))
  (if (and (natp m) (< m (len s)))
      (adt-set-rec-c s (+ 1 m) (cdr r) i (adt-set-c s m i (car r) c))
    c))

(local
 (defun adt-setrec-induct (s m r i c a)
   (declare (xargs :measure (nfix (- (len s) (nfix m))) :verify-guards nil))
   (if (and (natp m) (< m (len s)))
       (adt-setrec-induct s (+ 1 m) (cdr r) i (adt-set-c s m i (car r) c) (adt-set-a m i (car r) a))
     (list r c a))))

(local
 (defun adt-mx-induct (m x)
   (if (zp m) (list m x) (adt-mx-induct (1- m) (cdr x)))))

(local
 (defthm adt-take-update-nth-last
   (implies (and (natp m) (< m (len x)))
            (equal (append (take (+ 1 m) (update-nth m v x)) rest)
                   (append (take m x) (cons v rest))))
   :hints (("Goal" :induct (adt-mx-induct m x)
            :in-theory (e/d (update-nth) (adt-take-open adt-car-of-update-nth adt-cdr-of-update-nth
                                          adt-take-nthcdr-open))))))

(local
 (defthm adt-nth-update-nth-same-local
   (equal (nth i (update-nth i v x)) v)
   :hints (("Goal" :in-theory (enable nth update-nth)))))

(local
 (defthm adt-rec-p-nthcdr-step
   (implies (and (adt-rec-p (nthcdr m s) r) (natp m) (< m (len s)))
            (and (adt-val-okp (nth m s) (car r))
                 (consp r)
                 (adt-rec-p (nthcdr (+ 1 m) s) (cdr r))))
   :hints (("Goal" :expand ((adt-rec-p (nthcdr m s) r))
            :in-theory (e/d (adt-rec-p) (adt-cdr-nthcdr))
            :use ((:instance adt-cdr-nthcdr (j m) (r s)))))))

(local
 (defthm adt-nthcdr-len-nil-0
   (implies (and (natp m) (<= (len s) m)) (not (consp (nthcdr m s))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm adt-rec-p-nthcdr-end
   (implies (and (natp m) (<= (len s) m))
            (equal (adt-rec-p (nthcdr m s) r) (null r)))
   :hints (("Goal" :expand ((adt-rec-p (nthcdr m s) r))
            :in-theory (enable adt-rec-p)))))

(local
 (defthm adt-set-a-facts
   (implies (and (natp i) (< i (len a)))
            (and (equal (nth i (adt-set-a m i v a)) (update-nth m v (nth i a)))
                 (equal (len (adt-set-a m i v a)) (len a))
                 (equal (update-nth i x (adt-set-a m i v a)) (update-nth i x a))))
   :hints (("Goal" :in-theory (enable adt-set-a)))))

(local
 (defthm adt-corr-set-rec-step-shape
   (implies (and (natp m) (< m (len rec)) (consp r))
            (equal (append (take (+ 1 m) (update-nth m (car r) rec)) (cdr r))
                   (append (take m rec) r)))
   :hints (("Goal" :use ((:instance adt-take-update-nth-last (x rec) (v (car r)) (rest (cdr r))))
            :in-theory (union-theories (theory 'minimal-theory) '(cons-car-cdr))))))

(local
 (defthm adt-nthcdr-len-nil
   (implies (and (natp m) (<= (len s) m)) (not (consp (nthcdr m s))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm adt-corr-set-rec
  (implies (and (adt-corr s c a) (natp m) (<= m (len s)) (natp i) (< i (len a))
                (adt-rec-p (nthcdr m s) r))
           (adt-corr s (adt-set-rec-c s m r i c)
                     (update-nth i (append (take m (nth i a)) r) a)))
  :hints (("Goal" :induct (adt-setrec-induct s m r i c a)
           :in-theory (disable adt-take-nthcdr-open adt-take-open take))
          ("Subgoal *1/2" :use ((:instance adt-rec-p-of-nth (a a))
                                (:instance adt-len-when-rec-p (r (nth i a)))
                                (:instance adt-take-len-schema-of-rec (r (nth i a))))
           :in-theory (disable adt-len-when-rec-p adt-take-len-schema-of-rec
                               adt-take-nthcdr-open adt-take-open take))
          ("Subgoal *1/1" :use ((:instance adt-rec-p-of-nth (a a))
                                (:instance adt-len-when-rec-p (r (nth i a))))
           :in-theory (disable adt-len-when-rec-p adt-take-len-schema-of-rec
                               adt-take-nthcdr-open adt-take-open take))))

(defthm adt-nth-above-of-set-rec-c
  (implies (and (natp mm) (< (+ 2 (adt-ncols s)) mm))
           (equal (nth mm (adt-set-rec-c s m r i c)) (nth mm c))))

(defun adt-row-okc (s m n i c)
  (declare (xargs :verify-guards nil))
  (if (zp n)
      nil
    (cons (if (adt-get-okp s m i c) (adt-get-c s m i c) nil)
          (adt-row-okc s (+ 1 (nfix m)) (1- n) i c))))

(defthm adt-row-okc-of-corr
  (implies (and (adt-corr s c a) (natp i) (< i (len a)) (natp m) (<= (+ m (nfix n)) (len s)))
           (equal (adt-row-okc s m n i c) (take n (nthcdr m (nth i a)))))
  :hints (("Goal" :induct (adt-row-okc s m n i c))))

; -----------------------------------------------------------------------------
; F. The keyed operations on the image, and the keyed correspondence.
; S is the USER schema; the image is over (adt-pschema S), with the index
; one field above the fill.

(defun adt-kidx (s c)
  (declare (xargs :verify-guards nil))
  (nth (+ 3 (adt-ncols (adt-pschema s))) c))

(defun adt-kput (s h b c)
  (declare (xargs :verify-guards nil))
  (update-nth (+ 3 (adt-ncols (adt-pschema s))) (cons (cons h b) (adt-kidx s c)) c))

(defun adt-klookup-c (s j k c)
  (declare (xargs :verify-guards nil))
  (adt-kwalk (adt-pschema s) j k (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c)) c))

(defun adt-kfind-c (s j k c)
  (declare (xargs :verify-guards nil))
  (let ((i (adt-klookup-c s j k c)))
    (if i (adt-row-okc (adt-pschema s) 1 (len s) i c) nil)))

(defun adt-kget-c (s j k f c)
  (declare (xargs :verify-guards nil))
  (let ((i (adt-klookup-c s j k c)))
    (if (and i (adt-get-okp (adt-pschema s) (+ 1 (nfix f)) i c))
        (adt-get-c (adt-pschema s) (+ 1 (nfix f)) i c)
      nil)))

(defun adt-kinsert-c (s j r c)
  (declare (xargs :verify-guards nil))
  (let* ((n (nfix (adt-count-c (adt-pschema s) c)))
         (h (adt-khash (nth j s) (nth j r)))
         (b (adt-bucket h (adt-kidx s c))))
    (adt-kput s h (cons n b) (adt-append-c (adt-pschema s) (cons t r) c))))

(defun adt-kremove-c (s j k c)
  (declare (xargs :verify-guards nil))
  (let* ((h (adt-khash (nth j s) k))
         (b (adt-bucket h (adt-kidx s c)))
         (i (adt-kwalk (adt-pschema s) j k b c)))
    (if i
        (adt-kput s h (remove-equal i (true-list-fix b)) (adt-set-c (adt-pschema s) 0 i nil c))
      c)))

(defun adt-kreplace-c (s j r c)
  (declare (xargs :verify-guards nil))
  (let ((i (adt-klookup-c s j (nth j r) c)))
    (if i
        (adt-set-rec-c (adt-pschema s) 1 r i c)
      (adt-kinsert-c s j r c))))

(defun adt-kupdate-c (s j k f v c)
  (declare (xargs :verify-guards nil))
  (let ((i (adt-klookup-c s j k c)))
    (if i (adt-set-c (adt-pschema s) (+ 1 (nfix f)) i v c) c)))

(defun adt-kcorr (s dir j c a)
  (declare (xargs :verify-guards nil))
  (let ((p (adt-abs (adt-pschema s) c)))
    (and (adt-corr (adt-pschema s) c p)
         (natp j) (< j (len s))
         (equal (adt-kview dir p) a)
         (adt-kunique j a)
         (adt-kcovers (nth j s) j p 0 (adt-kidx s c)))))

(in-theory (disable adt-kidx adt-kput))

(defthm adt-kcorr-facts
  (implies (adt-kcorr s dir j c a)
           (and (adt-corr (adt-pschema s) c (adt-abs (adt-pschema s) c))
                (natp j) (< j (len s))
                (adt-kcovers (nth j s) j (adt-abs (adt-pschema s) c) 0 (adt-kidx s c))))
  :rule-classes :forward-chaining)

(defthm adt-live-recs-unique-of-kview
  (equal (adt-kunique j (adt-kview dir p)) (adt-kunique j (adt-live-recs p))))

(defthm adt-kmem-of-kview
  (equal (adt-kmem j k (adt-kview dir p)) (adt-kmem j k (adt-live-recs p))))

(defthm adt-klookup-some
  (implies (and (adt-corr (adt-pschema s) c p) (natp j) (< j (len s))
                (adt-kwalk (adt-pschema s) j k b c))
           (adt-kslot-p j k p (adt-kwalk (adt-pschema s) j k b c)))
  :hints (("Goal" :use ((:instance adt-kwalk-sound (s (adt-pschema s)))
                        (:instance adt-kgood-of-corr (i (adt-kwalk (adt-pschema s) j k b c))))
           :in-theory (disable adt-kwalk-sound adt-kgood-of-corr adt-kslot-p))))

(defthm adt-klookup-none
  (implies (and (adt-corr (adt-pschema s) c p) (natp j) (< j (len s))
                (adt-kcovers (nth j s) j p 0 idx)
                (not (adt-kwalk (adt-pschema s) j k (adt-bucket (adt-khash (nth j s) k) idx) c)))
           (not (adt-kmem j k (adt-live-recs p))))
  :hints (("Goal" :use ((:instance adt-kslot-of-first-kslot)
                        (:instance adt-kgood-of-corr (i (adt-first-kslot j k p)))
                        (:instance adt-kcovers-member (kd (nth j s)) (i 0) (m (adt-first-kslot j k p)))
                        (:instance adt-kwalk-complete (s (adt-pschema s)) (i (adt-first-kslot j k p))
                                   (b (adt-bucket (adt-khash (nth j s) k) idx))))
           :in-theory (disable adt-kslot-of-first-kslot adt-kgood-of-corr adt-kcovers-member
                               adt-kwalk-complete adt-kwalk))))

; The keystones.  Each is stated over adt-kcorr and the library operation;
; an instance's bridge equates its executable with the operation, and the
; defabsstobj obligations close by these.

(defun adt-kempty-c (s)
  (declare (xargs :verify-guards nil))
  (append (adt-empty-c (adt-pschema s)) (list nil)))

(local
 (defthm adt-len-nils-local
   (equal (len (adt-nils n)) (nfix n))))

(local
 (defthm adt-update-nth-len-is-append
   (implies (true-listp l) (equal (update-nth (len l) x l) (append l (list x))))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm adt-empty-c-facts
   (and (true-listp (adt-empty-c s))
        (equal (len (adt-empty-c s)) (+ 3 (adt-ncols s))))
   :hints (("Goal" :in-theory (enable adt-empty-c)))))

(defthm adt-kunique-nil
  (adt-kunique j nil)
  :hints (("Goal" :in-theory (enable adt-kunique))))

(defthm adt-kcorr-empty
  (implies (and (adt-schemap s) (natp j) (< j (len s)))
           (adt-kcorr s dir j (adt-kempty-c s) nil))
  :hints (("Goal" :in-theory (e/d (adt-kempty-c adt-kidx)
                                  (adt-empty-c adt-update-nth-len-is-append adt-corr-of-update-above
                                   adt-abs-of-corr adt-corr-empty))
           :use ((:instance adt-corr-empty (s (adt-pschema s)))
                 (:instance adt-update-nth-len-is-append (l (adt-empty-c (adt-pschema s))) (x nil))
                 (:instance adt-corr-of-update-above (s (adt-pschema s)) (c (adt-empty-c (adt-pschema s)))
                            (a nil) (m (+ 3 (adt-ncols (adt-pschema s)))) (x nil))
                 (:instance adt-abs-of-corr (s (adt-pschema s)) (a nil)
                            (c (append (adt-empty-c (adt-pschema s)) (list nil))))))))

(local
 (defthm adt-kview-append-live
   (equal (adt-kview dir (append p (list (cons t r))))
          (adt-kinsert dir r (adt-kview dir p)))))

(defthm adt-kcorr-insert
  (implies (and (adt-kcorr s dir j c a) (adt-rec-p s r) (not (adt-kmem j (nth j r) a)))
           (adt-kcorr s dir j (adt-kinsert-c s j r c) (adt-kinsert dir r a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kput adt-kidx) (adt-kinsert adt-kview adt-abs-of-corr adt-corr-append
                                                            adt-corr-of-update-above))
           :use ((:instance adt-abs-of-corr (s (adt-pschema s))
                            (c (adt-kinsert-c s j r c))
                            (a (append (adt-abs (adt-pschema s) c) (list (cons t r)))))
                 (:instance adt-corr-append (s (adt-pschema s)) (rec (cons t r))
                            (a (adt-abs (adt-pschema s) c)))
                 (:instance adt-corr-of-update-above (s (adt-pschema s))
                            (c (adt-append-c (adt-pschema s) (cons t r) c))
                            (a (append (adt-abs (adt-pschema s) c) (list (cons t r))))
                            (m (+ 3 (adt-ncols (adt-pschema s))))
                            (x (cons (cons (adt-khash (nth j s) (nth j r))
                                           (cons (nfix (adt-count-c (adt-pschema s) c))
                                                 (adt-bucket (adt-khash (nth j s) (nth j r))
                                                             (adt-kidx s c))))
                                     (adt-kidx s c))))
                 (:instance adt-corr-count (s (adt-pschema s)) (a (adt-abs (adt-pschema s) c)))))))

; One slot's live bit cleared, and the slot dropped from its bucket.
(defthm adt-kcorr-kill
  (implies (and (adt-kcorr s dir j c a)
                (adt-kslot-p j k (adt-abs (adt-pschema s) c) i)
                (equal b (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c))))
           (adt-kcorr s dir j
                      (adt-kput s (adt-khash (nth j s) k) (remove-equal i (true-list-fix b))
                                (adt-set-c (adt-pschema s) 0 i nil c))
                      (adt-kremove j k a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kput adt-kidx adt-kslot-p)
                           (adt-abs-of-corr adt-corr-set adt-corr-of-update-above adt-kcovers-kill
                                            adt-kremove-of-kslot))
           :use ((:instance adt-corr-set (s (adt-pschema s)) (a (adt-abs (adt-pschema s) c)) (j 0) (v nil))
                 (:instance adt-corr-of-update-above (s (adt-pschema s))
                            (c (adt-set-c (adt-pschema s) 0 i nil c))
                            (a (adt-set-a 0 i nil (adt-abs (adt-pschema s) c)))
                            (m (+ 3 (adt-ncols (adt-pschema s))))
                            (x (cons (cons (adt-khash (nth j s) k) (remove-equal i (true-list-fix b)))
                                     (adt-kidx s c))))
                 (:instance adt-abs-of-corr (s (adt-pschema s))
                            (c (update-nth (+ 3 (adt-ncols (adt-pschema s)))
                                           (cons (cons (adt-khash (nth j s) k) (remove-equal i (true-list-fix b)))
                                                 (adt-kidx s c))
                                           (adt-set-c (adt-pschema s) 0 i nil c)))
                            (a (adt-set-a 0 i nil (adt-abs (adt-pschema s) c))))
                 (:instance adt-kremove-of-kslot (p (adt-abs (adt-pschema s) c)))
                 (:instance adt-kcovers-kill (kd (nth j s)) (p (adt-abs (adt-pschema s) c)) (i 0) (m i)
                            (idx (adt-kidx s c)) (h (adt-khash (nth j s) k)))))
          ("Goal'" :in-theory (e/d (adt-kput adt-kidx adt-kslot-p adt-set-a)
                                   (adt-abs-of-corr adt-corr-set adt-corr-of-update-above adt-kcovers-kill
                                                    adt-kremove-of-kslot)))))

(defthm adt-kcorr-remove
  (implies (adt-kcorr s dir j c a)
           (adt-kcorr s dir j (adt-kremove-c s j k c) (adt-kremove j k a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kremove-c) (adt-kcorr adt-kcorr-kill adt-klookup-some adt-klookup-none
                                            adt-kwalk))
           :cases ((adt-kwalk (adt-pschema s) j k (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c)) c)))
          ("Subgoal 2"
           :in-theory (e/d (adt-kremove-c adt-kcorr) (adt-kcorr-kill adt-klookup-some adt-klookup-none
                                                      adt-kwalk))
           :use ((:instance adt-klookup-none (p (adt-abs (adt-pschema s) c)) (idx (adt-kidx s c)))))
          ("Subgoal 1"
           :use ((:instance adt-klookup-some (p (adt-abs (adt-pschema s) c))
                            (b (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c))))
                 (:instance adt-kcorr-kill
                            (i (adt-kwalk (adt-pschema s) j k (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c)) c))
                            (b (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c))))))))

(local
 (defthm adt-nthcdr-1
   (equal (nthcdr 1 x) (cdr x))
   :hints (("Goal" :expand ((nthcdr 1 x))))))

(defthm adt-kidx-of-ops
  (and (equal (adt-kidx s (adt-kput s h b c)) (cons (cons h b) (adt-kidx s c)))
       (equal (adt-kidx s (adt-set-c (adt-pschema s) m i v c)) (adt-kidx s c))
       (equal (adt-kidx s (adt-append-c (adt-pschema s) rec c)) (adt-kidx s c))
       (equal (adt-kidx s (adt-set-rec-c (adt-pschema s) m r i c)) (adt-kidx s c)))
  :hints (("Goal" :in-theory (enable adt-kidx adt-kput))))

(local
 (defthm adt-live-slot-rec
   (implies (and (adt-corr (adt-pschema s) c p) (adt-kslot-p j k p i))
            (and (adt-rec-p (adt-pschema s) (nth i p))
                 (equal (car (nth i p)) t)
                 (adt-rec-p s (cdr (nth i p)))))
   :hints (("Goal" :use ((:instance adt-rec-p-of-nth (s (adt-pschema s)) (a p)))
            :in-theory (e/d (adt-kslot-p) (adt-rec-p-of-nth))))))

(defthm adt-kcorr-find-at
  (implies (and (adt-kcorr s dir j c a) (adt-kslot-p j k (adt-abs (adt-pschema s) c) i))
           (equal (adt-row-okc (adt-pschema s) 1 (len s) i c) (adt-kfind j k a)))
  :hints (("Goal" :in-theory (e/d (adt-kcorr adt-kslot-p) (adt-live-slot-rec adt-kfind-of-kslot))
           :use ((:instance adt-live-slot-rec (p (adt-abs (adt-pschema s) c)))
                 (:instance adt-kfind-of-kslot (p (adt-abs (adt-pschema s) c)))
                 (:instance adt-take-len-schema-of-rec (r (cdr (nth i (adt-abs (adt-pschema s) c)))))))))

(defthm adt-kcorr-find
  (implies (adt-kcorr s dir j c a)
           (equal (adt-kfind-c s j k c) (adt-kfind j k a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kfind-c) (adt-kcorr adt-kcorr-find-at adt-klookup-some adt-klookup-none adt-kwalk))
           :cases ((adt-klookup-c s j k c)))
          ("Subgoal 2"
           :in-theory (e/d (adt-kfind-c adt-kcorr) (adt-kcorr-find-at adt-klookup-some adt-klookup-none adt-kwalk))
           :use ((:instance adt-klookup-none (p (adt-abs (adt-pschema s) c)) (idx (adt-kidx s c)))))
          ("Subgoal 1"
           :use ((:instance adt-klookup-some (p (adt-abs (adt-pschema s) c))
                            (b (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c))))
                 (:instance adt-kcorr-find-at (i (adt-klookup-c s j k c)))))))

(defthm adt-kcorr-get-at
  (implies (and (adt-kcorr s dir j c a) (adt-kslot-p j k (adt-abs (adt-pschema s) c) i)
                (natp f) (< f (len s)))
           (and (adt-get-okp (adt-pschema s) (+ 1 f) i c)
                (equal (adt-get-c (adt-pschema s) (+ 1 f) i c) (nth f (adt-kfind j k a)))))
  :hints (("Goal" :in-theory (e/d (adt-kslot-p) (adt-kcorr-find-at adt-corr-get))
           :use ((:instance adt-kcorr-find-at)
                 (:instance adt-corr-get (s (adt-pschema s)) (a (adt-abs (adt-pschema s) c)) (j (+ 1 f)))
                 (:instance adt-row-okc-of-corr (s (adt-pschema s)) (a (adt-abs (adt-pschema s) c))
                            (m 1) (n (len s)))
                 (:instance adt-live-slot-rec (p (adt-abs (adt-pschema s) c)))
                 (:instance adt-take-len-schema-of-rec (r (cdr (nth i (adt-abs (adt-pschema s) c)))))))))

(defthm adt-kcorr-get
  (implies (and (adt-kcorr s dir j c a) (natp f) (< f (len s)))
           (equal (adt-kget-c s j k f c) (nth f (adt-kfind j k a))))
  :hints (("Goal"
           :in-theory (e/d (adt-kget-c) (adt-kcorr adt-kcorr-get-at adt-klookup-some adt-klookup-none adt-kwalk))
           :cases ((adt-klookup-c s j k c)))
          ("Subgoal 2"
           :in-theory (e/d (adt-kget-c adt-kcorr) (adt-kcorr-get-at adt-klookup-some adt-klookup-none adt-kwalk))
           :use ((:instance adt-klookup-none (p (adt-abs (adt-pschema s) c)) (idx (adt-kidx s c)))))
          ("Subgoal 1"
           :use ((:instance adt-klookup-some (p (adt-abs (adt-pschema s) c))
                            (b (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c))))
                 (:instance adt-kcorr-get-at (i (adt-klookup-c s j k c)))))))

(defthm adt-kunique-kreplace-found
  (equal (adt-kunique j (adt-kreplace-found j r a)) (adt-kunique j a))
  :hints (("Goal" :in-theory (enable adt-kunique))))

(local
 (defthm adt-append-take-1
   (equal (append (take 1 x) r) (cons (car x) r))
   :hints (("Goal" :expand ((take 1 x))))))

(defthm adt-kcorr-setrec-at
  (implies (and (adt-kcorr s dir j c a) (adt-kslot-p j k (adt-abs (adt-pschema s) c) i)
                (adt-rec-p s r) (equal (nth j r) k))
           (adt-kcorr s dir j (adt-set-rec-c (adt-pschema s) 1 r i c) (adt-kreplace-found j r a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kslot-p)
                           (adt-abs-of-corr adt-corr-set-rec adt-kreplace-of-kslot adt-kcovers-same-key
                                            adt-live-slot-rec))
           :use ((:instance adt-live-slot-rec (p (adt-abs (adt-pschema s) c)))
                 (:instance adt-corr-set-rec (s (adt-pschema s)) (a (adt-abs (adt-pschema s) c)) (m 1))
                 (:instance adt-abs-of-corr (s (adt-pschema s))
                            (c (adt-set-rec-c (adt-pschema s) 1 r i c))
                            (a (update-nth i (cons t r) (adt-abs (adt-pschema s) c))))
                 (:instance adt-kreplace-of-kslot (p (adt-abs (adt-pschema s) c)))
                 (:instance adt-kcovers-same-key (kd (nth j s)) (p (adt-abs (adt-pschema s) c)) (i 0) (m i)
                            (idx (adt-kidx s c)) (y (cons t r)))))))

(defthm adt-kcorr-kmem
  (implies (adt-kcorr s dir j c a)
           (equal (adt-kmem j k a) (adt-kmem j k (adt-live-recs (adt-abs (adt-pschema s) c)))))
  :rule-classes nil)

(defthm adt-kcorr-replace
  (implies (and (adt-kcorr s dir j c a) (adt-rec-p s r))
           (adt-kcorr s dir j (adt-kreplace-c s j r c) (adt-kreplace dir j r a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kreplace-c adt-kreplace)
                           (adt-kcorr adt-kcorr-setrec-at adt-klookup-some adt-klookup-none adt-kwalk
                                      adt-kcorr-insert adt-kinsert-c))
           :cases ((adt-klookup-c s j (nth j r) c)))
          ("Subgoal 2"
           :use ((:instance adt-klookup-none (k (nth j r)) (p (adt-abs (adt-pschema s) c)) (idx (adt-kidx s c)))
                 (:instance adt-kcorr-kmem (k (nth j r)))
                 (:instance adt-kcorr-insert)))
          ("Subgoal 1"
           :use ((:instance adt-kcorr-kmem (k (nth j r)))
                 (:instance adt-klookup-some (k (nth j r)) (p (adt-abs (adt-pschema s) c))
                            (b (adt-bucket (adt-khash (nth j s) (nth j r)) (adt-kidx s c))))
                 (:instance adt-kmem-of-kslot (k (nth j r)) (p (adt-abs (adt-pschema s) c))
                            (i (adt-klookup-c s j (nth j r) c)))
                 (:instance adt-kcorr-setrec-at (k (nth j r)) (i (adt-klookup-c s j (nth j r) c)))))))

(defthm adt-kcorr-setfield-at
  (implies (and (adt-kcorr s dir j c a) (adt-kslot-p j k (adt-abs (adt-pschema s) c) i)
                (natp f) (< f (len s)) (not (equal f j)) (adt-val-okp (nth f s) v))
           (adt-kcorr s dir j (adt-set-c (adt-pschema s) (+ 1 f) i v c) (adt-kupdate j k f v a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kslot-p adt-set-a)
                           (adt-abs-of-corr adt-corr-set adt-kupdate-of-kslot adt-kcovers-same-key
                                            adt-live-slot-rec))
           :use ((:instance adt-live-slot-rec (p (adt-abs (adt-pschema s) c)))
                 (:instance adt-corr-set (s (adt-pschema s)) (a (adt-abs (adt-pschema s) c)) (j (+ 1 f)))
                 (:instance adt-abs-of-corr (s (adt-pschema s))
                            (c (adt-set-c (adt-pschema s) (+ 1 f) i v c))
                            (a (adt-set-a (+ 1 f) i v (adt-abs (adt-pschema s) c))))
                 (:instance adt-kupdate-of-kslot (p (adt-abs (adt-pschema s) c)))
                 (:instance adt-kcovers-same-key (kd (nth j s)) (p (adt-abs (adt-pschema s) c)) (i 0) (m i)
                            (idx (adt-kidx s c))
                            (y (update-nth (+ 1 f) v (nth i (adt-abs (adt-pschema s) c)))))))))

(defthm adt-kcorr-update
  (implies (and (adt-kcorr s dir j c a) (natp f) (< f (len s)) (not (equal f j))
                (adt-val-okp (nth f s) v))
           (adt-kcorr s dir j (adt-kupdate-c s j k f v c) (adt-kupdate j k f v a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kupdate-c)
                           (adt-kcorr adt-kcorr-setfield-at adt-klookup-some adt-klookup-none adt-kwalk))
           :cases ((adt-klookup-c s j k c)))
          ("Subgoal 2"
           :in-theory (e/d (adt-kupdate-c adt-kcorr)
                           (adt-kcorr-setfield-at adt-klookup-some adt-klookup-none adt-kwalk))
           :use ((:instance adt-klookup-none (p (adt-abs (adt-pschema s) c)) (idx (adt-kidx s c)))))
          ("Subgoal 1"
           :use ((:instance adt-klookup-some (p (adt-abs (adt-pschema s) c))
                            (b (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c))))
                 (:instance adt-kcorr-setfield-at (i (adt-klookup-c s j k c)))))))

; -----------------------------------------------------------------------------
; G. The logical recognizer is preserved (each instance's {PRESERVED}).

(defthm adt-seq-p-kremove
  (implies (adt-seq-p s a) (adt-seq-p s (adt-kremove j k a))))

(defthm adt-seq-p-kinsert
  (implies (and (adt-seq-p s a) (adt-rec-p s r)) (adt-seq-p s (adt-kinsert dir r a))))

(defthm adt-seq-p-kreplace-found
  (implies (and (adt-seq-p s a) (adt-rec-p s r)) (adt-seq-p s (adt-kreplace-found j r a))))

(defthm adt-seq-p-kreplace
  (implies (and (adt-seq-p s a) (adt-rec-p s r)) (adt-seq-p s (adt-kreplace dir j r a)))
  :hints (("Goal" :in-theory (disable adt-kinsert))))

(defthm adt-seq-p-kupdate
  (implies (and (adt-seq-p s a) (natp f) (< f (len s)) (adt-val-okp (nth f s) v))
           (adt-seq-p s (adt-kupdate j k f v a))))

(defthm adt-true-list-listp-when-seq-p
  (implies (adt-seq-p s a) (true-list-listp a))
  :hints (("Goal" :in-theory (enable adt-rec-p))))

; -----------------------------------------------------------------------------
; H. The one recursive shape a keyed instance adds: its bucket walk, as a
; constrained function (an instance's walk is a functional instance).

(encapsulate
  (((adt-g-ks) => *) ((adt-g-kj) => *) ((adt-g-kwalk * * *) => *))
  (local (defun adt-g-ks () nil))
  (local (defun adt-g-kj () 0))
  (local (defun adt-g-kwalk (k b c) (adt-kwalk (adt-g-ks) (adt-g-kj) k b c)))
  (defthm adt-g-kwalk-def
    (equal (adt-g-kwalk k b c)
           (if (atom b)
               nil
             (if (adt-kgood (adt-g-ks) (adt-g-kj) k (car b) c)
                 (car b)
               (adt-g-kwalk k (cdr b) c))))
    :rule-classes nil))

(local
 (defun adt-g-kwalk-induct (b)
   (if (atom b) b (adt-g-kwalk-induct (cdr b)))))

(defthm adt-g-kwalk-is-kwalk
  (equal (adt-g-kwalk k b c) (adt-kwalk (adt-g-ks) (adt-g-kj) k b c))
  :hints (("Goal" :induct (adt-g-kwalk-induct b))
          ("Subgoal *1/2" :use ((:instance adt-g-kwalk-def)))
          ("Subgoal *1/1" :use ((:instance adt-g-kwalk-def)))))

; Openers on a constant schema (an instance's by-definition bridges).
(defthm adt-row-okc-open
  (implies (and (syntaxp (quotep n)) (not (zp n)))
           (equal (adt-row-okc s m n i c)
                  (cons (if (adt-get-okp s m i c) (adt-get-c s m i c) nil)
                        (adt-row-okc s (+ 1 (nfix m)) (1- n) i c)))))

(defthm adt-row-okc-zero
  (implies (zp n) (equal (adt-row-okc s m n i c) nil)))

(defthm adt-set-rec-c-open
  (implies (and (syntaxp (and (quotep s) (quotep m))) (natp m) (< m (len s)))
           (equal (adt-set-rec-c s m r i c)
                  (adt-set-rec-c s (+ 1 m) (cdr r) i (adt-set-c s m i (car r) c)))))

(defthm adt-set-rec-c-end
  (implies (and (syntaxp (and (quotep s) (quotep m))) (natp m) (<= (len s) m))
           (equal (adt-set-rec-c s m r i c) c)))

(defun adt-kmem-c (s j k c)
  (declare (xargs :verify-guards nil))
  (if (adt-klookup-c s j k c) t nil))

(defthm adt-kcorr-mem
  (implies (adt-kcorr s dir j c a)
           (equal (adt-kmem-c s j k c) (adt-kmem j k a)))
  :hints (("Goal"
           :in-theory (e/d (adt-kmem-c) (adt-kcorr adt-klookup-some adt-klookup-none adt-kwalk))
           :use ((:instance adt-kcorr-kmem)
                 (:instance adt-klookup-none (p (adt-abs (adt-pschema s) c)) (idx (adt-kidx s c)))
                 (:instance adt-klookup-some (p (adt-abs (adt-pschema s) c))
                            (b (adt-bucket (adt-khash (nth j s) k) (adt-kidx s c))))
                 (:instance adt-kmem-of-kslot (p (adt-abs (adt-pschema s) c))
                            (i (adt-klookup-c s j k c)))))))

(defthm adt-natp-kwalk
  (implies (adt-kwalk s j k b c) (natp (adt-kwalk s j k b c)))
  :hints (("Goal" :use adt-kwalk-sound :in-theory (disable adt-kwalk-sound))))

(defthm adt-natp-klookup
  (implies (adt-klookup-c s j k c) (natp (adt-klookup-c s j k c)))
  :hints (("Goal" :in-theory (enable adt-klookup-c))))

(in-theory (disable adt-row-okc adt-set-rec-c adt-row-okc-open adt-row-okc-zero
                    adt-set-rec-c-open adt-set-rec-c-end
                    adt-kcorr adt-kfind-c adt-kget-c adt-kinsert-c adt-kremove-c adt-kreplace-c
                    adt-kupdate-c adt-klookup-c adt-kempty-c adt-kwalk adt-kmem-c
                    adt-kinsert adt-kreplace adt-kremove-is-all-when-unique))

(deftheory adt-kinstance-unfold
  '(adt-row-okc-open adt-row-okc-zero adt-set-rec-c-open adt-set-rec-c-end
    adt-kfind-c adt-kget-c adt-kinsert-c adt-kremove-c adt-kreplace-c adt-kupdate-c adt-klookup-c adt-kmem-c
    adt-kidx adt-kput adt-bucket adt-kempty-c
    (:executable-counterpart adt-pschema) (:executable-counterpart adt-ncols)))
