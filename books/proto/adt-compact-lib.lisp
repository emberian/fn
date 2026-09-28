; fn prototype (lane proto-adt-2, 2026-09-27): COMPACTION.  NOT on a served
; path; no host calls it.
;
; A `set' of an :octets field leaves the old octets in the pool; a keyed
; remove leaves a dead slot.  Compaction rebuilds the image from its live
; records into a fresh one, in order.  Theorems:
;   adt-corr-compact / adt-kcorr-kcompact
;       compaction preserves the logical value;
;   adt-compact-is-canon / adt-kcompact-is-kcanon
;       the result is a function of the logical value ALONE, so two
;       histories that reach one value compact to one image, list-equal
;       (capacities included);
;   adt-fill-of-canon / adt-count-of-canon
;       after compaction the pool fill is the value's own octet total and
;       the count its length: the bound an operation needs for u64 offset
;       and count columns is a bound on the VALUE, which an export guard
;       can state (see the record, section 2, for the typed columns).

(in-package "ACL2")
(include-book "adt-key-lib")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth update-nth)))

; -----------------------------------------------------------------------------
; A. The sequence.

(defun adt-compact-c (s c)
  (declare (xargs :verify-guards nil))
  (adt-canon s (adt-abs s c)))

(defthm adt-compact-is-canon
  (implies (adt-corr s c a) (equal (adt-compact-c s c) (adt-canon s a))))

(defthm adt-schemap-when-corr
  (implies (adt-corr s c a) (adt-schemap s))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable adt-corr))))

(defthm adt-corr-compact
  (implies (adt-corr s c a) (adt-corr s (adt-compact-c s c) a))
  :hints (("Goal" :use ((:instance adt-corr-canon)))))

; The octet total of a value, and the fill of its canonical image.
(defun adt-row-octets (s r)
  (declare (xargs :verify-guards nil))
  (if (atom s) 0
    (+ (if (adt-octets-kind-p (car s)) (len (car r)) 0)
       (adt-row-octets (cdr s) (cdr r)))))

(defun adt-vbytes (s a)
  (declare (xargs :verify-guards nil))
  (if (atom a) 0 (+ (adt-row-octets s (car a)) (adt-vbytes s (cdr a)))))

(local
 (defthm adt-fill-of-put-field-exact
   (implies (and (natp ci) (natp p) (<= (+ ci (adt-kind-width kd)) p) (natp (nth (+ 2 p) c)))
            (equal (nth (+ 2 p) (adt-put-field kd ci p n v c))
                   (if (adt-octets-kind-p kd)
                       (+ (nth (+ 2 p) c) (len v))
                     (nth (+ 2 p) c))))
   :hints (("Goal" :in-theory (enable adt-put-field update-nth nth)))))

(local
 (defthm adt-fill-of-append-fields-exact
   (implies (and (natp ci) (natp p) (<= (+ ci (adt-ncols s)) p) (natp (nth (+ 2 p) c)))
            (equal (nth (+ 2 p) (adt-append-fields s ci p n rec c))
                   (+ (nth (+ 2 p) c) (adt-row-octets s rec))))
   :hints (("Goal" :in-theory (enable adt-append-fields)
            :induct (adt-append-fields s ci p n rec c)))))

(defthm adt-fill-of-append-c
  (implies (natp (nth (+ 2 (adt-ncols s)) c))
           (equal (nth (+ 2 (adt-ncols s)) (adt-append-c s rec c))
                  (+ (nth (+ 2 (adt-ncols s)) c) (adt-row-octets s rec))))
  :hints (("Goal" :in-theory (e/d (adt-append-c) (adt-fill-of-append-fields-exact))
           :use ((:instance adt-fill-of-append-fields-exact (ci 0) (p (adt-ncols s))
                            (n (nth (+ 1 (adt-ncols s)) c)))))))

(local
 (defun adt-build-induct2 (s a c)
   (declare (xargs :verify-guards nil))
   (if (atom a) (list c) (adt-build-induct2 s (cdr a) (adt-append-c s (car a) c)))))

(defthm adt-fill-of-build
  (implies (natp (nth (+ 2 (adt-ncols s)) c))
           (equal (nth (+ 2 (adt-ncols s)) (adt-build s a c))
                  (+ (nth (+ 2 (adt-ncols s)) c) (adt-vbytes s a))))
  :hints (("Goal" :induct (adt-build-induct2 s a c) :in-theory (enable adt-build))))

(local
 (defthm adt-nth-nils-suffix
   (implies (and (natp k) (natp n))
            (equal (nth (+ n k) (append (adt-nils n) tail)) (nth k tail)))
   :hints (("Goal" :in-theory (enable nth) :induct (adt-nils n)))))

(defthm adt-fill-of-empty-c
  (equal (nth (+ 2 (adt-ncols s)) (adt-empty-c s)) 0)
  :hints (("Goal" :in-theory (enable adt-empty-c)
           :use ((:instance adt-nth-nils-suffix (k 2) (n (adt-ncols s)) (tail (list nil 0 0)))))))

(defthm adt-fill-of-canon
  (equal (nth (+ 2 (adt-ncols s)) (adt-canon s a)) (adt-vbytes s a))
  :hints (("Goal" :in-theory (enable adt-canon))))

(defthm adt-count-of-canon
  (implies (and (adt-schemap s) (adt-seq-p s a))
           (equal (adt-count-c s (adt-canon s a)) (len a)))
  :hints (("Goal" :use ((:instance adt-corr-canon)) :in-theory (disable adt-corr-canon))))

; -----------------------------------------------------------------------------
; B. The keyed set: re-insert the live records, in slot order, into the
; empty keyed image.

(defun adt-kbuild (s j recs c)
  (declare (xargs :verify-guards nil))
  (if (atom recs) c (adt-kbuild s j (cdr recs) (adt-kinsert-c s j (car recs) c))))

(defun adt-kcanon (s dir j a)
  ; the canonical keyed image of the value A: its records in slot order
  (declare (xargs :verify-guards nil))
  (adt-kbuild s j (if (eq dir :stack) (adt-rev a) a) (adt-kempty-c s)))

(defun adt-kcompact-c (s dir j c)
  (declare (xargs :verify-guards nil))
  (adt-kcanon s dir j (adt-kview dir (adt-abs (adt-pschema s) c))))

(defthm adt-kcompact-is-kcanon
  (implies (adt-kcorr s dir j c a)
           (equal (adt-kcompact-c s dir j c) (adt-kcanon s dir j a)))
  :hints (("Goal" :in-theory (enable adt-kcorr))))

; Folding inserts from a corresponding image.
(defun adt-kfold (dir recs a)
  (declare (xargs :verify-guards nil))
  (if (atom recs) a (adt-kfold dir (cdr recs) (adt-kinsert dir (car recs) a))))

(local
 (defun adt-kbuild-induct (s dir j recs c a)
   (declare (xargs :verify-guards nil))
   (if (atom recs) (list c a)
     (adt-kbuild-induct s dir j (cdr recs) (adt-kinsert-c s j (car recs) c)
                        (adt-kinsert dir (car recs) a)))))

(local
 (defthm adt-member-append-c
   (iff (member-equal e (append x y)) (or (member-equal e x) (member-equal e y)))))

(defthm adt-kmem-kinsert
  (equal (adt-kmem j k (adt-kinsert dir r a))
         (or (equal (nth j r) k) (adt-kmem j k a)))
  :hints (("Goal" :in-theory (enable adt-kinsert adt-kmem))))

(defun adt-kfresh-any (j recs a)
  ; the same freshness, whatever the order the records join A in
  (declare (xargs :verify-guards nil))
  (if (atom recs) t
    (and (not (adt-kmem j (nth j (car recs)) a))
         (not (member-equal (nth j (car recs)) (adt-keys j (cdr recs))))
         (adt-kfresh-any j (cdr recs) a))))

(defthm adt-kfresh-any-insert
  (implies (and (adt-kfresh-any j xs a) (not (member-equal (nth j r) (adt-keys j xs))))
           (adt-kfresh-any j xs (adt-kinsert dir r a))))

(defthm adt-kfresh-any-step
  (implies (and (adt-kfresh-any j recs a) (consp recs))
           (adt-kfresh-any j (cdr recs) (adt-kinsert dir (car recs) a))))

(defthm adt-kcorr-kbuild
  (implies (and (adt-kcorr s dir j c a) (adt-seq-p s recs) (adt-kfresh-any j recs a))
           (adt-kcorr s dir j (adt-kbuild s j recs c) (adt-kfold dir recs a)))
  :hints (("Goal" :induct (adt-kbuild-induct s dir j recs c a))))

(defthm adt-kfresh-any-of-unique
  (implies (adt-kunique j recs) (adt-kfresh-any j recs nil))
  :hints (("Goal" :in-theory (enable adt-kunique adt-kmem))))

(defthm adt-kfold-append-order
  (implies (true-listp a)
           (equal (adt-kfold :append recs a) (append a (true-list-fix recs))))
  :hints (("Goal" :in-theory (enable adt-kinsert))))

(defthm adt-kfold-stack-order
  (equal (adt-kfold :stack recs a) (append (adt-rev recs) a))
  :hints (("Goal" :in-theory (enable adt-kinsert))))

(defthm adt-rev-rev
  (implies (true-listp x) (equal (adt-rev (adt-rev x)) x)))

(defthm adt-seq-p-rev
  (implies (adt-seq-p s a) (adt-seq-p s (adt-rev a))))

(defthm adt-kcorr-kcanon
  (implies (and (adt-schemap s) (natp j) (< j (len s)) (adt-seq-p s a) (adt-kunique j a)
                (or (eq dir :stack) (eq dir :append)))
           (adt-kcorr s dir j (adt-kcanon s dir j a) a))
  :hints (("Goal" :in-theory (disable adt-kcorr-kbuild)
           :use ((:instance adt-kcorr-kbuild (c (adt-kempty-c s)) (a nil)
                            (recs (if (eq dir :stack) (adt-rev a) a)))
                 (:instance adt-kcorr-empty)))))

(defthm adt-seq-p-live-recs
  (implies (adt-seq-p (adt-pschema s) p) (adt-seq-p s (adt-live-recs p))))

(defthm adt-kcorr-value-facts
  (implies (adt-kcorr s dir j c a)
           (and (adt-seq-p s a) (adt-kunique j a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable adt-kcorr))))

(defthm adt-kcorr-kcompact
  ; compaction preserves the logical value
  (implies (and (adt-kcorr s dir j c a) (adt-schemap s) (or (eq dir :stack) (eq dir :append)))
           (adt-kcorr s dir j (adt-kcompact-c s dir j c) a))
  :hints (("Goal" :in-theory (disable adt-kcompact-c adt-kcanon adt-kcorr-kcanon)
           :use ((:instance adt-kcorr-value-facts)
                 (:instance adt-kcorr-kcanon)))))

(defthm adt-kcompact-path-independent
  (implies (and (adt-kcorr s dir j c1 a) (adt-kcorr s dir j c2 a))
           (equal (adt-kcompact-c s dir j c1) (adt-kcompact-c s dir j c2)))
  :rule-classes nil)

(defthm adt-compact-path-independent
  (implies (and (adt-corr s c1 a) (adt-corr s c2 a))
           (equal (adt-compact-c s c1) (adt-compact-c s c2)))
  :rule-classes nil)
