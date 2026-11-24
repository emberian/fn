; Refinement of the streaming Merkle frontier to the recursive tree model.
; One link of the Merkle proof chain; events are exported so the consistency
; links see the same world.
(in-package "ACL2")
(include-book "merkle")
(include-book "owed-discharge")
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)


; The tag shifts each digest word by one byte. The first compression takes
; sixteen shifted words. The second takes the single remaining high byte.
(defthm mk-word-from-bytes
  (implies (unsigned-byte-p 32 w)
   (equal (fn-b3-le-word (mod w 256) (mod (floor w 256) 256)
                         (mod (floor w 65536) 256) (mod (floor w 16777216) 256))
          w))
  :hints (("Goal" :in-theory (enable mod fn-b3-le-word fn-b3-octet fn-b3-byte))))

(defthm mk-prefixed-word
  (implies (and (unsigned-byte-p 8 b) (unsigned-byte-p 32 w))
   (equal (fn-b3-le-word b (mod w 256) (mod (floor w 256) 256)
                         (mod (floor w 65536) 256))
          (fn-b3-word (+ (ash w 8) b))))
  :hints (("Goal" :in-theory (enable mod fn-b3-le-word fn-b3-octet fn-b3-byte fn-b3-word fn-b3-w32 ash))))

(defthm mk-last-byte
  (implies (unsigned-byte-p 32 w)
   (equal (mod (floor w 16777216) 256) (ash w -24)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm mk-word-id
 (implies (unsigned-byte-p 32 w) (equal (fn-b3-word w) w))
 :hints (("Goal" :in-theory (enable fn-b3-word))))
(defthm mk-high-byte-type
 (implies (unsigned-byte-p 32 w) (unsigned-byte-p 8 (ash w -24)))
 :hints (("Goal" :in-theory (enable ash))))
(in-theory (disable ash mod floor mk-last-byte unsigned-byte-p
                           fn-b3-words fn-b3-words-octets fn-b3-word-listp))
(defthm mk-read-written-words
 (implies (fn-b3-word-listp ws)
          (equal (fn-b3-words (len ws) (fn-b3-words-octets ws)) ws))
 :hints (("Goal" :induct (len ws)
          :in-theory (enable fn-b3-word-listp fn-b3-words fn-b3-words-octets))))
(defthm mk-read-eight-words
 (implies (and (fn-b3-word-listp ws) (equal (len ws) 8))
          (equal (fn-b3-words 8 (fn-b3-words-octets ws)) ws))
 :hints (("Goal" :use mk-read-written-words)))
(defthm mk-digest-round-trip
 (equal (fn-b3-words-octets (fn-b3-words 8 (fn-blake3 msg))) (fn-blake3 msg))
 :hints (("Goal" :in-theory (enable fn-blake3 fn-b3-hash fn-b3-output-root))))
(defun mk-shift (ws b)
 (if (atom ws) nil
   (cons (fn-b3-word (+ (ash (car ws) 8) b))
         (mk-shift (cdr ws) (ash (car ws) -24)))))
(defthm mk-read-shift
 (implies (and (fn-b3-word-listp ws) (unsigned-byte-p 8 b))
  (equal (fn-b3-words (len ws) (cons b (fn-b3-words-octets ws)))
         (mk-shift ws b)))
 :hints (("Goal" :induct (mk-shift ws b)
          :in-theory (enable fn-b3-word-listp fn-b3-words fn-b3-words-octets mk-last-byte))))
(defun mk-last-high (ws b)
 (if (atom ws) b (mk-last-high (cdr ws) (ash (car ws) -24))))
(defthm mk-drop-four
 (implies (natp n)
  (equal (fn-b3-nthcdrx (+ 4 n) (list* a b c d tail)) (fn-b3-nthcdrx n tail)))
 :hints (("Goal" :expand ((:free (x) (fn-b3-nthcdrx (+ 1 n) x)) (:free (x) (fn-b3-nthcdrx (+ 2 n) x)) (:free (x) (fn-b3-nthcdrx (+ 3 n) x)) (:free (x) (fn-b3-nthcdrx (+ 4 n) x))))))
(defthm mk-drop-zero (equal (fn-b3-nthcdrx 0 xs) xs))
(defthm mk-shift-tail
 (implies (and (fn-b3-word-listp ws) (unsigned-byte-p 8 b))
  (equal (fn-b3-nthcdrx (* 4 (len ws)) (cons b (fn-b3-words-octets ws)))
         (list (mk-last-high ws b))))
 :hints (("Goal" :induct (mk-last-high ws b)
           :in-theory (e/d (fn-b3-word-listp fn-b3-words-octets mk-last-byte)
                           (fn-b3-nthcdrx)))))

(defthm mk-node-message
 (implies (and (fn-b3-word-listp ws) (equal (len ws) 16))
  (equal (fn-b3-words 8 (fn-blake3 (cons 1 (fn-b3-words-octets ws))))
         (fn-b3-compress
          (fn-b3-cv8 (fn-b3-compress *fn-b3-iv* (mk-shift ws 1) 0 64 1))
          (fn-b3-words 16 (list (mk-last-high ws 1))) 0 1 10)))
 :hints (("Goal" :use ((:instance mk-read-shift (b 1)) (:instance mk-shift-tail (b 1)))
          :in-theory (e/d (fn-blake3 fn-b3-hash fn-b3-output-root fn-b3-octet-listp)
           (fn-b3-nthcdrx mk-shift mk-read-shift mk-shift-tail mk-last-high fn-b3-cv8
            fn-b3-fix-octets))
          :expand ((:free (cv) (fn-b3-chunk cv (cons 1 (fn-b3-words-octets ws)) 0 0 t)))
          )))

; A canonical parent is the digest of the tagged pair. MK-PARENT also models
; the arithmetic on unrestricted ACL2 values, including unguarded loads.
(defun mk-join (l r)
 (fn-b3-words 8 (fn-blake3 (cons 1 (fn-b3-words-octets (append l r))))))
(defun mk-words8p (xs)
 (and (equal (len xs) 8) (fn-b3-word-listp xs)))
(defthm mk-join-words8p (mk-words8p (mk-join l r)))
(defthm mk-leaf-words8p (mk-words8p (fn-b3-words 8 bytes)))
(defthm mk-word-listp-append
 (implies (and (fn-b3-word-listp l) (fn-b3-word-listp r))
          (fn-b3-word-listp (append l r)))
 :hints (("Goal" :in-theory (enable fn-b3-word-listp))))
(defthm mk-len-append (equal (len (append l r)) (+ (len l) (len r))))
(defthm mk-last-high-type
 (implies (and (fn-b3-word-listp ws) (unsigned-byte-p 8 b))
          (unsigned-byte-p 8 (mk-last-high ws b)))
 :hints (("Goal" :in-theory (enable fn-b3-word-listp))))
(defthm mk-final-word
 (implies (unsigned-byte-p 8 b)
  (equal (fn-b3-words 16 (list b)) (cons b (make-list 15 :initial-element 0))))
 :hints (("Goal" :in-theory (enable fn-b3-words fn-b3-le-word fn-b3-octet fn-b3-byte unsigned-byte-p))))
(defthm mk-join-implementation
 (implies (and (mk-words8p l) (mk-words8p r))
  (equal (mk-join l r)
         (let ((ws (append l r)))
          (fn-b3-compress
           (fn-b3-cv8 (fn-b3-compress *fn-b3-iv* (mk-shift ws 1) 0 64 1))
           (cons (mk-last-high ws 1) (make-list 15 :initial-element 0)) 0 1 10))))
 :hints (("Goal" :in-theory (disable fn-blake3-of-octets mk-shift mk-last-high fn-b3-cv8 binary-append))))
(defun mk-parent (l r)
 (let ((ws (append l r)))
  (fn-b3-compress
   (fn-b3-cv8 (fn-b3-compress *fn-b3-iv* (mk-shift ws 1) 0 64 1))
   (cons (mk-last-high ws 1) (make-list 15 :initial-element 0)) 0 1 10)))
(defthm mk-parent-canonical
 (implies (and (mk-words8p l) (mk-words8p r))
          (equal (mk-parent l r) (mk-join l r)))
 :hints (("Goal" :in-theory (disable mk-join mk-shift mk-last-high fn-b3-cv8 binary-append))))
(in-theory (disable mk-join-implementation mk-parent-canonical mk-words8p))
(defthm mk-node-row
 (equal (fn2-digest-list dst (fn2-mk-node dst left right d))
                 (mk-parent (fn2-digest-list left d) (fn2-digest-list right d)))
 :hints (("Goal" :in-theory
          (e/d (fn2-mk-node fn2-mk-node-first fn-b3-compress
                fn2-digests-w0 fn2-digests-w1 fn2-digests-w2 fn2-digests-w3
                fn2-digests-w4 fn2-digests-w5 fn2-digests-w6 fn2-digests-w7
                fn-b3-word-listp)
               (mk-join fn2-digest-store-words-effect nfix nth)))))
(in-theory (disable mk-parent mk-join))
(defthm mk-node-other
 (implies (not (equal (nfix i) (nfix dst)))
  (equal (fn2-digest-list i (fn2-mk-node dst l r d)) (fn2-digest-list i d)))
 :hints (("Goal" :in-theory (disable nth nfix))))
(defthm mk-copy-row
 (equal (fn2-digest-list i (fn2-digest-copy dst src d))
        (if (equal (nfix i) (nfix dst)) (fn2-digest-list src d) (fn2-digest-list i d)))
 :hints (("Goal" :in-theory (e/d (fn2-digest-copy nth-update-nth) (nth nfix update-nth)))))
(defthm mk-eight-of-words
 (implies (mk-words8p words)
  (equal (list (nth 0 words) (nth 1 words) (nth 2 words) (nth 3 words) (nth 4 words) (nth 5 words) (nth 6 words) (nth 7 words)) words))
 :hints (("Goal" :in-theory (enable mk-words8p fn-b3-word-listp)
                 :expand ((len words) (fn-b3-word-listp words) (len (cdr words)) (fn-b3-word-listp (cdr words)) (len (cdr (cdr words))) (fn-b3-word-listp (cdr (cdr words))) (len (cdr (cdr (cdr words)))) (fn-b3-word-listp (cdr (cdr (cdr words)))) (len (cdr (cdr (cdr (cdr words))))) (fn-b3-word-listp (cdr (cdr (cdr (cdr words))))) (len (cdr (cdr (cdr (cdr (cdr words)))))) (fn-b3-word-listp (cdr (cdr (cdr (cdr (cdr words)))))) (len (cdr (cdr (cdr (cdr (cdr (cdr words))))))) (fn-b3-word-listp (cdr (cdr (cdr (cdr (cdr (cdr words))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr words)))))))) (fn-b3-word-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr words)))))))) (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr words))))))))) (fn-b3-word-listp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr words)))))))))))))
(defthm mk-load-row
 (implies (or (not (equal (nfix i) (nfix dst))) (mk-words8p words))
  (equal (fn2-digest-list i (fn2-digest-load dst words d))
         (if (equal (nfix i) (nfix dst)) words (fn2-digest-list i d))))
 :hints (("Goal" :in-theory (e/d (nth-update-nth) (nth nfix update-nth)))))

(defthm mk-empty-row
 (equal (fn2-digest-list i (fn2-digest-empty dst d))
        (if (equal (nfix i) (nfix dst)) *fn2-b3-empty-root* (fn2-digest-list i d)))
 :hints (("Goal" :in-theory (e/d (fn2-digest-empty nth-update-nth) (nth nfix update-nth)))))
(in-theory (disable fn2-digest-list fn2-digest-load fn2-mk-size))

; Project the sixty frontier rows. Carry changes the first available level
; and leaves every lower row in place, even when that row becomes inactive.
(defun-nx mk-front (level d)
 (declare (xargs :measure (nfix (- 60 (nfix level)))))
 (if (or (not (natp level)) (<= 60 level)) nil
  (cons (fn2-digest-list (+ 58 level) d) (mk-front (+ 1 level) d))))
(defthm mk-front-len
 (implies (and (natp level) (<= level 60)) (equal (len (mk-front level d)) (- 60 level))))
(defthm mk-front-consp
 (equal (consp (mk-front level d)) (and (natp level) (< level 60))))
(defthm mk-front-copy
 (implies (and (natp dst) (natp level) (or (< dst (+ 58 level)) (<= 118 dst)))
          (equal (mk-front level (fn2-digest-copy dst src d)) (mk-front level d)))
 :hints (("Goal" :induct (mk-front level d))))
(defthm mk-front-node
 (implies (and (natp dst) (natp level) (or (< dst (+ 58 level)) (<= 118 dst)))
          (equal (mk-front level (fn2-mk-node dst l r d)) (mk-front level d)))
 :hints (("Goal" :induct (mk-front level d))))
(defthm mk-front-load
 (implies (and (natp dst) (natp level) (or (< dst (+ 58 level)) (<= 118 dst)))
          (equal (mk-front level (fn2-digest-load dst words d)) (mk-front level d)))
 :hints (("Goal" :induct (mk-front level d))))
(defthm mk-front-empty
 (implies (and (natp dst) (natp level) (or (< dst (+ 58 level)) (<= 118 dst)))
          (equal (mk-front level (fn2-digest-empty dst d)) (mk-front level d)))
 :hints (("Goal" :induct (mk-front level d))))
(defun mk-insert (n x fs)
 (if (atom fs) nil
  (if (and (consp (cdr fs)) (oddp (nfix n)))
      (cons (car fs) (mk-insert (floor n 2) (mk-parent (car fs) x) (cdr fs)))
    (cons x (cdr fs)))))
(defthm mk-carry-preserves-lower
 (implies (and (natp level) (< level 60) (natp i) (< i (+ 58 level)))
  (equal (fn2-digest-list i (fn2-mk-carry 0 level n 118 d m)) (fn2-digest-list i d)))
 :hints (("Goal" :induct (fn2-mk-carry 0 level n 118 d m)
          :in-theory (enable fn2-mk-carry))))
(defthm mk-carry-to-insert
 (implies (and (natp level) (< level 60))
  (equal (mk-front level (fn2-mk-carry 0 level n 118 d m))
         (mk-insert n (fn2-digest-list 118 d) (mk-front level d))))
 :hints (("Goal" :induct (fn2-mk-carry 0 level n 118 d m)
                 :in-theory (enable fn2-mk-carry)
                 :expand ((:free (d) (mk-front level d))))))

; At each level, prepend the occupied frontier row to the remaining input,
; combine adjacent pairs, and promote an unmatched rightmost digest.
(defun mk-pairs (xs)
 (if (and (consp xs) (consp (cdr xs)))
     (cons (mk-parent (car xs) (cadr xs)) (mk-pairs (cddr xs)))
   xs))
(defun mk-lift (n fs xs)
 (if (atom fs) (if (consp xs) (car xs) *fn2-b3-empty-root*)
  (mk-lift (floor n 2) (cdr fs)
           (mk-pairs (if (oddp n) (cons (car fs) xs) xs)))))
(defthm mk-lift-finished
 (implies (atom (cdr xs))
          (equal (mk-lift 0 fs xs) (if (consp xs) (car xs) *fn2-b3-empty-root*))))
(defthm mk-fold-to-lift
 (implies (and (natp n) (natp level) (<= level 60)
               (or seen (equal (fn2-digest-list 136 d) *fn2-b3-empty-root*)))
  (equal (fn2-digest-list 136 (fn2-mk-fold 136 0 level n seen d m))
         (mk-lift n (mk-front level d) (if seen (list (fn2-digest-list 136 d)) nil))))
 :hints (("Goal" :induct (fn2-mk-fold 136 0 level n seen d m)
          :in-theory (enable fn2-mk-fold)
          :expand ((mk-front level d)))))

(defthm mk-odd-succ
 (implies (integerp n) (equal (oddp (+ 1 n)) (not (oddp n)))))
(defthm mk-half-succ
 (implies (integerp n)
  (equal (floor (+ 1 n) 2) (if (oddp n) (+ 1 (floor n 2)) (floor n 2))))
 :hints (("Goal" :use ((:instance floor-bounds-1 (x n) (y 2)) (:instance floor-bounds-1 (x (+ 1 n)) (y 2))))))
(in-theory (disable evenp oddp))
(defun mk-insert-induct (n x fs xs)
 (if (and (consp fs) (consp (cdr fs)) (oddp (nfix n)))
     (mk-insert-induct (floor n 2) (mk-parent (car fs) x) (cdr fs) (mk-pairs xs))
   (list n x fs xs)))
(defthm mk-double-expt
 (implies (natp k) (equal (expt 2 (+ 1 k)) (* 2 (expt 2 k))))
 :hints (("Goal" :expand (expt 2 (+ 1 k)))))
(defthm mk-half-room
 (implies (and (natp n) (oddp n) (integerp cap) (< (+ 1 n) (* 2 cap)))
          (< (+ 1 (floor n 2)) cap))
 :hints (("Goal" :use ((:instance floor-bounds-1 (x n) (y 2)))
                 :in-theory (enable oddp evenp))))
(defthm mk-lift-insert
 (implies (and (natp n) (< (+ 1 n) (expt 2 (len fs))))
  (equal (mk-lift (+ 1 n) (mk-insert n x fs) xs)
         (mk-lift n fs (cons x xs))))
 :hints (("Goal" :induct (mk-insert-induct n x fs xs)
                 :do-not-induct t
                 :in-theory (disable mk-double-expt mk-half-room)
                 :expand ((mk-lift n fs (cons x xs)) (mk-insert n x fs))) ("Subgoal *1/1" :use ((:instance mk-half-room (cap (expt 2 (len (cdr fs))))) (:instance mk-double-expt (k (len (cdr fs))))))))
(in-theory (disable mk-front mk-lift mk-insert mk-double-expt mk-half-room))
(defthm mk-size-after-set
 (equal (fn2-mk-size 0 (fn2-mk-set-size 0 n m)) n)
 :hints (("Goal" :in-theory (enable fn2-mk-size nth-update-nth))))
(defun mk-word-rows (xs)
 (if (consp xs) (and (mk-words8p (car xs)) (mk-word-rows (cdr xs))) t))
(defthm mk-run-to-lift
 (implies (and (true-listp xs) (mk-word-rows xs)
               (natp (fn2-mk-size 0 m))
               (< (+ (len xs) (fn2-mk-size 0 m)) (expt 2 60)))
  (equal (car (fn2-mk-run-hashes xs d m))
         (mk-lift (fn2-mk-size 0 m) (mk-front 0 d) xs)))
 :hints (("Goal" :induct (fn2-mk-run-hashes xs d m) :expand ((len xs) (true-listp xs) (mk-word-rows xs) (fn2-mk-run-hashes xs d m))
                 :in-theory (e/d (fn2-mk-append fn2-mk-root)
                   (fn2-mk-set-size mk-lift-finished fn2-mk-append-shape))
                 :do-not-induct t)))

; Pairing a layer preserves its recursive tree. For more than two leaves,
; the RFC split is twice the split of the paired layer.
(include-book "std/lists/take" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(defthm mk-split-bounds
 (implies (and (natp n) (< 1 n))
          (and (posp (fn2-mk-split n)) (< (fn2-mk-split n) n)))
 :rule-classes (:rewrite (:linear :corollary (implies (and (natp n) (< 1 n)) (< (fn2-mk-split n) n))))
 :hints (("Goal" :induct (fn2-mk-split n))))
(defun mk-tree (xs)
 (declare (xargs :measure (len xs)))
 (cond ((atom xs) *fn2-b3-empty-root*)
       ((atom (cdr xs)) (car xs))
       (t (let ((k (fn2-mk-split (len xs))))
            (mk-parent (mk-tree (take k xs)) (mk-tree (nthcdr k xs)))))))
(defthm mk-pair-len
 (equal (len (mk-pairs xs)) (ceiling (len xs) 2))
 :hints (("Goal" :induct (mk-pairs xs))))
(defun mk-pair-induct (k xs)
 (if (or (zp k) (atom xs) (atom (cdr xs))) (list k xs)
  (mk-pair-induct (1- k) (cddr xs))))
(defthm mk-pairs-drop
 (implies (and (natp k) (true-listp xs))
   (equal (nthcdr k (mk-pairs xs)) (mk-pairs (nthcdr (* 2 k) xs))))
 :hints (("Goal" :induct (mk-pair-induct k xs) :expand ((mk-pairs xs) (:free (xs) (nthcdr (* 2 k) xs)) (:free (xs) (nthcdr (+ -1 (* 2 k)) xs))) :in-theory (disable nthcdr-of-cdr))))
(defthm mk-pairs-take
 (implies (and (natp k) (<= (* 2 k) (len xs)))
  (equal (take k (mk-pairs xs)) (mk-pairs (take (* 2 k) xs))))
 :hints (("Goal" :induct (mk-pair-induct k xs)
          :expand ((mk-pairs xs) (:free (xs) (take (* 2 k) xs))
                   (:free (xs) (take (+ -1 (* 2 k)) xs))))))
(defthm mk-pairs-proper (implies (true-listp xs) (true-listp (mk-pairs xs))) :hints (("Goal" :induct (mk-pairs xs))))
(defthm mk-consp-pairs (equal (consp (mk-pairs xs)) (consp xs)))
(defthm mk-cdr-pairs
 (equal (consp (cdr (mk-pairs xs))) (< 2 (len xs)))
 :hints (("Goal" :expand ((len xs) (len (cdr xs)) (len (cddr xs)) (mk-pairs xs)))))
(defthm mk-split-pos (posp (fn2-mk-split n)) :rule-classes :type-prescription)
(defthm mk-split-even
 (implies (and (natp n) (< 2 n))
  (equal (* 2 (fn2-mk-split (ceiling n 2))) (fn2-mk-split n)))
 :hints (("Goal" :expand (fn2-mk-split n))))
(defthm mk-room-for-half
 (implies (and (natp n) (< 2 n))
          (<= (* 2 (fn2-mk-split (ceiling n 2))) n)))
(defthm mk-tree-atom-tail
 (implies (atom (cdr xs)) (equal (mk-tree xs) (if (consp xs) (car xs) *fn2-b3-empty-root*))))
(defthm mk-first-pair
 (equal (car (mk-pairs xs))
        (if (and (consp xs) (consp (cdr xs))) (mk-parent (car xs) (cadr xs)) (car xs))))
(defthm mk-tree-of-pairs
 (implies (true-listp xs) (equal (mk-tree (mk-pairs xs)) (mk-tree xs)))
 :hints (("Goal" :induct (mk-tree xs) :do-not-induct t
          :in-theory (disable (:definition mk-tree) mk-pairs fn2-mk-split ceiling ceiling-to-floor)
          :expand ((mk-tree xs) (mk-tree (mk-pairs xs))))
         ("Subgoal *1/3" :cases ((consp (cddr xs))))))
(defun mk-lift-induct (fs xs)
 (if (atom fs) xs (mk-lift-induct (cdr fs) (mk-pairs xs))))
(defthm mk-half-integer-cap
 (implies (and (natp n) (integerp cap) (<= n (* 2 cap))) (<= (ceiling n 2) cap))
 :hints (("Goal" :use ((:instance floor-bounds-1 (x n) (y 2))))))
(defthm mk-halving-fits
 (implies (and (natp n) (natp k) (<= n (expt 2 (+ 1 k))))
          (<= (ceiling n 2) (expt 2 k)))
 :hints (("Goal" :use (mk-double-expt (:instance mk-half-integer-cap (cap (expt 2 k))))
                 :in-theory (union-theories (theory 'minimal-theory)
                                  '(natp (:type-prescription expt-type-prescription-integerp-base))))))
(defthm mk-lift-to-tree
 (implies (and (true-listp xs) (<= (len xs) (expt 2 (len fs))))
  (equal (mk-lift 0 fs xs) (mk-tree xs)))
 :hints (("Goal" :induct (mk-lift-induct fs xs) :do-not-induct t
          :in-theory (disable mk-tree mk-pairs ceiling ceiling-to-floor)
          :expand (mk-lift 0 fs xs))
         ("Subgoal *1/1" :cases ((consp (cdr xs))) :expand ((len xs) (len (cdr xs)) (mk-lift 0 fs xs)))
         ("Subgoal *1/2" :use ((:instance mk-halving-fits (n (len xs)) (k (len (cdr fs))))))))

; Relate the pure tree over word rows to the byte-valued, fuelled MTH.
(defthm mk-len-leaves (equal (len (fn2-mk-leaves xs)) (len xs)))
(defthm mk-leaves-word-rows (mk-word-rows (fn2-mk-leaves xs)))
(defthm mk-take-leaves
 (implies (and (natp k) (<= k (len xs)))
  (equal (take k (fn2-mk-leaves xs)) (fn2-mk-leaves (take k xs))))
 :hints (("Goal" :induct (take k xs))))
(defthm mk-drop-leaves
 (equal (nthcdr k (fn2-mk-leaves xs)) (fn2-mk-leaves (nthcdr k xs)))
 :hints (("Goal" :induct (nthcdr k xs)
         :in-theory (union-theories (theory 'minimal-theory)
           '(nthcdr zp fn2-mk-leaves car-cons cdr-cons nthcdr-when-zp
             nthcdr-when-atom (:executable-counterpart fn2-mk-leaves)))
         :expand ((:free (ys) (nthcdr k ys)) (fn2-mk-leaves xs)))))
(defthm mk-serialize-append
 (equal (fn-b3-words-octets (append l r))
        (append (fn-b3-words-octets l) (fn-b3-words-octets r)))
 :hints (("Goal" :in-theory (enable fn-b3-words-octets))))
(defthm mk-model-round-trip
 (equal (fn-b3-words-octets (fn-b3-words 8 (car (fn2-mk-model xs fuel))))
        (car (fn2-mk-model xs fuel)))
 :hints (("Goal" :expand ((fn2-mk-model xs fuel))
                 :in-theory (disable fn-blake3-of-octets))))
(defthm mk-consp-leaves (equal (consp (fn2-mk-leaves xs)) (consp xs)))
(defthm mk-head-leaves
 (implies (consp xs)
  (equal (car (fn2-mk-leaves xs)) (fn-b3-words 8 (fn-blake3 (cons 0 (car xs)))))))
(defthm mk-tail-leaves
 (equal (cdr (fn2-mk-leaves xs)) (fn2-mk-leaves (cdr xs))))
(defthm mk-min-one (implies (consp xs) (<= 1 (len xs))) :rule-classes :linear)
(defthm mk-min-two
 (implies (consp (cdr xs)) (<= 2 (len xs))) :rule-classes :linear)
(defthm mk-tree-is-model
 (implies (and (natp fuel) (<= (len xs) fuel))
  (equal (mk-tree (fn2-mk-leaves xs)) (fn-b3-words 8 (car (fn2-mk-model xs fuel)))))
 :hints (("Goal" :induct (fn2-mk-model xs fuel) :do-not-induct t
          :expand ((mk-tree (fn2-mk-leaves xs)) (fn2-mk-model xs fuel))
          :in-theory (e/d (mk-parent-canonical mk-join)
             (fn-blake3-of-octets mk-tree fn2-mk-split fn2-mk-leaves (:definition fn2-mk-model) len)))))

(defthm mk-initial-size
 (equal (fn2-mk-size 0 (fn2-mk-table-init 1 (create-fn2-mk))) 0)
 :hints (("Goal" :in-theory (enable fn2-mk-table-init fn2-mk-size create-fn2-mk))))
(defthm mk-leaves-proper (true-listp (fn2-mk-leaves xs)))
(defthm fn2-mk-root-is-mth-proved
 (fn2-mk-root-is-mth$owed records hashes)
 :rule-classes nil
 :hints (("Goal" :use ((:instance mk-tree-is-model (xs records) (fuel (len records))))
          :in-theory (e/d (fn2-mk-root-is-mth$owed)
                          (mk-tree-is-model mk-front fn2-mk-run-hashes fn2-mk-leaves
                           fn2-mk-model mk-tree mk-words8p fn2-mk-size)))))

(fn2-owed-discharge fn2-mk-root-is-mth fn2-mk-root-is-mth-proved)
(defthm mk-evidence-equal
 (implies (fn2-a-integrity-evidence x y) (equal x y))
 :rule-classes :forward-chaining
 :hints (("Goal" :use ((:instance fn2-a-integrity-evidence-sound
                                  (expected x) (observed y))))))

(defthm mk-against-member
 (implies (and (fn2-mk-integrity-against x ys) (member-equal y ys)
               (equal (fn-blake3 x) (fn-blake3 y)))
          (equal x y))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-mk-integrity-against x ys)
          :in-theory (disable fn-blake3-of-octets))))
(defthm mk-opening-injective
 (implies (and (fn2-mk-integrity-openings all)
               (member-equal x all) (member-equal y all)
               (equal (fn-blake3 x) (fn-blake3 y)))
          (equal x y))
 :rule-classes nil
 :hints (("Goal" :induct (len all) :in-theory (disable fn2-mk-integrity-against))
         ("Subgoal *1/1" :use ((:instance mk-against-member (x (car all)) (ys (cdr all)))
                               (:instance mk-against-member (x (car all)) (y x) (ys (cdr all)))))))
(defun-nx mk-opening (xs fuel)
 (cond ((or (zp fuel) (atom xs)) nil)
       ((atom (cdr xs)) (cons 0 (car xs)))
       (t (let* ((k (fn2-mk-split (len xs)))
                 (l (car (fn2-mk-model (take k xs) (1- fuel))))
                 (r (car (fn2-mk-model (nthcdr k xs) (1- fuel)))))
            (cons 1 (append l r))))))
(defthm mk-model-hash
 (equal (car (fn2-mk-model xs fuel)) (fn-blake3 (mk-opening xs fuel)))
 :hints (("Goal" :expand (fn2-mk-model xs fuel) :in-theory (disable fn-blake3-of-octets))))
(in-theory (disable mk-model-hash))
(defthm mk-model-openings-first
 (equal (car (cadr (fn2-mk-model xs fuel))) (mk-opening xs fuel))
 :hints (("Goal" :expand (fn2-mk-model xs fuel) :in-theory (disable mk-model-hash))))
(defthm mk-model-openings-consp
 (consp (cadr (fn2-mk-model xs fuel)))
 :hints (("Goal" :expand (fn2-mk-model xs fuel))))
(include-book "std/lists/sets" :dir :system)
(defthm mk-opening-member
 (implies (subsetp-equal (cadr (fn2-mk-model xs fuel)) all)
          (member-equal (mk-opening xs fuel) all))
 :hints (("Goal" :expand (subsetp-equal (cadr (fn2-mk-model xs fuel)) all)
          :in-theory (disable mk-opening fn2-mk-model))))
(defthm mk-model-binding
 (implies (and (fn2-mk-integrity-openings all)
               (subsetp-equal (cadr (fn2-mk-model xs fuel)) all)
               (subsetp-equal (cadr (fn2-mk-model ys fuel)) all)
               (equal (car (fn2-mk-model xs fuel)) (car (fn2-mk-model ys fuel))))
          (equal (mk-opening xs fuel) (mk-opening ys fuel)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mk-opening-injective
                         (x (mk-opening xs fuel)) (y (mk-opening ys fuel))))
          :in-theory (e/d (mk-model-hash) (mk-opening fn2-mk-model fn2-mk-integrity-openings)))))
(defthm mk-model-digest-shape
 (and (equal (len (car (fn2-mk-model xs fuel))) 32)
      (true-listp (car (fn2-mk-model xs fuel))))
 :hints (("Goal" :in-theory (e/d (mk-model-hash) (mk-opening fn2-mk-model fn-blake3-of-octets)))))
(defun mk-cdr-both (x u)
 (if (consp x) (mk-cdr-both (cdr x) (cdr u)) u))
(defthm mk-split-digest-pair
 (implies (and (true-listp x) (true-listp u) (equal (len x) (len u)))
          (equal (equal (append x y) (append u v))
                 (and (equal x u) (equal y v))))
 :hints (("Goal" :induct (mk-cdr-both x u)
 :in-theory (union-theories (theory 'minimal-theory)
  '(mk-cdr-both len true-listp binary-append car-cons cdr-cons cons-equal
    cons-car-cdr default-car default-cdr (:type-prescription len)))
 :expand ((len u) (true-listp u) (append u v)))))
(defthm mk-child-openings
 (implies (and (posp fuel) (consp xs) (consp (cdr xs))
               (subsetp-equal (cadr (fn2-mk-model xs fuel)) all))
          (let ((k (fn2-mk-split (len xs))))
           (and (subsetp-equal (cadr (fn2-mk-model (take k xs) (1- fuel))) all)
                (subsetp-equal (cadr (fn2-mk-model (nthcdr k xs) (1- fuel))) all))))
 :rule-classes nil
 :hints (("Goal" :expand ((fn2-mk-model xs fuel)
                          (:free (a d) (subsetp-equal (cons a d) all)))
                  :in-theory (disable mk-opening fn2-mk-split))))
(defun mk-compare-trees (kfuel xs ys)
 (declare (xargs :measure (nfix kfuel)))
 (if (or (zp kfuel) (atom xs) (atom (cdr xs))) (list xs ys)
  (let ((k (fn2-mk-split (len xs))))
   (list (mk-compare-trees (1- kfuel) (take k xs) (take k ys))
         (mk-compare-trees (1- kfuel) (nthcdr k xs) (nthcdr k ys))))))
(defun-nx mk-matchp (xs ys fuel all)
 (and (natp fuel) (<= (len xs) fuel) (equal (len xs) (len ys))
      (true-listp xs) (true-listp ys) (fn2-mk-integrity-openings all)
      (subsetp-equal (cadr (fn2-mk-model xs fuel)) all)
      (subsetp-equal (cadr (fn2-mk-model ys fuel)) all)
      (equal (car (fn2-mk-model xs fuel)) (car (fn2-mk-model ys fuel)))))
(in-theory (disable fn2-mk-integrity-openings fn2-mk-model fn2-mk-split
                    take nthcdr true-listp len fn-blake3-of-octets mk-opening mk-matchp
                    mk-split-digest-pair))
(defthm mk-match-opening
 (implies (mk-matchp xs ys fuel all) (equal (mk-opening xs fuel) (mk-opening ys fuel)))
 :hints (("Goal" :use mk-model-binding :in-theory (enable mk-matchp)))
 :rule-classes nil)
(defthm mk-two-or-more
 (equal (consp (cdr xs)) (< 1 (len xs)))
 :hints (("Goal" :expand ((len xs) (len (cdr xs))))))
(defthm mk-split-rejoin
 (implies (and (natp k) (<= k (len xs)) (<= k (len ys))
               (equal (take k xs) (take k ys)) (equal (nthcdr k xs) (nthcdr k ys)))
          (equal xs ys))
 :hints (("Goal" :use ((:instance append-of-take-and-nthcdr (x xs) (n k))
                       (:instance append-of-take-and-nthcdr (x ys) (n k)))
           :in-theory (disable append-of-take-and-nthcdr mk-split-digest-pair)))
 :rule-classes nil)
(defthm mk-match-children
 (implies (and (mk-matchp xs ys fuel all) (posp fuel) (consp (cdr xs)))
          (let ((k (fn2-mk-split (len xs))))
           (and (mk-matchp (take k xs) (take k ys) (1- fuel) all)
                (mk-matchp (nthcdr k xs) (nthcdr k ys) (1- fuel) all))))
 :hints (("Goal" :use (mk-match-opening mk-child-openings (:instance mk-child-openings (xs ys)))
          :in-theory (enable mk-matchp mk-opening mk-split-digest-pair)))
 :rule-classes nil)
(defthm mk-short-trees
 (implies (and (natp fuel) (<= (len xs) fuel) (equal (len xs) (len ys))
               (true-listp xs) (true-listp ys)
               (or (zp fuel) (atom xs) (atom (cdr xs)))
               (equal (mk-opening xs fuel) (mk-opening ys fuel)))
          (equal xs ys))
 :rule-classes nil
 :hints (("Goal" :cases ((consp xs) (consp ys) (consp (cdr ys)))
          :in-theory (union-theories (theory 'minimal-theory)
           '(natp zp true-listp len mk-opening cons-equal cons-car-cdr
             default-car default-cdr (:type-prescription len)))
          :expand ((len xs) (len ys) (len (cdr ys)) (true-listp xs) (true-listp ys)))))
(defthm mk-match-base
 (implies (and (mk-matchp xs ys fuel all) (or (zp fuel) (atom xs) (atom (cdr xs))))
          (equal xs ys))
 :hints (("Goal" :use (mk-match-opening mk-short-trees)
          :in-theory (union-theories (theory 'minimal-theory) '(mk-matchp))))
 :rule-classes nil)
(defthm mk-match-rejoin
 (implies (and (mk-matchp xs ys fuel all) (posp fuel) (consp (cdr xs))
               (let ((k (fn2-mk-split (len xs))))
                (and (equal (take k xs) (take k ys))
                     (equal (nthcdr k xs) (nthcdr k ys)))))
          (equal xs ys))
 :rule-classes nil
 :hints (("Goal" :use ((:instance mk-split-rejoin (k (fn2-mk-split (len xs)))))
          :in-theory (enable mk-matchp))))
(defthm mk-tree-binding
 (implies (mk-matchp xs ys fuel all) (equal xs ys))
 :rule-classes nil
 :hints (("Goal" :induct (mk-compare-trees fuel xs ys)
          :in-theory (union-theories (theory 'minimal-theory) '(mk-compare-trees posp zp)))
         ("Subgoal *1/2" :use (mk-match-children mk-match-rejoin))
         ("Subgoal *1/1" :use mk-match-base)))
(defthm mk-digest-comparison
 (equal (fn2-digest-equal i j d) (equal (fn2-digest-list i d) (fn2-digest-list j d)))
 :hints (("Goal" :in-theory (enable fn2-digest-equal fn2-digest-list))))
(defthm mk-proof-load-below
 (implies (and (natp i) (natp at) (< i at))
  (equal (fn2-digest-list i (fn2-mk-load-proof proof at d)) (fn2-digest-list i d)))
 :hints (("Goal" :induct (fn2-mk-load-proof proof at d))))
(defthm mk-initial-phase
 (equal (fn2-mk-phase 0 (fn2-mk-table-init 1 (create-fn2-mk))) 0)
 :hints (("Goal" :in-theory (enable fn2-mk-table-init fn2-mk-phase create-fn2-mk))))
(defthm mk-same-size-run
 (implies (and (posp n) (equal (fn2-mk-phase 0 m) 0))
  (equal (car (fn2-mk-consistency-run 64 n n count d m))
         (cond ((not (equal count 0)) :proof-length)
               ((equal (fn2-digest-list 136 d) (fn2-digest-list 137 d)) :ok)
               (t :root-mismatch))))
 :hints (("Goal" :expand (fn2-mk-consistency-run 64 n n count d m)
          :in-theory (e/d (fn2-mk-verify-consistency)
                          (fn2-mk-phase fn2-mk-proof-openings)))))
(defthm mk-same-size-observation
 (implies (and (posp (len old)) (equal (len old) (len new))
               (equal (car (fn2-mk-consistency-observation old new proof)) :ok))
          (equal (fn-b3-words 8 (fn2-mk-mth old)) (fn-b3-words 8 (fn2-mk-mth new))))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn2-mk-mth fn2-mk-consistency-run fn2-mk-load-proof
                                    fn2-mk-table-init fn2-digests-init fn2-mk-phase))))
(defthm mk-equal-packed-roots
 (implies (equal (fn-b3-words 8 (car (fn2-mk-model xs fuel)))
                 (fn-b3-words 8 (car (fn2-mk-model ys fuel))))
          (equal (car (fn2-mk-model xs fuel)) (car (fn2-mk-model ys fuel))))
 :rule-classes nil
 :hints (("Goal" :use (mk-model-round-trip (:instance mk-model-round-trip (xs ys)))
          :in-theory (theory 'minimal-theory))))

(defun-nx mk-run-openings (old new proof)
 (append (cadr (fn2-mk-model old (len old)))
         (cadr (fn2-mk-model new (len new)))
         (cadr (fn2-mk-consistency-observation old new proof))))

(defthm mk-equal-size-binding
 (implies (and (true-list-listp old) (true-list-listp new)
               (posp (len old)) (equal (len old) (len new))
               (fn2-mk-consistency-premise old new proof)
               (equal (car (fn2-mk-consistency-observation old new proof)) :ok))
          (equal old new))
 :rule-classes nil
 :hints (("Goal" :use (mk-same-size-observation
                       (:instance mk-equal-packed-roots (xs old) (ys new) (fuel (len old)))
                       (:instance mk-tree-binding (xs old) (ys new) (fuel (len old))
                         (all (mk-run-openings old new proof))))
          :in-theory (e/d (mk-matchp fn2-mk-mth)
                          (fn2-mk-consistency-observation fn2-mk-model fn2-mk-integrity-openings)))))

(defthm mk-larger-old-run
 (implies (and (< new old) (equal (fn2-mk-phase 0 m) 0))
          (equal (car (fn2-mk-consistency-run 64 old new count d m)) :size))
 :hints (("Goal" :expand (fn2-mk-consistency-run 64 old new count d m)
          :in-theory (e/d (fn2-mk-verify-consistency)
                          (fn2-mk-phase fn2-mk-proof-openings)))))

(defthm mk-larger-old-observation
 (implies (< (len new) (len old))
          (equal (car (fn2-mk-consistency-observation old new proof)) :size))
 :hints (("Goal" :in-theory (disable fn2-mk-mth fn2-mk-consistency-run fn2-mk-load-proof
                                    fn2-mk-table-init fn2-digests-init fn2-mk-phase))))

(defthm mk-nongrowing-prefix
 (implies (and (true-list-listp old) (true-list-listp new)
               (or (not (< (len old) (len new))) (zp (len old)))
               (fn2-mk-consistency-premise old new proof)
               (equal (car (fn2-mk-consistency-observation old new proof)) :ok))
          (equal old (take (len old) new)))
 :rule-classes nil
 :hints (("Goal" :cases ((consp old) (< (len new) (len old)))
          :do-not-induct t :use mk-equal-size-binding
          :in-theory (e/d (len) (fn2-mk-consistency-premise fn2-mk-consistency-observation)))))
