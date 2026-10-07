; fn: reading the persisted page image through a frame pool (lane s-pool,
; 2026-10-07; Phase 2b of build/coordinator/STORAGE-PROGRAM-20261006.md).
; The read half of books/def-representation-pages.lisp: a TAPE's words
; [J, END) are read page by page through a pool of RES resident pages, a
; missing page being FILLED and the same word read again (the page store's
; `pgs-x-read' verdict (:need-page I PHYS) answered by a fill).  Every
; function and theorem here is a function of the schema or of the tape's
; words; an instance (`NAME-read-row') is the library's at its schema
; constant (books/def-representation.lisp, `rep-pages-events').
;
; The pool: RES is the resident pages, most recent first; a fill makes the
; page the most recent and evicts the least recent past the frame count.
; "A frame the ledger allows" (books/page-read-ledger.lisp) is not modelled
; (one reader pins nothing); owed as CPG-POOL-LEDGER.

(in-package "ACL2")
(include-book "def-representation-pages")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(defun adt-pr-cap (frames)
  (declare (xargs :guard t))
  (max 1 (nfix frames)))

(defun adt-pr-fill (p res frames)
  (declare (xargs :guard t :verify-guards nil))
  (take (adt-pr-cap frames) (cons p (remove p res))))

(defthm adt-pr-member-of-fill
  (member p (adt-pr-fill p res frames))
  :hints (("Goal" :in-theory (enable adt-pr-fill adt-pr-cap))))

(defthm adt-pr-len-of-fill
  (<= (len (adt-pr-fill p res frames)) (adt-pr-cap frames))
  :hints (("Goal" :in-theory (enable adt-pr-fill))))

; Word J (absolute) of the tape TAG as the pool shows it: the word, or the verdict.
; A pool page is (TAG . PAGE): the catalog's tapes share one pool.
(defun adt-pr-word (tag j pages res)
  (declare (xargs :guard (natp j) :verify-guards nil))
  (let ((p (floor (nfix j) *pgs-page-words*)))
    (if (member (cons tag p) res)
        (nth (mod (nfix j) *pgs-page-words*) (nth p pages))
      (list :need-page tag p))))

; Read words [J, END): a missing page is filled and the SAME word read again.
; (mv words res fills); FILLS the pages filled, most recent first.
(defun adt-pr-read-words (tag j end pages res frames acc fills)
  (declare (xargs :guard (and (natp j) (natp end) (true-listp acc))
                  :measure (+ (* 2 (nfix (- (nfix end) (nfix j))))
                              (if (member (cons tag (floor (nfix j) *pgs-page-words*)) res) 0 1))
                  :verify-guards nil))
  (cond ((not (< (nfix j) (nfix end))) (mv (reverse acc) res fills))
        ((member (cons tag (floor (nfix j) *pgs-page-words*)) res)
         (adt-pr-read-words tag (+ 1 (nfix j)) end pages res frames
                            (cons (adt-pr-word tag j pages res) acc) fills))
        (t (let ((p (floor (nfix j) *pgs-page-words*)))
             (adt-pr-read-words tag j end pages (adt-pr-fill (cons tag p) res frames) frames acc (cons (cons tag p) fills))))))

; The pages words [J, END) touch.
(defun adt-pr-span (j end)
  (declare (xargs :guard (and (natp j) (natp end))))
  (if (<= (nfix end) (nfix j))
      0
    (+ 1 (- (floor (+ -1 (nfix end)) *pgs-page-words*) (floor (nfix j) *pgs-page-words*)))))

(defthm adt-pr-nth-of-take
  (implies (and (natp m) (< m (nfix n)) (< m (len v)))
           (equal (nth m (adt-tp-take n v)) (nth m v)))
  :hints (("Goal" :in-theory (enable adt-tp-take nth))))

(defthm adt-pr-nth-of-append
  (implies (and (natp m) (< m (len v)))
           (equal (nth m (append v z)) (nth m v)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm adt-pr-nth-of-page-short
  (implies (and (natp m) (< m (len v)) (true-listp v) (<= (len v) *pgs-page-words*))
           (equal (nth m (adt-tp-page v)) (nth m v)))
  :hints (("Goal" :in-theory (disable adt-tp-page-long adt-tp-page-short)
           :use ((:instance adt-tp-page-short (w v))
                 (:instance adt-pr-nth-of-append (z (adt-tp-zeros (- *pgs-page-words* (len v)))))))))

(defthm adt-pr-nth-of-page-long
  (implies (and (natp m) (< m *pgs-page-words*) (< m (len v)) (true-listp v) (<= *pgs-page-words* (len v)))
           (equal (nth m (adt-tp-page v)) (nth m v)))
  :hints (("Goal" :in-theory (disable adt-tp-page-long adt-tp-page-short)
           :use ((:instance adt-tp-page-long (w v)) (:instance adt-pr-nth-of-take (n *pgs-page-words*))))))

(defthm adt-pr-nth-of-page
  (implies (and (natp m) (< m *pgs-page-words*) (< m (len v)) (true-listp v))
           (equal (nth m (adt-tp-page v)) (nth m v)))
  :hints (("Goal" :in-theory (disable adt-tp-page-long adt-tp-page-short adt-pr-nth-of-page-short adt-pr-nth-of-page-long)
           :use (adt-pr-nth-of-page-short adt-pr-nth-of-page-long))))

(defthm adt-pr-nth-of-nthcdr
  (implies (and (natp a) (natp b))
           (equal (nth a (nthcdr b w)) (nth (+ a b) w)))
  :hints (("Goal" :in-theory (enable nth nthcdr))))

(defthm adt-pr-floor-mod
  (implies (natp j)
           (equal (+ (mod j *pgs-page-words*) (* *pgs-page-words* (floor j *pgs-page-words*))) j))
  :hints (("Goal" :in-theory (enable mod))))

(defthm adt-pr-mod-bounds
  (implies (natp j)
           (and (<= 0 (mod j *pgs-page-words*)) (< (mod j *pgs-page-words*) *pgs-page-words*)))
  :rule-classes nil)

(defthm adt-pr-floor-natp
  (implies (natp j) (natp (floor j *pgs-page-words*)))
  :rule-classes :type-prescription)

(defthm adt-pr-mod-natp
  (implies (natp j) (natp (mod j *pgs-page-words*)))
  :rule-classes :type-prescription)

; The arithmetic of a word's place, once, with floor and mod closed.
(defthm adt-pr-place
  (implies (and (natp j) (natp len) (< j len))
           (and (< (* *pgs-page-words* (floor j *pgs-page-words*)) len)
                (< (mod j *pgs-page-words*) (- len (* *pgs-page-words* (floor j *pgs-page-words*))))
                (< (mod j *pgs-page-words*) *pgs-page-words*)
                (equal (+ (mod j *pgs-page-words*) (* *pgs-page-words* (floor j *pgs-page-words*))) j)))
  :hints (("Goal" :do-not-induct t :in-theory (disable floor mod)
           :use (adt-pr-floor-mod adt-pr-mod-bounds)))
  :rule-classes nil)

; The word at J of the page image is the tape's.
(defthm adt-pr-nth-of-pages
  (implies (and (true-listp w) (natp j) (< j (len w)))
           (equal (nth (mod j *pgs-page-words*) (nth (floor j *pgs-page-words*) (adt-tp-pages w)))
                  (nth j w)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-tp-nth-of-pages (k (floor j *pgs-page-words*)))
                 (:instance adt-pr-place (len (len w)))
                 (:instance adt-pr-nth-of-page (m (mod j *pgs-page-words*))
                            (v (nthcdr (* *pgs-page-words* (floor j *pgs-page-words*)) w)))
                 (:instance adt-pr-nth-of-nthcdr (a (mod j *pgs-page-words*))
                            (b (* *pgs-page-words* (floor j *pgs-page-words*)))))
           :in-theory (e/d (adt-tp-len-nthcdr)
                           (adt-tp-nth-of-pages adt-pr-nth-of-page adt-pr-nth-of-nthcdr adt-pr-floor-mod
                            floor mod adt-tp-page-short adt-tp-page-long)))))

(defthm adt-pr-nthcdr-cons
  (implies (and (natp j) (< j (len w)))
           (equal (nthcdr j w) (cons (nth j w) (nthcdr (+ 1 j) w))))
  :hints (("Goal" :in-theory (enable nth nthcdr) :induct (nth j w))))

(defthm adt-pr-take-step
  (implies (and (natp j) (< j (len w)) (natp end) (< j end))
           (equal (adt-tp-take (- end j) (nthcdr j w))
                  (cons (nth j w) (adt-tp-take (- end (+ 1 j)) (nthcdr (+ 1 j) w)))))
  :hints (("Goal" :in-theory (e/d (adt-tp-take) (adt-pr-nthcdr-cons))
           :use adt-pr-nthcdr-cons)))

(defthm adt-pr-reverse-is-revappend
  (implies (true-listp x) (equal (reverse x) (revappend x nil)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm adt-pr-take-zero
  (equal (adt-tp-take 0 x) nil)
  :hints (("Goal" :in-theory (enable adt-tp-take))))

; Reading [J, END) through the pool gives the tape's words there, whatever the
; pool holds and however small it is.
(defthm adt-pr-read-words-words
  (implies (and (true-listp w) (natp j) (natp end) (<= j end) (<= end (len w)) (true-listp acc))
           (equal (mv-nth 0 (adt-pr-read-words tag j end (adt-tp-pages w) res frames acc fills))
                  (revappend acc (adt-tp-take (- end j) (nthcdr j w)))))
  :hints (("Goal" :induct (adt-pr-read-words tag j end (adt-tp-pages w) res frames acc fills)
           :in-theory (e/d (adt-pr-word) (adt-pr-nth-of-pages adt-tp-pages adt-pr-take-step floor mod)))
          ("Subgoal *1/2" :use ((:instance adt-pr-nth-of-pages (j j)) (:instance adt-pr-take-step)))))


(defthm adt-pr-floor-succ
  (implies (natp j)
           (or (equal (floor (+ 1 j) *pgs-page-words*) (floor j *pgs-page-words*))
               (equal (floor (+ 1 j) *pgs-page-words*) (+ 1 (floor j *pgs-page-words*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable floor mod)
           :use (adt-pr-floor-mod (:instance adt-pr-floor-mod (j (+ 1 j)))
                 adt-pr-mod-bounds (:instance adt-pr-mod-bounds (j (+ 1 j)))))))

(defthm adt-pr-floor-mono
  (implies (and (natp j) (natp k) (<= j k))
           (<= (floor j *pgs-page-words*) (floor k *pgs-page-words*)))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t :in-theory (disable floor mod)
           :use (adt-pr-floor-mod (:instance adt-pr-floor-mod (j k))
                 adt-pr-mod-bounds (:instance adt-pr-mod-bounds (j k))))))

; Pages still to fill: the pages of [J, END), less the current one if resident.
(defun adt-pr-bnd (tag j end res)
  (declare (xargs :guard (and (natp j) (natp end)) :verify-guards nil))
  (if (<= (nfix end) (nfix j))
      0
    (- (adt-pr-span j end)
       (if (member (cons tag (floor (nfix j) *pgs-page-words*)) res) 1 0))))

(defthm adt-pr-read-words-fills
  (implies (and (natp j) (natp end))
           (<= (len (mv-nth 2 (adt-pr-read-words tag j end pages res frames acc fills)))
               (+ (len fills) (adt-pr-bnd tag j end res))))
  :hints (("Goal" :induct (adt-pr-read-words tag j end pages res frames acc fills)
           :in-theory (e/d (adt-pr-bnd adt-pr-span) (floor mod adt-pr-fill)))))

(defthm adt-pr-read-words-residency
  (implies (<= (len res) (adt-pr-cap frames))
           (<= (len (mv-nth 1 (adt-pr-read-words tag j end pages res frames acc fills)))
               (adt-pr-cap frames)))
  :hints (("Goal" :induct (adt-pr-read-words tag j end pages res frames acc fills)
           :in-theory (disable floor mod adt-pr-fill adt-pr-cap))))

(defthm adt-pr-floor-plus-page
  (implies (natp x)
           (equal (floor (+ *pgs-page-words* x) *pgs-page-words*) (+ 1 (floor x *pgs-page-words*))))
  :hints (("Goal" :do-not-induct t :in-theory (disable floor mod)
           :use (adt-pr-floor-mod (:instance adt-pr-floor-mod (j (+ *pgs-page-words* x)))
                 adt-pr-mod-bounds (:instance adt-pr-mod-bounds (j (+ *pgs-page-words* x)))))))

(defthm adt-pr-floor-plus-small
  (implies (and (natp x) (natp y) (< y *pgs-page-words*))
           (<= (floor (+ x y) *pgs-page-words*) (+ 1 (floor x *pgs-page-words*))))
  :hints (("Goal" :do-not-induct t :in-theory (disable floor mod)
           :use (adt-pr-floor-mod (:instance adt-pr-floor-mod (j (+ x y)))
                 adt-pr-mod-bounds (:instance adt-pr-mod-bounds (j (+ x y)))))))

; A record of W words read from OFF touches at most one page more than W
; words take.
(defthm adt-pr-span-of-record
  (implies (and (natp off) (natp w))
           (<= (adt-pr-span off (+ off w)) (+ 1 (adt-tp-npages w))))
  :hints (("Goal" :induct (adt-tp-npages w)
           :in-theory (e/d (adt-pr-span adt-tp-npages) (floor mod)))
          ("Subgoal *1/2" :use ((:instance adt-pr-floor-plus-small (x off) (y (+ -1 w)))))))

; The record of W words at word OFF of the tape, decoded: (mv rec res fills).
(defun adt-pr-read-rec (tag s off w pages res frames fills)
  (declare (xargs :guard (and (natp off) (natp w)) :verify-guards nil))
  (mv-let (ws res fills)
    (adt-pr-read-words tag off (+ (nfix off) (nfix w)) pages res frames nil fills)
    (mv (car (adt-tp-dseq s ws)) res fills)))

(defthm adt-pr-append-take-nthcdr
  (implies (and (true-listp a) (natp i) (<= i (len a)))
           (equal (append (take i a) (nthcdr i a)) a)))

(defthm adt-pr-nthcdr-of-append-len
  (implies (and (true-listp p) (equal (len p) off))
           (equal (nthcdr off (append p r)) r)))

(defthm adt-pr-take-of-append-len
  (implies (and (true-listp x) (equal (len x) w))
           (equal (adt-tp-take w (append x r)) x))
  :hints (("Goal" :use ((:instance adt-tp-take-of-append (n w) (a x) (b r))
                        (:instance adt-tp-take-of-len (a x)))
           :in-theory (disable adt-tp-take-of-append adt-tp-take-of-len))))

(defthm adt-pr-seq-words-of-split
  (implies (and (natp i) (< i (len a)) (true-listp a))
           (equal (adt-tp-seq-words s a)
                  (append (adt-tp-seq-words s (take i a))
                          (append (adt-tp-rw s (nth i a))
                                  (adt-tp-seq-words s (nthcdr (+ 1 i) a))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-pr-append-take-nthcdr)
                 (:instance adt-tp-seq-words-of-append (a (take i a)) (b (nthcdr i a)))
                 (:instance adt-pr-nthcdr-cons (j i) (w a)))
           :in-theory (disable adt-pr-append-take-nthcdr adt-tp-seq-words-of-append adt-pr-nthcdr-cons
                               adt-tp-seq-words-of-snoc take nthcdr))))

(defthm adt-pr-len-seq-words-split
  (implies (and (natp i) (< i (len a)) (true-listp a))
           (<= (+ (len (adt-tp-seq-words s (take i a))) (len (adt-tp-rw s (nth i a))))
               (len (adt-tp-seq-words s a))))
  :hints (("Goal" :use adt-pr-seq-words-of-split :in-theory (disable adt-pr-seq-words-of-split take nthcdr))))

(defthm adt-pr-rec-p-of-nth
  (implies (and (adt-seq-p s a) (natp i) (< i (len a)))
           (adt-rec-p s (nth i a)))
  :hints (("Goal" :in-theory (enable nth adt-seq-p))))

(defthm adt-pr-seq-p-true-listp
  (implies (adt-seq-p s a) (true-listp a))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable adt-seq-p))))

(defthm adt-pr-dseq-of-rw
  (implies (and (adt-tp-schema-ok s) (adt-rec-p s x))
           (equal (car (adt-tp-dseq s (adt-tp-rw s x))) x))
  :hints (("Goal" :use ((:instance adt-tp-seq-roundtrip (a (list x)) (tail nil)))
           :in-theory (e/d (adt-seq-p) (adt-tp-seq-roundtrip)))))

; Row I of a sequence, read from its page image through the pool: OFF its word
; offset and W its width.
(defthm adt-pr-read-rec-is-nth
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a) (natp i) (< i (len a))
                (equal off (len (adt-tp-seq-words s (take i a))))
                (equal w (len (adt-tp-rw s (nth i a)))))
           (equal (mv-nth 0 (adt-pr-read-rec tag s off w (adt-tp-pages-of s a) res frames fills))
                  (nth i a)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-pr-read-rec adt-tp-pages-of)
                           (adt-tp-pages adt-tp-seq-words adt-tp-rw adt-pr-read-words-words
                            adt-pr-seq-words-of-split take nthcdr adt-tp-dseq adt-pr-dseq-of-rw
                            adt-pr-len-seq-words-split adt-pr-take-of-append-len adt-pr-nthcdr-of-append-len))
           :use ((:instance adt-pr-read-words-words (w (adt-tp-seq-words s a)) (j off) (end (+ off w))
                            (acc nil))
                 adt-pr-seq-words-of-split adt-pr-len-seq-words-split
                 (:instance adt-pr-dseq-of-rw (x (nth i a)))
                 (:instance adt-pr-nthcdr-of-append-len (p (adt-tp-seq-words s (take i a)))
                            (r (append (adt-tp-rw s (nth i a)) (adt-tp-seq-words s (nthcdr (+ 1 i) a)))))
                 (:instance adt-pr-take-of-append-len (x (adt-tp-rw s (nth i a)))
                            (r (adt-tp-seq-words s (nthcdr (+ 1 i) a)))))))
          )

(defthm adt-pr-read-rec-fills
  (implies (and (natp off) (natp w))
           (<= (len (mv-nth 2 (adt-pr-read-rec tag s off w pages res frames fills)))
               (+ (len fills) 1 (adt-tp-npages w))))
  :hints (("Goal" :in-theory (disable adt-pr-read-words-fills adt-pr-span-of-record adt-pr-bnd)
           :use ((:instance adt-pr-read-words-fills (j off) (end (+ off w)) (acc nil))
                 (:instance adt-pr-span-of-record)))
          ("Goal'" :in-theory (enable adt-pr-read-rec adt-pr-bnd))))

(defthm adt-pr-read-rec-residency
  (implies (<= (len res) (adt-pr-cap frames))
           (<= (len (mv-nth 1 (adt-pr-read-rec tag s off w pages res frames fills)))
               (adt-pr-cap frames)))
  :hints (("Goal" :in-theory (e/d (adt-pr-read-rec) (adt-pr-read-words-residency adt-pr-cap))
           :use ((:instance adt-pr-read-words-residency (j off) (end (+ (nfix off) (nfix w))) (acc nil))))))

; The directory of a sequence: for each record its word offset (from OFF) and
; width.  Entry I is the offset of record I, the sum of the widths before it.
(defun adt-pr-dir-rows (s rows off)
  (declare (xargs :guard (natp off) :verify-guards nil))
  (if (consp rows)
      (let ((w (len (adt-tp-rw s (car rows)))))
        (cons (list off w) (adt-pr-dir-rows s (cdr rows) (+ off w))))
    nil))

(defthm adt-pr-len-dir-rows
  (equal (len (adt-pr-dir-rows s rows off)) (len rows)))

(defun adt-pr-dir-ind (rows i off s)
  (if (consp rows)
      (adt-pr-dir-ind (cdr rows) (1- i) (+ off (len (adt-tp-rw s (car rows)))) s)
    (list i off)))

(defthm adt-pr-dir-rows-nth
  (implies (and (natp i) (< i (len rows)) (natp off))
           (equal (nth i (adt-pr-dir-rows s rows off))
                  (list (+ off (len (adt-tp-seq-words s (take i rows))))
                        (len (adt-tp-rw s (nth i rows))))))
  :hints (("Goal" :induct (adt-pr-dir-ind rows i off s)
           :in-theory (e/d (nth take adt-tp-seq-words) (adt-tp-rw adt-tp-fw)))))

; The directory is itself a tape of two-u64 records (offset, width): three
; words each, so entry I is at word 3I.
(defconst *adt-pr-dir-schema* '((:u64) (:u64)))

(defthm adt-pr-len-dir-rw
  (equal (len (adt-tp-rw *adt-pr-dir-schema* x)) 3))

(defthm adt-pr-len-dir-seq-words
  (equal (len (adt-tp-seq-words *adt-pr-dir-schema* a)) (* 3 (len a)))
  :hints (("Goal" :in-theory (enable adt-tp-seq-words))))

(defthm adt-pr-len-dir-seq-words-take
  (implies (and (natp i) (<= i (len a)))
           (equal (len (adt-tp-seq-words *adt-pr-dir-schema* (take i a))) (* 3 i)))
  :hints (("Goal" :in-theory (disable adt-pr-len-dir-seq-words)
           :use ((:instance adt-pr-len-dir-seq-words (a (take i a)))))))

; The words of a sequence from OFF fit a u64 (the offsets and widths are u64).
(defthm adt-pr-dir-rows-seq-p
  (implies (and (natp off) (< (+ off (len (adt-tp-seq-words s rows))) (expt 2 64)))
           (adt-seq-p *adt-pr-dir-schema* (adt-pr-dir-rows s rows off)))
  :hints (("Goal" :induct (adt-pr-dir-rows s rows off)
           :in-theory (e/d (adt-seq-p adt-tp-seq-words adt-rec-p adt-val-okp)
                           (adt-tp-rw adt-tp-fw)))
          ("Subgoal *1/2" :use ((:instance adt-tp-true-listp-rw (s s) (rec (car rows)))))))

; Row I through its directory entry: the entry read, then the row read, both
; through the one pool.
(defun adt-pr-read-indexed (s i dpages rpages res frames fills)
  (declare (xargs :guard (natp i) :verify-guards nil))
  (mv-let (ent res fills)
    (adt-pr-read-rec :dir *adt-pr-dir-schema* (* 3 (nfix i)) 3 dpages res frames fills)
    (adt-pr-read-rec :rows s (nfix (nth 0 ent)) (nfix (nth 1 ent)) rpages res frames fills)))

(defthm adt-pr-dir-schema-ok
  (adt-tp-schema-ok *adt-pr-dir-schema*))

(defthm adt-pr-dir-entry-read
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s rows) (natp i) (< i (len rows))
                (< (len (adt-tp-seq-words s rows)) (expt 2 64)))
           (equal (mv-nth 0 (adt-pr-read-rec tag *adt-pr-dir-schema* (* 3 i) 3
                                             (adt-tp-pages-of *adt-pr-dir-schema* (adt-pr-dir-rows s rows 0))
                                             res frames fills))
                  (list (len (adt-tp-seq-words s (take i rows)))
                        (len (adt-tp-rw s (nth i rows))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable adt-pr-read-rec-is-nth adt-pr-dir-rows-nth adt-pr-len-dir-rows
                               adt-pr-dir-rows-seq-p adt-pr-len-dir-seq-words-take adt-pr-len-dir-rw
                               adt-pr-read-rec adt-tp-pages-of adt-pr-dir-rows adt-pr-len-seq-words-split)
           :use ((:instance adt-pr-read-rec-is-nth (s *adt-pr-dir-schema*) (a (adt-pr-dir-rows s rows 0))
                            (off (* 3 i)) (w 3))
                 (:instance adt-pr-dir-rows-nth (off 0))
                 adt-pr-len-dir-rows
                 (:instance adt-pr-dir-rows-seq-p (off 0))
                 (:instance adt-pr-len-dir-seq-words-take (a (adt-pr-dir-rows s rows 0)))
                 (:instance adt-pr-len-dir-rw (x (nth i (adt-pr-dir-rows s rows 0))))
                 (:instance adt-pr-len-seq-words-split (a rows))))))

(defthm adt-pr-read-indexed-is-nth
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s rows) (natp i) (< i (len rows))
                (< (len (adt-tp-seq-words s rows)) (expt 2 64)))
           (equal (mv-nth 0 (adt-pr-read-indexed s i
                                                 (adt-tp-pages-of *adt-pr-dir-schema* (adt-pr-dir-rows s rows 0))
                                                 (adt-tp-pages-of s rows) res frames fills))
                  (nth i rows)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable adt-tp-pages-of adt-pr-dir-rows adt-pr-len-seq-words-split adt-pr-read-rec)
           :expand ((adt-pr-read-indexed s i (adt-tp-pages-of *adt-pr-dir-schema* (adt-pr-dir-rows s rows 0))
                                         (adt-tp-pages-of s rows) res frames fills)))))

; Two reads: the entry (3 words: at most 2 pages) and the row.
(defthm adt-pr-read-indexed-fills
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s rows) (natp i) (< i (len rows))
                (< (len (adt-tp-seq-words s rows)) (expt 2 64)))
           (<= (len (mv-nth 2 (adt-pr-read-indexed s i
                                                   (adt-tp-pages-of *adt-pr-dir-schema* (adt-pr-dir-rows s rows 0))
                                                   (adt-tp-pages-of s rows) res frames fills)))
               (+ (len fills) 3 (adt-tp-npages (len (adt-tp-rw s (nth i rows)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable adt-tp-pages-of adt-pr-dir-rows adt-pr-len-seq-words-split adt-pr-read-rec
                               adt-pr-read-rec-fills)
           :use ((:instance adt-pr-read-rec-fills (tag :dir) (s *adt-pr-dir-schema*) (off (* 3 i)) (w 3)
                            (pages (adt-tp-pages-of *adt-pr-dir-schema* (adt-pr-dir-rows s rows 0))))
                 (:instance adt-pr-read-rec-fills (tag :rows) (s s)
                            (off (len (adt-tp-seq-words s (take i rows))))
                            (w (len (adt-tp-rw s (nth i rows))))
                            (pages (adt-tp-pages-of s rows))
                            (res (mv-nth 1 (adt-pr-read-rec :dir *adt-pr-dir-schema* (* 3 i) 3
                                  (adt-tp-pages-of *adt-pr-dir-schema* (adt-pr-dir-rows s rows 0))
                                  res frames fills)))
                            (fills (mv-nth 2 (adt-pr-read-rec :dir *adt-pr-dir-schema* (* 3 i) 3
                                  (adt-tp-pages-of *adt-pr-dir-schema* (adt-pr-dir-rows s rows 0))
                                  res frames fills)))))
           :expand ((adt-pr-read-indexed s i (adt-tp-pages-of *adt-pr-dir-schema* (adt-pr-dir-rows s rows 0))
                                         (adt-tp-pages-of s rows) res frames fills)))))

(defthm adt-pr-read-indexed-residency
  (implies (<= (len res) (adt-pr-cap frames))
           (<= (len (mv-nth 1 (adt-pr-read-indexed s i dpages rpages res frames fills)))
               (adt-pr-cap frames)))
  :hints (("Goal" :in-theory (disable adt-pr-read-rec adt-pr-read-rec-residency adt-pr-cap)
           :use ((:instance adt-pr-read-rec-residency (tag :dir) (s *adt-pr-dir-schema*) (off (* 3 (nfix i))) (w 3)
                            (pages dpages))
                 (:instance adt-pr-read-rec-residency (tag :rows) (pages rpages)
                            (res (mv-nth 1 (adt-pr-read-rec :dir *adt-pr-dir-schema* (* 3 (nfix i)) 3 dpages res frames fills)))
                            (off (nfix (nth 0 (mv-nth 0 (adt-pr-read-rec :dir *adt-pr-dir-schema* (* 3 (nfix i)) 3 dpages res frames fills)))))
                            (w (nfix (nth 1 (mv-nth 0 (adt-pr-read-rec :dir *adt-pr-dir-schema* (* 3 (nfix i)) 3 dpages res frames fills)))))
                            (fills (mv-nth 2 (adt-pr-read-rec :dir *adt-pr-dir-schema* (* 3 (nfix i)) 3 dpages res frames fills)))))
           :expand ((adt-pr-read-indexed s i dpages rpages res frames fills)))))
