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

; Word J (absolute) of the tape as the pool shows it: the word, or the verdict.
(defun adt-pr-word (j pages res)
  (declare (xargs :guard (natp j) :verify-guards nil))
  (let ((p (floor (nfix j) *pgs-page-words*)))
    (if (member p res)
        (nth (mod (nfix j) *pgs-page-words*) (nth p pages))
      (list :need-page p))))

; Read words [J, END): a missing page is filled and the SAME word read again.
; (mv words res fills); FILLS the pages filled, most recent first.
(defun adt-pr-read-words (j end pages res frames acc fills)
  (declare (xargs :guard (and (natp j) (natp end) (true-listp acc))
                  :measure (+ (* 2 (nfix (- (nfix end) (nfix j))))
                              (if (member (floor (nfix j) *pgs-page-words*) res) 0 1))
                  :verify-guards nil))
  (cond ((not (< (nfix j) (nfix end))) (mv (reverse acc) res fills))
        ((member (floor (nfix j) *pgs-page-words*) res)
         (adt-pr-read-words (+ 1 (nfix j)) end pages res frames
                            (cons (adt-pr-word j pages res) acc) fills))
        (t (let ((p (floor (nfix j) *pgs-page-words*)))
             (adt-pr-read-words j end pages (adt-pr-fill p res frames) frames acc (cons p fills))))))

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

; The word at J of the page image is the tape's.
(defthm adt-pr-nth-of-pages
  (implies (and (true-listp w) (natp j) (< j (len w)))
           (equal (nth (mod j *pgs-page-words*) (nth (floor j *pgs-page-words*) (adt-tp-pages w)))
                  (nth j w)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-tp-nth-of-pages (k (floor j *pgs-page-words*)))
                 (:instance adt-pr-floor-mod)
                 (:instance adt-pr-nth-of-page (m (mod j *pgs-page-words*))
                            (v (nthcdr (* *pgs-page-words* (floor j *pgs-page-words*)) w)))
                 (:instance adt-pr-nth-of-nthcdr (a (mod j *pgs-page-words*))
                            (b (* *pgs-page-words* (floor j *pgs-page-words*)))))
           :in-theory (disable adt-tp-nth-of-pages adt-pr-nth-of-page adt-pr-nth-of-nthcdr adt-pr-floor-mod
                               floor mod adt-tp-page-short adt-tp-page-long))))

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
           (equal (mv-nth 0 (adt-pr-read-words j end (adt-tp-pages w) res frames acc fills))
                  (revappend acc (adt-tp-take (- end j) (nthcdr j w)))))
  :hints (("Goal" :induct (adt-pr-read-words j end (adt-tp-pages w) res frames acc fills)
           :in-theory (e/d (adt-pr-word) (adt-pr-nth-of-pages adt-tp-pages adt-pr-take-step floor mod)))
          ("Subgoal *1/2" :use ((:instance adt-pr-nth-of-pages (j j)) (:instance adt-pr-take-step)))))

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(defthm adt-pr-mod-bounds
  (implies (natp j)
           (and (<= 0 (mod j *pgs-page-words*)) (< (mod j *pgs-page-words*) *pgs-page-words*)))
  :rule-classes nil)

(defthm adt-pr-floor-natp
  (implies (natp j) (natp (floor j *pgs-page-words*)))
  :rule-classes :type-prescription)

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
(defun adt-pr-bnd (j end res)
  (declare (xargs :guard (and (natp j) (natp end)) :verify-guards nil))
  (if (<= (nfix end) (nfix j))
      0
    (- (adt-pr-span j end)
       (if (member (floor (nfix j) *pgs-page-words*) res) 1 0))))

(defthm adt-pr-read-words-fills
  (implies (and (natp j) (natp end))
           (<= (len (mv-nth 2 (adt-pr-read-words j end pages res frames acc fills)))
               (+ (len fills) (adt-pr-bnd j end res))))
  :hints (("Goal" :induct (adt-pr-read-words j end pages res frames acc fills)
           :in-theory (e/d (adt-pr-bnd adt-pr-span) (floor mod adt-pr-fill)))))

(defthm adt-pr-read-words-residency
  (implies (<= (len res) (adt-pr-cap frames))
           (<= (len (mv-nth 1 (adt-pr-read-words j end pages res frames acc fills)))
               (adt-pr-cap frames)))
  :hints (("Goal" :induct (adt-pr-read-words j end pages res frames acc fills)
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
