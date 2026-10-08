; fn: the staged keystone's pre-state is the previous commit's image (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM-20261006.md section 3.3, phase 2c).
;
; `fn-pck-x-stage-is-the-dirty' (paged-checkpoint-stage.lisp) assumes a mem0
; whose dirty pages hold the prefix tail then zeros, resident.  Here that state
; is derived from the image the previous commit left.
;
;   (pcki-img PW pgs-mem)   the tape invariant: pages 8..V-1 are all resident
;       (vi = 2); the arrays have the image's lengths (d = V, w = 2048 V); the
;       tape window (words 16384 .. 2048 V) is PW followed by zeros.
;
;   fn-pck-x-prestate   from (pcki-img PW mem), the image grown to NPN pages
;       (`pgs-x-grow-image': zero pages, resident), NPN covering the last tape
;       page of PW ++ a WL-word delta:
;         (pcks-res CNT (+ CNT WL) mem2)   every delta position is writable
;         (pgs-x-abs-dirty LP mem2) = (pck-shift 8 (adt-tp-dirty-at CNT TAIL zeros(WL)))
;       with CNT = (len PW), TAIL = PW's last partial page, LP the pages of that
;       set.  These are premises (1) and (2) of the keystone.  The tail page
;       needs no separate read: the invariant holds it resident.
;
;   fn-pck-x-image-after-commit   the invariant is the loop's: from
;       (pcki-img PW mem), growing, staging the delta rows and
;       `pgs-x-commit-durable' on the tape's dirty pages leave
;       (pcki-img PW++W mem4), W the words of the delta; the staging answers
;       :ok.  A store opened (every tape page filled and verified) establishes
;       the invariant once, and each publication keeps it.
;
; Scope.  `pgs-x-commit' between the staging and the durable marking touches
; the page store's tables and the image's word array only through the dirty
; pages' digests (pagestore-refine.lisp, pgs-x-words-0-of-commit); the
; invariant is stated over the w, d and v arrays and is closed under
; `pgs-x-commit-durable' here.  PCK-STAGE-NEED-PAGE (a tail page that is not
; resident answers (:need-page LP) under lazy open; fill and retry) stays owed.
; Premise (3) of the keystone (every program under 2^64 octets) is
; `adt-tp-seq-lens-ok', carried through.
(in-package "ACL2")
(include-book "paged-checkpoint-stage")
(include-book "history-pages-relocate")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The invariant.

(defun pcki-resident (lo hi pgs-mem)
  (declare (xargs :stobjs pgs-mem :measure (nfix (- (nfix hi) (nfix lo)))))
  (if (and (natp lo) (natp hi) (< lo hi))
      (and (< lo (pgs-v-length pgs-mem)) (equal (pgs-vi lo pgs-mem) 2) (pcki-resident (1+ lo) hi pgs-mem))
    t))

(defun pcki-img (pw pgs-mem)
  (declare (xargs :stobjs pgs-mem))
  (and (true-listp pw)
       (<= 8 (pgs-v-length pgs-mem))
       (equal (pgs-d-length pgs-mem) (pgs-v-length pgs-mem))
       (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem)))
       (<= (len pw) (* 2048 (- (pgs-v-length pgs-mem) 8)))
       (pcki-resident 8 (pgs-v-length pgs-mem) pgs-mem)
       (equal (pgs-x-words 0 16384 (* 2048 (- (pgs-v-length pgs-mem) 8)) pgs-mem)
              (append pw (adt-tp-zeros (- (* 2048 (- (pgs-v-length pgs-mem) 8)) (len pw)))))))

(in-theory (disable pcki-resident))

; -----------------------------------------------------------------------------
; The grown image: the old words, then zeros.

(defun pcki-resize-ind (j l n)
  (if (zp n) (list j l) (pcki-resize-ind (1- j) (if (consp l) (cdr l) l) (1- n))))

(defthm pcki-nth-resize-list
  (implies (natp j)
           (equal (nth j (resize-list l n d))
                  (if (< j (nfix n)) (if (< j (len l)) (nth j l) d) nil)))
  :hints (("Goal" :in-theory (enable nth) :induct (pcki-resize-ind j l n))))

(defthm pcki-word-of-grown
  (implies (and (natp j) (natp npn) (< (pgs-v-length pgs-mem) npn)
                (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem))))
           (equal (pgs-x-word 0 j (pgs-x-grow-image npn pgs-mem))
                  (cond ((< j (pgs-w-length pgs-mem)) (pgs-x-word 0 j pgs-mem))
                        ((< j (* 2048 npn)) 0)
                        (t nil))))
  :hints (("Goal" :in-theory (e/d (pgs-x-word-0 pgs-wi pgs-w-length) (pgs-x-grow-image))
           :use (fn-hp-grow-image-words (:instance pcki-nth-resize-list (l (nth *pgs-wi* pgs-mem)) (n (* 2048 npn)) (d 0))))))

(defthm pcki-wi-of-grown
  (implies (and (natp j) (natp npn) (< (pgs-v-length pgs-mem) npn)
                (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem))))
           (equal (pgs-wi j (pgs-x-grow-image npn pgs-mem))
                  (cond ((< j (pgs-w-length pgs-mem)) (pgs-wi j pgs-mem))
                        ((< j (* 2048 npn)) 0)
                        (t nil))))
  :hints (("Goal" :use pcki-word-of-grown :in-theory (e/d (pgs-x-word-0) (pgs-x-grow-image pcki-word-of-grown)))))

(defthm pcki-words-of-grown-old
  (implies (and (natp a) (natp k) (natp npn) (< (pgs-v-length pgs-mem) npn)
                (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem)))
                (<= (+ a k) (pgs-w-length pgs-mem)))
           (equal (pgs-x-words 0 a k (pgs-x-grow-image npn pgs-mem))
                  (pgs-x-words 0 a k pgs-mem)))
  :hints (("Goal" :induct (pcks-ind a k) :in-theory (e/d (pcks-words-step pcks-words-zero) (pgs-x-grow-image pgs-x-word-0 pcki-word-of-grown)))
          ("Subgoal *1/2" :use ((:instance pcki-wi-of-grown (j a))))))

(defthm pcki-zeros-pos (implies (posp k) (equal (adt-tp-zeros k) (cons 0 (adt-tp-zeros (1- k)))))
  :hints (("Goal" :expand ((adt-tp-zeros k)))))

(defthm pcki-words-of-grown-new
  (implies (and (natp a) (natp k) (natp npn) (< (pgs-v-length pgs-mem) npn)
                (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem)))
                (<= (pgs-w-length pgs-mem) a) (<= (+ a k) (* 2048 npn)))
           (equal (pgs-x-words 0 a k (pgs-x-grow-image npn pgs-mem))
                  (adt-tp-zeros k)))
  :hints (("Goal" :induct (pcks-ind a k) :in-theory (e/d (pcks-words-step pcks-words-zero) (pgs-x-grow-image pgs-x-word-0 pcki-word-of-grown)))
          ("Subgoal *1/2" :use ((:instance pcki-wi-of-grown (j a))))))

(in-theory (disable pcki-zeros-pos pcki-words-of-grown-new pcki-words-of-grown-old pcki-wi-of-grown pcki-word-of-grown))

(defthm pcki-zeros-append
  (implies (and (natp a) (natp b)) (equal (append (adt-tp-zeros a) (adt-tp-zeros b)) (adt-tp-zeros (+ a b))))
  :hints (("Goal" :induct (adt-tp-zeros a) :in-theory (enable adt-tp-zeros))))

(defthm pcki-arith1
  (implies (and (natp v) (natp n) (<= 8 v) (< v n))
           (and (equal (+ (* 2048 (- v 8)) (* 2048 (- n v))) (* 2048 (- n 8)))
                (equal (+ 16384 (* 2048 (- v 8))) (* 2048 v)))))

(defthm pcki-window-parts
  (implies (and (pcki-img pw pgs-mem) (natp npn) (< (pgs-v-length pgs-mem) npn))
           (equal (append (pgs-x-words 0 16384 (* 2048 (- (pgs-v-length pgs-mem) 8)) (pgs-x-grow-image npn pgs-mem))
                          (pgs-x-words 0 (* 2048 (pgs-v-length pgs-mem)) (* 2048 (- npn (pgs-v-length pgs-mem))) (pgs-x-grow-image npn pgs-mem)))
                  (append pw (adt-tp-zeros (- (* 2048 (- npn 8)) (len pw))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcki-words-of-grown-old (a 16384) (k (* 2048 (- (pgs-v-length pgs-mem) 8))))
                 (:instance pcki-words-of-grown-new (a (* 2048 (pgs-v-length pgs-mem))) (k (* 2048 (- npn (pgs-v-length pgs-mem)))))
                 (:instance pcki-zeros-append (a (- (* 2048 (- (pgs-v-length pgs-mem) 8)) (len pw))) (b (* 2048 (- npn (pgs-v-length pgs-mem)))))
                 (:instance pcki-arith1 (v (pgs-v-length pgs-mem)) (n npn)))
           :in-theory (e/d (pcki-img) (pgs-x-words pgs-x-grow-image adt-tp-zeros pcki-words-of-grown-old pcki-words-of-grown-new pcki-zeros-append pcks-words-step)))))

(defthm pcki-window-of-grown
  (implies (and (pcki-img pw pgs-mem) (natp npn) (< (pgs-v-length pgs-mem) npn))
           (equal (pgs-x-words 0 16384 (* 2048 (- npn 8)) (pgs-x-grow-image npn pgs-mem))
                  (append pw (adt-tp-zeros (- (* 2048 (- npn 8)) (len pw))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pgs-x-words-split (s 0) (a 16384) (k1 (* 2048 (- (pgs-v-length pgs-mem) 8))) (k2 (* 2048 (- npn (pgs-v-length pgs-mem))))
                            (pgs-mem (pgs-x-grow-image npn pgs-mem)))
                 pcki-window-parts
                 (:instance pcki-arith1 (v (pgs-v-length pgs-mem)) (n npn)))
           :in-theory (e/d (pcki-img) (pgs-x-words-split pgs-x-words pgs-x-grow-image adt-tp-zeros pcki-window-parts pcki-words-of-grown-new pcki-words-of-grown-old pcki-wi-of-grown pcki-word-of-grown pcks-words-step)))))

(in-theory (disable pcki-window-of-grown pcki-window-parts pcki-zeros-append))

; -----------------------------------------------------------------------------
; List facts: the slice of the tape window that holds the dirty pages.

(defthm pcki-nthcdr-append
  (implies (and (natp m) (<= m (len a)))
           (equal (nthcdr m (append a b)) (append (nthcdr m a) b)))
  :hints (("Goal" :induct (nthcdr m a))))

(defun pcki-kz-ind (k z) (if (zp k) z (pcki-kz-ind (1- k) (1- z))))

(defthm pcki-take-zeros
  (implies (and (natp k) (natp z) (<= k z))
           (equal (take k (adt-tp-zeros z)) (adt-tp-zeros k)))
  :hints (("Goal" :induct (pcki-kz-ind k z) :in-theory (e/d (take pcki-zeros-pos) (adt-tp-zeros)))))

(defun pcki-len-ind (tl) (if (atom tl) tl (pcki-len-ind (cdr tl))))

(defthm pcki-take-append
  (implies (and (true-listp tl) (natp j))
           (equal (take (+ (len tl) j) (append tl x)) (append tl (take j x))))
  :hints (("Goal" :induct (pcki-len-ind tl) :in-theory (enable take))))

(defthm pcki-slice-list
  (implies (and (true-listp pw) (natp q) (natp n) (natp z)
                (<= (* 2048 q) (len pw)) (<= (len pw) (* 2048 (+ q n)))
                (<= (* 2048 (+ q n)) (+ (len pw) z)))
           (equal (take (* 2048 n) (nthcdr (* 2048 q) (append pw (adt-tp-zeros z))))
                  (append (nthcdr (* 2048 q) pw)
                          (adt-tp-zeros (- (* 2048 n) (- (len pw) (* 2048 q)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcki-nthcdr-append (m (* 2048 q)) (a pw) (b (adt-tp-zeros z)))
                 (:instance pcks-len-tail (k q))
                 (:instance pcki-take-append (tl (nthcdr (* 2048 q) pw)) (j (- (* 2048 n) (- (len pw) (* 2048 q))))
                            (x (adt-tp-zeros z)))
                 (:instance pcki-take-zeros (k (- (* 2048 n) (- (len pw) (* 2048 q)))) (z z)))
           :in-theory (disable pcki-nthcdr-append pcks-len-tail pcki-take-append pcki-take-zeros adt-tp-zeros nthcdr take))))

(defthm pcki-slice-words
  (implies (and (natp q) (natp n) (natp tt) (<= (+ q n) tt))
           (equal (pgs-x-words 0 (* 2048 (+ 8 q)) (* 2048 n) pgs-mem)
                  (take (* 2048 n) (nthcdr (* 2048 q) (pgs-x-words 0 16384 (* 2048 tt) pgs-mem)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pgs-x-nthcdr-of-words (s 0) (a 16384) (j (* 2048 q)) (k (* 2048 tt)))
                 (:instance pgs-x-take-of-words (s 0) (a (+ 16384 (* 2048 q))) (j (* 2048 n)) (k (- (* 2048 tt) (* 2048 q)))))
           :in-theory (disable pgs-x-nthcdr-of-words pgs-x-take-of-words pgs-x-words))))

(in-theory (disable pcki-slice-words pcki-slice-list pcki-take-append pcki-nthcdr-append pcki-take-zeros))

(defthm pcki-pad-npages
  (implies (natp x) (equal (adt-tp-pad x) (- (* 2048 (adt-tp-npages x)) x)))
  :hints (("Goal" :induct (adt-tp-pad x) :in-theory (e/d (adt-tp-pad adt-tp-npages) (pcks-npages-closed)))))

(defthm pcki-pad-closed
  (implies (natp x) (equal (adt-tp-pad x) (- (* 2048 (floor (+ x 2047) 2048)) x)))
  :hints (("Goal" :use (pcki-pad-npages pcks-npages-closed) :in-theory (disable pcki-pad-npages pcks-npages-closed))))

(defthm pcki-pages-of-zero-padded
  (implies (and (true-listp tail) (natp wl))
           (equal (adt-tp-pages (append tail (adt-tp-zeros (- (* 2048 (floor (+ (len tail) wl 2047) 2048)) (len tail)))))
                  (adt-tp-pages (append tail (adt-tp-zeros wl)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcks-pages-of-padded (w (append tail (adt-tp-zeros wl))))
                 (:instance pcki-pad-closed (x (+ (len tail) wl)))
                 (:instance pcki-zeros-append (a wl) (b (adt-tp-pad (+ (len tail) wl)))))
           :in-theory (disable pcks-pages-of-padded pcki-pad-closed pcki-zeros-append adt-tp-pad adt-tp-pages adt-tp-zeros))))

(defthm pcki-take-pw-zeros
  (implies (and (true-listp pw) (natp k) (natp z) (<= (len pw) k) (<= k (+ (len pw) z)))
           (equal (take k (append pw (adt-tp-zeros z)))
                  (append pw (adt-tp-zeros (- k (len pw))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcki-take-append (tl pw) (j (- k (len pw))) (x (adt-tp-zeros z)))
                 (:instance pcki-take-zeros (k (- k (len pw)))))
           :in-theory (disable pcki-take-append pcki-take-zeros adt-tp-zeros take))))

(defthm pcki-grow-same
  (implies (<= npn (pgs-v-length pgs-mem))
           (equal (pgs-x-grow-image npn pgs-mem) pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-grow-image))))

(defthm pcki-window-any
  (implies (and (pcki-img pw pgs-mem) (natp npn) (natp tt) (<= (len pw) (* 2048 tt)) (<= (+ 8 tt) npn))
           (equal (pgs-x-words 0 16384 (* 2048 tt) (pgs-x-grow-image npn pgs-mem))
                  (append pw (adt-tp-zeros (- (* 2048 tt) (len pw))))))
  :hints (("Goal" :do-not-induct t
           :cases ((< (pgs-v-length pgs-mem) npn)))
          ("Subgoal 2" :use ((:instance pcki-grow-same)
                             (:instance pgs-x-take-of-words (s 0) (a 16384) (j (* 2048 tt)) (k (* 2048 (- (pgs-v-length pgs-mem) 8)))
                                        (pgs-mem pgs-mem))
                             (:instance pcki-take-pw-zeros (k (* 2048 tt)) (z (- (* 2048 (- (pgs-v-length pgs-mem) 8)) (len pw)))))
           :in-theory (e/d (pcki-img) (pcki-grow-same pgs-x-take-of-words pcki-take-pw-zeros pgs-x-words adt-tp-zeros take)))
          ("Subgoal 1" :use ((:instance pcki-window-of-grown)
                             (:instance pgs-x-take-of-words (s 0) (a 16384) (j (* 2048 tt)) (k (* 2048 (- npn 8)))
                                        (pgs-mem (pgs-x-grow-image npn pgs-mem)))
                             (:instance pcki-take-pw-zeros (k (* 2048 tt)) (z (- (* 2048 (- npn 8)) (len pw)))))
           :in-theory (e/d (pcki-img) (pcki-window-of-grown pgs-x-take-of-words pcki-take-pw-zeros pgs-x-words pgs-x-grow-image adt-tp-zeros take)))))

; -----------------------------------------------------------------------------
; Residency of the delta's positions.

(defthm pcki-resident-vi
  (implies (and (pcki-resident lo hi pgs-mem) (natp lo) (natp hi) (natp p) (<= lo p) (< p hi))
           (and (< p (pgs-v-length pgs-mem)) (equal (pgs-vi p pgs-mem) 2)))
  :hints (("Goal" :induct (pcki-resident lo hi pgs-mem)
           :in-theory (enable pcki-resident))))

(defthm pcki-writable
  (implies (and (pcki-img pw pgs-mem) (natp npn) (natp q) (< (+ 8 (floor q 2048)) npn))
           (pcks-writable q (pgs-x-grow-image npn pgs-mem)))
  :hints (("Goal" :do-not-induct t :cases ((< (pgs-v-length pgs-mem) npn)))
          ("Subgoal 2" :use ((:instance pcki-grow-same)
                             (:instance pcki-resident-vi (lo 8) (hi (pgs-v-length pgs-mem)) (p (+ 8 (floor q 2048)))))
           :in-theory (e/d (pcki-img pcks-writable) (pcki-grow-same pcki-resident-vi)))
          ("Subgoal 1" :use ((:instance fn-hp-grow-image-lengths (np (pgs-v-length pgs-mem)) (npn npn))
                             (:instance fn-hp-grow-image-vi (q (+ 8 (floor q 2048))))
                             (:instance pcki-resident-vi (lo 8) (hi (pgs-v-length pgs-mem)) (p (+ 8 (floor q 2048)))))
           :in-theory (e/d (pcki-img pcks-writable) (fn-hp-grow-image-lengths fn-hp-grow-image-vi pcki-resident-vi pgs-x-grow-image)))))

(defthm pcki-floor-lt
  (implies (and (natp q) (natp m) (< q (* 2048 m))) (< (floor q 2048) m))
  :hints (("Goal" :in-theory (enable floor))))

(defthm pcki-res
  (implies (and (pcki-img pw pgs-mem) (natp npn) (<= hi (* 2048 (- npn 8))))
           (pcks-res lo hi (pgs-x-grow-image npn pgs-mem)))
  :hints (("Goal" :induct (pcks-res lo hi (pgs-x-grow-image npn pgs-mem))
           :in-theory (disable pcki-writable pgs-x-grow-image pcki-floor-lt))
          ("Subgoal *1/2" :use ((:instance pcki-writable (q lo))
                                (:instance pcki-floor-lt (q lo) (m (- npn 8))))
           :expand ((pcks-res lo hi (pgs-x-grow-image npn pgs-mem))))))

; -----------------------------------------------------------------------------
; The dirty pages of the grown image are the model's dirty set.

(defthm pcki-arith2
  (implies (and (natp cnt) (natp wl) (< 0 wl))
           (let* ((q (floor cnt 2048))
                  (lt (- cnt (* 2048 q)))
                  (n (floor (+ lt wl 2047) 2048)))
             (and (natp q) (natp n) (natp lt)
                  (<= (* 2048 q) cnt)
                  (<= cnt (* 2048 (+ q n)))
                  (equal (+ q n) (floor (+ cnt wl 2047) 2048))
                  (<= (+ cnt wl) (* 2048 (+ q n))))))
  :hints (("Goal" :use ((:instance pcks-ceil-bound (x (+ (- cnt (* 2048 (floor cnt 2048))) wl)))
                        (:instance pcks-floor-plus-multiple (y (+ (- cnt (* 2048 (floor cnt 2048))) wl 2047)) (k (floor cnt 2048)))
                        (:instance pcki-floor-lt))
           :in-theory (disable pcks-ceil-bound pcks-floor-plus-multiple pcki-floor-lt))))

(defthm pcki-dirty-iota
  (implies (and (pcki-img pw pgs-mem) (natp q) (natp n) (natp npn)
                (<= (* 2048 q) (len pw)) (<= (len pw) (* 2048 (+ q n))) (<= (+ 8 q n) npn))
           (equal (pgs-x-abs-dirty (pcks-iota (+ 8 q) n) (pgs-x-grow-image npn pgs-mem))
                  (adt-tp-number (+ 8 q)
                                 (adt-tp-pages (append (nthcdr (* 2048 q) pw)
                                                       (adt-tp-zeros (- (* 2048 n) (- (len pw) (* 2048 q)))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcks-abs-dirty-iota (lp0 (+ 8 q)) (pgs-mem (pgs-x-grow-image npn pgs-mem)))
                 (:instance pcki-slice-words (tt (+ q n)) (pgs-mem (pgs-x-grow-image npn pgs-mem)))
                 (:instance pcki-window-any (tt (+ q n)))
                 (:instance pcki-slice-list (z (- (* 2048 (+ q n)) (len pw)))))
           :in-theory (e/d (pcki-img) (pcks-abs-dirty-iota pcki-slice-words pcki-window-any pcki-slice-list
                                       pgs-x-grow-image pgs-x-words adt-tp-pages adt-tp-zeros nthcdr take adt-tp-number)))))

(defthm pcki-model-shift
  (implies (and (natp cnt) (natp wl) (< 0 wl))
           (equal (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros wl)))
                  (adt-tp-number (+ 8 (floor cnt 2048)) (adt-tp-pages (append tail (adt-tp-zeros wl))))))
  :hints (("Goal" :use ((:instance pcks-dirty-at-open (n (adt-tp-zeros wl)))
                        (:instance pcks-shift-of-number (k 8) (j (floor cnt 2048)) (ps (adt-tp-pages (append tail (adt-tp-zeros wl)))))
                        (:instance pcks-consp-zeros (l wl)))
           :in-theory (disable pcks-dirty-at-open pcks-shift-of-number pcks-consp-zeros adt-tp-dirty-at adt-tp-number adt-tp-pages adt-tp-zeros pck-shift))))

; (pgs-dirty-lpages nil) as a rule of this book: certified inside the owner
; image (owner@books:books/owner), store-records-field's export theory leaves
; pgs-dirty-lpages and its executable counterpart disabled, so the empty-delta
; cases below would keep it unevaluated.
(defthm pcki-dirty-lpages-nil
  (equal (pgs-dirty-lpages nil) nil)
  :hints (("Goal" :in-theory (enable pgs-dirty-lpages))))

(defthm pcki-model-lpages
  (implies (and (natp cnt) (natp wl) (< 0 wl) (true-listp tail) (equal (len tail) (- cnt (* 2048 (floor cnt 2048)))))
           (equal (pgs-dirty-lpages (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros wl))))
                  (pcks-iota (+ 8 (floor cnt 2048)) (floor (+ (- cnt (* 2048 (floor cnt 2048))) wl 2047) 2048))))
  :hints (("Goal" :use (pcki-model-shift
                        (:instance pcks-dirty-lpages-of-number (j (+ 8 (floor cnt 2048))) (ps (adt-tp-pages (append tail (adt-tp-zeros wl)))))
                        (:instance pcks-len-pages-of-tail-words (w (adt-tp-zeros wl)))
                        (:instance pcks-consp-zeros (l wl)))
           :in-theory (disable pcki-model-shift pcks-dirty-lpages-of-number pcks-len-pages-of-tail-words pcks-consp-zeros
                               adt-tp-dirty-at adt-tp-number adt-tp-pages adt-tp-zeros pck-shift pgs-dirty-lpages))))

(defthm pcki-dirty-pos
  (implies (and (pcki-img pw pgs-mem) (natp wl) (< 0 wl) (natp npn)
                (<= (+ 8 (floor (+ (len pw) wl 2047) 2048)) npn))
           (let* ((cnt (len pw))
                  (tail (nthcdr (* 2048 (floor cnt 2048)) pw))
                  (d (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros wl)))))
             (equal (pgs-x-abs-dirty (pgs-dirty-lpages d) (pgs-x-grow-image npn pgs-mem)) d)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcki-arith2 (cnt (len pw)))
                 (:instance pcki-model-shift (cnt (len pw)) (tail (nthcdr (* 2048 (floor (len pw) 2048)) pw)))
                 (:instance pcki-model-lpages (cnt (len pw)) (tail (nthcdr (* 2048 (floor (len pw) 2048)) pw)))
                 (:instance pcks-len-tail (k (floor (len pw) 2048)))
                 (:instance pcki-dirty-iota (q (floor (len pw) 2048)) (n (floor (+ (- (len pw) (* 2048 (floor (len pw) 2048))) wl 2047) 2048)))
                 (:instance pcki-pages-of-zero-padded (tail (nthcdr (* 2048 (floor (len pw) 2048)) pw))))
           :in-theory (e/d (pcki-img) (pcki-arith2 pcki-model-shift pcki-model-lpages pcks-len-tail pcki-dirty-iota pcki-pages-of-zero-padded
                                       pgs-x-grow-image pgs-x-words adt-tp-pages adt-tp-zeros adt-tp-dirty-at pck-shift nthcdr take adt-tp-number pgs-dirty-lpages pgs-x-abs-dirty)))))

(defthm pcki-hi-bound
  (implies (and (natp cnt) (natp wl) (natp npn) (<= (+ 8 (floor (+ cnt wl 2047) 2048)) npn))
           (<= (+ cnt wl) (* 2048 (- npn 8))))
  :hints (("Goal" :use ((:instance pcks-ceil-bound (x (+ cnt wl)))) :in-theory (disable pcks-ceil-bound))))

(defthm pcki-prestate-res
  (implies (and (pcki-img pw pgs-mem) (natp wl) (natp npn)
                (<= (+ 8 (floor (+ (len pw) wl 2047) 2048)) npn))
           (pcks-res (len pw) (+ (len pw) wl) (pgs-x-grow-image npn pgs-mem)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcki-hi-bound (cnt (len pw)))
                 (:instance pcki-res (lo (len pw)) (hi (+ (len pw) wl))))
           :in-theory (union-theories (theory 'minimal-theory) '((:type-prescription len) (:compound-recognizer natp-compound-recognizer))))))

(defthm pcki-prestate-dirty
  (implies (and (pcki-img pw pgs-mem) (natp wl) (natp npn)
                (<= (+ 8 (floor (+ (len pw) wl 2047) 2048)) npn))
           (let* ((cnt (len pw))
                  (tail (nthcdr (* 2048 (floor cnt 2048)) pw))
                  (d (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros wl)))))
             (equal (pgs-x-abs-dirty (pgs-dirty-lpages d) (pgs-x-grow-image npn pgs-mem)) d)))
  :hints (("Goal" :do-not-induct t :cases ((< 0 wl))
           :in-theory (disable pcki-dirty-pos pgs-x-grow-image adt-tp-dirty-at pck-shift))
          ("Subgoal 2" :in-theory (e/d (pcks-dirty-at-nil) (pcki-dirty-pos pgs-x-grow-image adt-tp-dirty-at pck-shift)))
          ("Subgoal 1" :use (pcki-dirty-pos) :in-theory (disable pcki-dirty-pos pgs-x-grow-image adt-tp-dirty-at pck-shift))))

(defthm fn-pck-x-prestate
  (implies (and (pcki-img pw pgs-mem) (natp wl) (natp npn)
                (<= (+ 8 (floor (+ (len pw) wl 2047) 2048)) npn))
           (let* ((mem2 (pgs-x-grow-image npn pgs-mem))
                  (cnt (len pw))
                  (tail (nthcdr (* 2048 (floor cnt 2048)) pw))
                  (d (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros wl)))))
             (and (pcks-res cnt (+ cnt wl) mem2)
                  (equal (pgs-x-abs-dirty (pgs-dirty-lpages d) mem2) d))))
  :hints (("Goal" :use (pcki-prestate-res pcki-prestate-dirty)
           :in-theory (theory 'minimal-theory))))

; -----------------------------------------------------------------------------
; Staging keeps the image's shape: the array lengths and every page's flag.
; Reading the flags as a list (`pcki-vis') lets the frame be one equality.

(defun pcki-vis (n pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (zp n) nil (cons (pgs-vi (1- n) pgs-mem) (pcki-vis (1- n) pgs-mem))))

(defun pcki-shape (pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (list (pgs-w-length pgs-mem) (pgs-d-length pgs-mem) (pgs-v-length pgs-mem)
        (pcki-vis (pgs-v-length pgs-mem) pgs-mem)))

(defthm pcki-write-nonok
  (implies (not (equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           (equal (mv-nth 1 (pgs-x-write lp off v pgs-mem)) pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-write))))

(defthm pcki-vi-of-write
  (implies (and (natp lp) (natp off) (natp j))
           (equal (pgs-vi j (mv-nth 1 (pgs-x-write lp off v pgs-mem))) (pgs-vi j pgs-mem)))
  :hints (("Goal" :cases ((equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           :in-theory (disable pgs-x-write))
          ("Subgoal 2" :use pcki-write-nonok :in-theory (disable pcki-write-nonok pgs-x-write))
          ("Subgoal 1" :use ((:instance pgs-x-write-facts (a 0) (j j)))
           :in-theory (disable pgs-x-write-facts pgs-x-write))))

(defthm pcki-lengths-of-write
  (implies (and (natp lp) (natp off))
           (and (equal (pgs-w-length (mv-nth 1 (pgs-x-write lp off v pgs-mem))) (pgs-w-length pgs-mem))
                (equal (pgs-d-length (mv-nth 1 (pgs-x-write lp off v pgs-mem))) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (mv-nth 1 (pgs-x-write lp off v pgs-mem))) (pgs-v-length pgs-mem))))
  :hints (("Goal" :cases ((equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           :in-theory (disable pgs-x-write))
          ("Subgoal 2" :use pcki-write-nonok :in-theory (disable pcki-write-nonok pgs-x-write))
          ("Subgoal 1" :use ((:instance pgs-x-write-facts (a 0) (j 0)))
           :in-theory (disable pgs-x-write-facts pgs-x-write))))

(defthm pcki-vis-of-write
  (implies (and (natp lp) (natp off))
           (equal (pcki-vis n (mv-nth 1 (pgs-x-write lp off v pgs-mem))) (pcki-vis n pgs-mem)))
  :hints (("Goal" :induct (pcki-vis n pgs-mem) :in-theory (disable pgs-x-write))))

(defthm pcki-shape-of-write
  (implies (and (natp lp) (natp off))
           (equal (pcki-shape (mv-nth 1 (pgs-x-write lp off v pgs-mem))) (pcki-shape pgs-mem)))
  :hints (("Goal" :in-theory (disable pgs-x-write pcki-vis))))

(in-theory (disable pcki-shape pcki-vis pcki-write-nonok pcki-vi-of-write pcki-lengths-of-write pcki-vis-of-write))

(defthm pcki-shape-of-wr
  (implies (natp q)
           (equal (pcki-shape (mv-nth 1 (pcks-wr q v pgs-mem))) (pcki-shape pgs-mem)))
  :hints (("Goal" :expand ((pcks-wr q v pgs-mem))
           :use ((:instance pcki-shape-of-write (lp (+ 8 (floor q 2048))) (off (mod q 2048))))
           :in-theory (disable pcki-shape-of-write pgs-x-write))))

(defthm pcki-shape-of-put-row
  (implies (and (natp j) (natp nw) (natp p))
           (equal (pcki-shape (mv-nth 1 (fn-pck-x-put-row j nw p fn-octets pgs-mem))) (pcki-shape pgs-mem)))
  :hints (("Goal" :induct (pcks-put-ind j nw p fn-octets pgs-mem)
           :in-theory (union-theories '(pcks-put-row-open pcks-put-row-done (:induction pcks-put-ind) pcki-shape-of-wr)
                                      (disable fn-pck-x-put-row pcks-wr pcki-shape pgs-x-write)))))

(defthm pcki-shape-of-stage
  (implies (natp p)
           (equal (pcki-shape (mv-nth 2 (fn-pck-x-stage-rows rows p fn-arena fn-octets pgs-mem))) (pcki-shape pgs-mem)))
  :hints (("Goal" :induct (pcks-stage-ind rows p fn-arena fn-octets pgs-mem)
           :in-theory (union-theories '(pcks-stage-open pcks-stage-done (:induction pcks-stage-ind) pcki-shape-of-put-row)
                                      (disable fn-pck-x-stage-rows fn-pck-x-put-row fn-pck-x-encode-row fn-pck-x-row-words pcki-shape)))))

(defthm pcki-vis-vi
  (implies (and (equal (pcki-vis n a) (pcki-vis n b)) (natp n) (natp j) (< j n))
           (equal (pgs-vi j a) (pgs-vi j b)))
  :hints (("Goal" :induct (pcki-vis n a) :in-theory (enable pcki-vis))))

(defthm pcki-shape-vi
  (implies (and (equal (pcki-shape a) (pcki-shape b)) (natp j) (< j (pgs-v-length a)))
           (equal (pgs-vi j a) (pgs-vi j b)))
  :hints (("Goal" :use ((:instance pcki-vis-vi (n (pgs-v-length a))))
           :in-theory (e/d (pcki-shape) (pcki-vis-vi)))))

(defthm pcki-shape-resident
  (implies (equal (pcki-shape a) (pcki-shape b))
           (equal (pcki-resident lo hi a) (pcki-resident lo hi b)))
  :hints (("Goal" :induct (pcki-resident lo hi a)
           :in-theory (e/d (pcki-resident pcki-shape) (pcki-vis-vi)))
          (and stable-under-simplificationp
               '(:use ((:instance pcki-shape-vi (j lo)))
                 :in-theory (e/d (pcki-resident pcki-shape) (pcki-vis-vi pcki-shape-vi))))))

(defthm pcki-shape-img
  (implies (equal (pcki-shape a) (pcki-shape b))
           (and (equal (pgs-w-length a) (pgs-w-length b))
                (equal (pgs-d-length a) (pgs-d-length b))
                (equal (pgs-v-length a) (pgs-v-length b))))
  :hints (("Goal" :in-theory (enable pcki-shape))))

; -----------------------------------------------------------------------------
; `pgs-x-commit-durable' marks pages clean and verified: lengths and words stay,
; and a resident page stays resident.

(defun pcki-fw (m) (nth *pgs-wi* m))
(defun pcki-fd (m) (nth *pgs-di* m))
(defun pcki-fv (m) (nth *pgs-vi* m))

(defthm pcki-fields-of-update-d
  (and (equal (pcki-fv (update-pgs-di i v m)) (pcki-fv m))
       (equal (pcki-fw (update-pgs-di i v m)) (pcki-fw m))
       (implies (< (nfix i) (len (pcki-fd m)))
                (equal (len (pcki-fd (update-pgs-di i v m))) (len (pcki-fd m)))))
  :hints (("Goal" :in-theory (enable update-pgs-di pcki-fv pcki-fw pcki-fd))))

(defthm pcki-fields-of-update-v
  (and (equal (pcki-fd (update-pgs-vi i v m)) (pcki-fd m))
       (equal (pcki-fw (update-pgs-vi i v m)) (pcki-fw m))
       (implies (< (nfix i) (len (pcki-fv m)))
                (equal (len (pcki-fv (update-pgs-vi i v m))) (len (pcki-fv m))))
       (implies (and (natp q) (natp i) (< i (len (pcki-fv m))))
                (equal (nth q (pcki-fv (update-pgs-vi i v m)))
                       (if (equal q i) v (nth q (pcki-fv m))))))
  :hints (("Goal" :in-theory (enable update-pgs-vi pcki-fv pcki-fw pcki-fd))))

(defthm pcki-lengths-are-fields
  (and (equal (pgs-d-length m) (len (pcki-fd m)))
       (equal (pgs-w-length m) (len (pcki-fw m)))
       (equal (pgs-v-length m) (len (pcki-fv m))))
  :hints (("Goal" :in-theory (enable pgs-d-length pgs-w-length pgs-v-length pcki-fd pcki-fv pcki-fw))))

(in-theory (disable pcki-fw pcki-fd pcki-fv))

(defun pcki-dstep (l pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (let* ((pgs-mem (if (< l (pgs-d-length pgs-mem)) (update-pgs-di l 0 pgs-mem) pgs-mem))
         (pgs-mem (if (< l (pgs-v-length pgs-mem)) (update-pgs-vi l 2 pgs-mem) pgs-mem)))
    pgs-mem))

(defthm pcki-durable-cons
  (implies (consp lpages)
           (equal (pgs-x-commit-durable lpages pgs-mem)
                  (pgs-x-commit-durable (cdr lpages) (pcki-dstep (car lpages) pgs-mem))))
  :hints (("Goal" :expand ((pgs-x-commit-durable lpages pgs-mem)) :in-theory (enable pcki-dstep))))

(defthm pcki-dstep-fields
  (implies (natp l)
           (and (equal (pcki-fw (pcki-dstep l m)) (pcki-fw m))
                (equal (len (pcki-fd (pcki-dstep l m))) (len (pcki-fd m)))
                (equal (len (pcki-fv (pcki-dstep l m))) (len (pcki-fv m)))
                (implies (and (natp q) (equal (nth q (pcki-fv m)) 2))
                         (equal (nth q (pcki-fv (pcki-dstep l m))) 2))))
  :hints (("Goal" :in-theory (e/d (pcki-dstep) (update-pgs-di update-pgs-vi))
           :do-not-induct t
           :cases ((< l (len (pcki-fd m))) ))
          ("Subgoal 2" :cases ((< l (len (pcki-fv m)))))))

(defun pcki-dind (lpages pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom lpages)
      pgs-mem
    (let ((pgs-mem (pcki-dstep (car lpages) pgs-mem)))
      (pcki-dind (cdr lpages) pgs-mem))))

(defthm pcki-durable-fields
  (implies (nat-listp lpages)
           (and (equal (pcki-fw (pgs-x-commit-durable lpages m)) (pcki-fw m))
                (equal (len (pcki-fd (pgs-x-commit-durable lpages m))) (len (pcki-fd m)))
                (equal (len (pcki-fv (pgs-x-commit-durable lpages m))) (len (pcki-fv m)))
                (implies (and (natp q) (equal (nth q (pcki-fv m)) 2))
                         (equal (nth q (pcki-fv (pgs-x-commit-durable lpages m))) 2))))
  :hints (("Goal" :induct (pcki-dind lpages m)
           :in-theory (e/d (pgs-x-commit-durable) (pcki-durable-cons pcki-dstep-fields pcki-dstep)))
          (and stable-under-simplificationp
               '(:use ((:instance pcki-durable-cons (pgs-mem m)) (:instance pcki-dstep-fields (l (car lpages))))
                 :in-theory (disable pcki-durable-cons pcki-dstep-fields pcki-dstep pgs-x-commit-durable)))))

(defthm pcki-wi-is-fw
  (equal (pgs-wi j m) (nth j (pcki-fw m)))
  :hints (("Goal" :in-theory (enable pgs-wi pcki-fw))))

(defthm pcki-vi-is-fv
  (equal (pgs-vi j m) (nth j (pcki-fv m)))
  :hints (("Goal" :in-theory (enable pgs-vi pcki-fv))))

(defthm pcki-durable-wi
  (implies (nat-listp lpages)
           (equal (pgs-wi j (pgs-x-commit-durable lpages m)) (pgs-wi j m)))
  :hints (("Goal" :use pcki-durable-fields :in-theory (disable pcki-durable-fields pgs-x-commit-durable))))

(defthm pcki-durable-words
  (implies (and (nat-listp lpages) (natp k))
           (equal (pgs-x-words 0 a k (pgs-x-commit-durable lpages pgs-mem)) (pgs-x-words 0 a k pgs-mem)))
  :hints (("Goal" :induct (pcks-ind a k)
           :in-theory (e/d (pcks-words-step pcks-words-zero) (pgs-x-commit-durable)))))

(defthm pcki-durable-resident
  (implies (and (nat-listp lpages) (pcki-resident lo hi m))
           (pcki-resident lo hi (pgs-x-commit-durable lpages m)))
  :hints (("Goal" :induct (pcki-resident lo hi m)
           :in-theory (e/d (pcki-resident) (pgs-x-commit-durable pcki-durable-fields)))
          (and stable-under-simplificationp
               '(:use ((:instance pcki-durable-fields (q lo)))
                 :in-theory (e/d (pcki-resident pcki-vi-is-fv pcki-lengths-are-fields)
                                 (pgs-x-commit-durable pcki-durable-fields))))))

(defthm pcki-img-of-durable
  (implies (and (pcki-img pw pgs-mem) (nat-listp lpages))
           (pcki-img pw (pgs-x-commit-durable lpages pgs-mem)))
  :hints (("Goal" :use ((:instance pcki-durable-fields (m pgs-mem))
                        (:instance pcki-durable-resident (lo 8) (hi (pgs-v-length pgs-mem)) (m pgs-mem))
                        (:instance pcki-durable-words (a 16384) (k (* 2048 (- (pgs-v-length pgs-mem) 8)))))
           :in-theory (e/d (pcki-img pcki-lengths-are-fields)
                           (pcki-durable-fields pcki-durable-resident pcki-durable-words pgs-x-commit-durable pgs-x-words)))))

; -----------------------------------------------------------------------------
; The invariant survives growth, staging and the durable marking.

(defthm pcki-resident-of-grown
  (implies (and (pcki-img pw pgs-mem) (natp npn) (< (pgs-v-length pgs-mem) npn)
                (natp lo) (<= 8 lo) (natp hi) (<= hi npn))
           (pcki-resident lo hi (pgs-x-grow-image npn pgs-mem)))
  :hints (("Goal" :induct (pcki-resident lo hi (pgs-x-grow-image npn pgs-mem))
           :in-theory (e/d (pcki-img (:induction pcki-resident)) (pgs-x-grow-image fn-hp-grow-image-vi fn-hp-grow-image-lengths pcki-resident-vi)))
          (and stable-under-simplificationp
               '(:expand ((pcki-resident lo hi (pgs-x-grow-image npn pgs-mem)))
                 :use ((:instance fn-hp-grow-image-vi (q lo))
                       (:instance fn-hp-grow-image-lengths (np (pgs-v-length pgs-mem)))
                       (:instance pcki-resident-vi (lo 8) (hi (pgs-v-length pgs-mem)) (p lo)))
                 :in-theory (e/d (pcki-img) (pgs-x-grow-image fn-hp-grow-image-vi fn-hp-grow-image-lengths pcki-resident-vi))))))

(defthm pcki-img-of-grown
  (implies (and (pcki-img pw pgs-mem) (natp npn) (<= (len pw) (* 2048 (- npn 8))))
           (pcki-img pw (pgs-x-grow-image npn pgs-mem)))
  :hints (("Goal" :do-not-induct t :cases ((< (pgs-v-length pgs-mem) npn)))
          ("Subgoal 2" :use (pcki-grow-same) :in-theory (disable pcki-grow-same pgs-x-grow-image))
          ("Subgoal 1" :use ((:instance fn-hp-grow-image-lengths (np (pgs-v-length pgs-mem)))
                             (:instance pcki-resident-of-grown (lo 8) (hi npn))
                             (:instance pcki-window-any (tt (- npn 8))))
           :in-theory (e/d (pcki-img) (fn-hp-grow-image-lengths pcki-resident-of-grown pcki-window-any pgs-x-grow-image pgs-x-words adt-tp-zeros)))))

(defthm pcki-true-listp-wlist
  (true-listp (pcks-wlist rows fn-arena))
  :hints (("Goal" :in-theory (enable pcks-wlist-is-dlo-of-words))))

(defthm pcki-img-of-stage
  (implies (and (pcki-img pw pgs-mem) (pcks-treesp rows fn-arena)
                (pcks-res (len pw) (+ (len pw) (pcks-wlen rows fn-arena)) pgs-mem)
                (<= (+ (len pw) (pcks-wlen rows fn-arena)) (* 2048 (- (pgs-v-length pgs-mem) 8))))
           (let ((m3 (mv-nth 2 (fn-pck-x-stage-rows rows (len pw) fn-arena fn-octets pgs-mem))))
             (and (equal (mv-nth 0 (fn-pck-x-stage-rows rows (len pw) fn-arena fn-octets pgs-mem)) :ok)
                  (pcki-img (append pw (pcks-wlist rows fn-arena)) m3))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcks-stage-rows (p (len pw)) (a 16384) (k (* 2048 (- (pgs-v-length pgs-mem) 8))))
                 (:instance pcki-shape-of-stage (p (len pw)))
                 (:instance pcki-shape-img (a pgs-mem) (b (mv-nth 2 (fn-pck-x-stage-rows rows (len pw) fn-arena fn-octets pgs-mem))))
                 (:instance pcki-shape-resident (lo 8) (hi (pgs-v-length pgs-mem)) (a pgs-mem)
                            (b (mv-nth 2 (fn-pck-x-stage-rows rows (len pw) fn-arena fn-octets pgs-mem))))
                 (:instance pcks-put-over-zeros (a pw) (ws (pcks-wlist rows fn-arena))
                            (r (adt-tp-zeros (- (- (* 2048 (- (pgs-v-length pgs-mem) 8)) (len pw)) (pcks-wlen rows fn-arena)))))
                 (:instance pcki-zeros-append (a (pcks-wlen rows fn-arena))
                            (b (- (- (* 2048 (- (pgs-v-length pgs-mem) 8)) (len pw)) (pcks-wlen rows fn-arena))))
                 (:instance pcks-wlen-is-len-wlist))
           :in-theory (e/d (pcki-img) (pcks-stage-rows pcki-shape-of-stage pcki-shape-img pcki-shape-resident pcks-put-over-zeros
                                       pcki-zeros-append pcks-wlen-is-len-wlist fn-pck-x-stage-rows pcks-res pcks-put
                                       pgs-x-words adt-tp-zeros pcks-wlen pcks-wlist
                                       pcks-wlen-is-len-words pcks-wlist-is-dlo-of-words pcks-len-dlo-list pcks-res-hi)))))

(defthm pcki-nat-listp-iota
  (implies (natp a) (nat-listp (pcks-iota a n)))
  :hints (("Goal" :induct (pcks-iota a n))))

(defthm pcki-lpages-nat
  (implies (and (natp cnt) (natp wl) (true-listp tail) (equal (len tail) (- cnt (* 2048 (floor cnt 2048)))))
           (nat-listp (pgs-dirty-lpages (pck-shift 8 (adt-tp-dirty-at cnt tail (adt-tp-zeros wl))))))
  :hints (("Goal" :cases ((< 0 wl)))
          ("Subgoal 2" :in-theory (e/d (pcks-dirty-at-nil) (adt-tp-dirty-at pck-shift)))
          ("Subgoal 1" :use (pcki-model-lpages) :in-theory (disable pcki-model-lpages adt-tp-dirty-at pck-shift pcks-iota))))

(defthm pcki-grown-vlen
  (implies (and (pcki-img pw pgs-mem) (natp npn))
           (<= npn (pgs-v-length (pgs-x-grow-image npn pgs-mem))))
  :hints (("Goal" :do-not-induct t :cases ((< (pgs-v-length pgs-mem) npn)))
          ("Subgoal 2" :use (pcki-grow-same) :in-theory (disable pcki-grow-same pgs-x-grow-image))
          ("Subgoal 1" :use ((:instance fn-hp-grow-image-lengths (np (pgs-v-length pgs-mem))))
           :in-theory (e/d (pcki-img) (fn-hp-grow-image-lengths pgs-x-grow-image)))))

(defthm pcki-img-true-listp
  (implies (pcki-img pw pgs-mem) (true-listp pw))
  :hints (("Goal" :in-theory (enable pcki-img))))

(defthm pcki-true-listp-nthcdr
  (implies (true-listp x) (true-listp (nthcdr n x))))

(defthm pcki-after-commit-wlist
  (implies (and (pcki-img pw pgs-mem) (natp npn) (pcks-treesp rows fn-arena)
                (<= (+ 8 (floor (+ (len pw) (pcks-wlen rows fn-arena) 2047) 2048)) npn))
           (let* ((mem2 (pgs-x-grow-image npn pgs-mem))
                  (r (fn-pck-x-stage-rows rows (len pw) fn-arena fn-octets mem2))
                  (tail (nthcdr (* 2048 (floor (len pw) 2048)) pw))
                  (lp (pgs-dirty-lpages (pck-shift 8 (adt-tp-dirty-at (len pw) tail (adt-tp-zeros (pcks-wlen rows fn-arena)))))))
             (and (equal (mv-nth 0 r) :ok)
                  (pcki-img (append pw (pcks-wlist rows fn-arena))
                            (pgs-x-commit-durable lp (mv-nth 2 r))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcki-hi-bound (cnt (len pw)) (wl (pcks-wlen rows fn-arena)))
                 (:instance pcki-img-of-grown)
                 (:instance pcki-prestate-res (wl (pcks-wlen rows fn-arena)))
                 (:instance pcki-grown-vlen)
                 (:instance pcki-img-of-stage (pgs-mem (pgs-x-grow-image npn pgs-mem)))
                 (:instance pcki-lpages-nat (cnt (len pw)) (wl (pcks-wlen rows fn-arena))
                            (tail (nthcdr (* 2048 (floor (len pw) 2048)) pw)))
                 (:instance pcks-len-tail (k (floor (len pw) 2048)))
                 (:instance pcki-img-of-durable (pw (append pw (pcks-wlist rows fn-arena)))
                            (pgs-mem (mv-nth 2 (fn-pck-x-stage-rows rows (len pw) fn-arena fn-octets (pgs-x-grow-image npn pgs-mem))))
                            (lpages (pgs-dirty-lpages (pck-shift 8 (adt-tp-dirty-at (len pw) (nthcdr (* 2048 (floor (len pw) 2048)) pw)
                                                                                    (adt-tp-zeros (pcks-wlen rows fn-arena))))))))
           :in-theory (disable pcki-hi-bound pcki-img-of-grown pcki-prestate-res pcki-grown-vlen pcki-img-of-stage pcki-lpages-nat
                               pcks-len-tail pcki-img-of-durable pgs-x-grow-image pgs-x-commit-durable fn-pck-x-stage-rows
                               pcks-wlen pcks-wlist adt-tp-dirty-at adt-tp-zeros pck-shift pgs-dirty-lpages pcki-img
                               pcks-wlen-is-len-words pcks-wlist-is-dlo-of-words pcks-len-dlo-list pcks-res-hi pcks-res))))

(defthm pcki-wlist-is-words
  (implies (and (fn-pck-sccb-listp (fn-rows-wire-of rows fn-arena))
                (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows (fn-rows-wire-of rows fn-arena))))
           (equal (pcks-wlist rows fn-arena)
                  (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows (fn-rows-wire-of rows fn-arena)))))
  :hints (("Goal" :do-not-induct t
           :use (pcks-wlist-is-dlo-of-words
                        (:instance pck-rows-ap (recs (fn-rows-wire-of rows fn-arena)))
                        (:instance pcks-dlo-list-id (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows (fn-rows-wire-of rows fn-arena)))))
                        (:instance adt-tp-u64s-seq-words (s *fn-pck-row-schema*) (a (fn-pck-rows (fn-rows-wire-of rows fn-arena)))))
           :in-theory (disable pcks-wlist-is-dlo-of-words pcks-dlo-list-id adt-tp-u64s-seq-words pcks-wlist adt-tp-seq-words pck-rows-ap))))

(defthm fn-pck-x-image-after-commit
  ; The loop: from the image of PW, growing it, staging the delta rows and
  ; marking the tape's dirty pages durable leave the image of PW ++ the
  ; delta's words.  The staging answers :ok.
  (let* ((delta (fn-rows-wire-of rows fn-arena))
         (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows delta)))
         (mem2 (pgs-x-grow-image npn pgs-mem))
         (r (fn-pck-x-stage-rows rows (len pw) fn-arena fn-octets mem2))
         (tail (nthcdr (* *pgs-page-words* (floor (len pw) *pgs-page-words*)) pw))
         (lp (pgs-dirty-lpages (pck-shift 8 (adt-tp-dirty-at (len pw) tail (adt-tp-zeros (len w)))))))
    (implies (and (pcki-img pw pgs-mem) (natp npn)
                  (fn-pck-sccb-listp delta)
                  (adt-tp-seq-lens-ok *fn-pck-row-schema* (fn-pck-rows delta))
                  (<= (+ 8 (floor (+ (len pw) (len w) 2047) 2048)) npn))
             (and (equal (mv-nth 0 r) :ok)
                  (pcki-img (append pw w) (pgs-x-commit-durable lp (mv-nth 2 r))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcki-after-commit-wlist))
           :in-theory (union-theories '(pcks-wlen-is-len-words pcki-wlist-is-words pcks-treesp-of-sccb-listp)
                                      (theory 'minimal-theory)))))
