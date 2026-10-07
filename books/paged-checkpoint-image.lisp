; fn: the staged keystone's pre-state is the previous commit's image (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM-20261006.md section 3.3, phase 2c).
;
; STATEMENTS (written first; the proofs follow in this file).
;
; `fn-pck-x-stage-is-the-dirty' (paged-checkpoint-stage.lisp) assumes a mem0
; whose dirty pages hold the prefix tail then zeros, resident.  Here that state
; is derived from the image the previous commit left.
;
;   (pcki-img PW pgs-mem)   the tape invariant: pages 8..V-1 are all resident
;       (vi = 2); the arrays have the image's lengths (d = V, w = 2048 V); the
;       tape window (words 16384 .. 2048 V) is PW followed by zeros.
;
;   fn-pck-x-prestate   (pcki-img PW mem), the image grown to NPN pages
;       (`pgs-x-grow-image', zero pages, resident) with NPN covering
;       the last tape page of PW ++ a WL-word delta:
;         (pcks-res CNT (+ CNT WL) mem2)   -- every delta position is writable
;         (pgs-x-abs-dirty LP mem2) = (pck-shift 8 (adt-tp-dirty-at CNT TAIL zeros(WL)))
;       with CNT = (len PW), TAIL = PW's last partial page, LP the pages of that
;       set.  These are exactly premises (1) and (2) of the keystone.  The tail
;       page needs no separate read: the invariant holds it resident.
;
;   fn-pck-x-image-after-commit   the invariant is the loop's: from
;       (pcki-img PW mem), growing, staging the delta rows and
;       `pgs-x-commit-durable' on the tape's dirty pages leave
;       (pcki-img PW' mem4) with PW' the words of (prefix ++ delta); the
;       staging answers :ok.  So a store opened (every tape page filled and
;       verified) establishes the invariant once, and each publication keeps it.
;
; Not here (owed, PCK-STAGE-NEED-PAGE): a tail page that is not resident
; (lazy open) answers (:need-page LP); that path fills the page and retries.

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
