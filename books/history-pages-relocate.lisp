;; fn: the history's growth step over the page store's stobj, as the host
;; calls it (lane arena-store-4, 2026-09-28).  Prefix fn-hp-.
(in-package "ACL2")
(include-book "history-pages-grow")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound adt-nth-0
                          adt-nth-1+ fn-hp-lens-col-sizes fn-hp-okp fn-scc-octet-listp-facts)))

; -----------------------------------------------------------------------------
; L. The growth step's word loops over the stobj: a copy, a zeroing, a
;    dirty marking.  Each costs one step per word (or page) it names.

(local
 (defthm fn-hp-floor-2048-below
   (implies (and (natp x) (natp d) (< x (* 2048 d))) (< (floor x 2048) d))
   :hints (("Goal" :in-theory (enable floor)))
   :rule-classes :linear))

(defun fn-hp-x-copy (src dst k pgs-mem)
  ; words DST .. DST+K-1 := words SRC .. SRC+K-1, each written page dirty
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp src) (natp dst) (natp k)
                              (<= (+ src k) (pgs-w-length pgs-mem)) (<= (+ dst k) (pgs-w-length pgs-mem))
                              (<= (+ dst k) (* 2048 (pgs-d-length pgs-mem))))))
  (if (zp k)
      pgs-mem
    (let* ((pgs-mem (update-pgs-wi dst (pgs-wi src pgs-mem) pgs-mem))
           (pgs-mem (update-pgs-di (floor dst 2048) 1 pgs-mem)))
      (fn-hp-x-copy (+ 1 src) (+ 1 dst) (1- k) pgs-mem))))

(defun fn-hp-x-zero (j k pgs-mem)
  ; words J .. J+K-1 := 0, each written page dirty
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp j) (natp k) (<= (+ j k) (pgs-w-length pgs-mem))
                              (<= (+ j k) (* 2048 (pgs-d-length pgs-mem))))))
  (if (zp k)
      pgs-mem
    (let* ((pgs-mem (update-pgs-wi j 0 pgs-mem))
           (pgs-mem (update-pgs-di (floor j 2048) 1 pgs-mem)))
      (fn-hp-x-zero (+ 1 j) (1- k) pgs-mem))))

(defun fn-hp-x-mark (i k pgs-mem)
  ; pages I .. K-1 dirty
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp k) (<= k (pgs-d-length pgs-mem)))
                  :measure (nfix (- (nfix k) (nfix i)))))
  (if (mbe :logic (zp (- (nfix k) (nfix i))) :exec (<= k i))
      pgs-mem
    (let ((pgs-mem (update-pgs-di i 1 pgs-mem)))
      (fn-hp-x-mark (+ 1 (nfix i)) k pgs-mem))))
(local
 (defthm fn-hp-x-words-of-update-w
   (implies (and (natp i) (natp j) (or (< j i) (<= (+ i (nfix k)) j)))
            (equal (fn-hp-x-words i k (update-pgs-wi j v pgs-mem)) (fn-hp-x-words i k pgs-mem)))
   :hints (("Goal" :induct (fn-hp-x-words i k pgs-mem) :in-theory (enable pgs-wi update-pgs-wi)))))

(local
 (defthm fn-hp-x-words-of-update-d
   (equal (fn-hp-x-words i k (update-pgs-di j v pgs-mem)) (fn-hp-x-words i k pgs-mem))
   :hints (("Goal" :induct (fn-hp-x-words i k pgs-mem) :in-theory (enable pgs-wi update-pgs-di)))))

(defthm fn-hp-x-copy-is-put
  (implies (and (natp src) (natp dst) (<= (+ src (nfix k)) dst))
           (equal (fn-hp-x-copy src dst k pgs-mem)
                  (fn-hp-x-put dst (fn-hp-x-words src k pgs-mem) pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-copy src dst k pgs-mem) :in-theory (disable floor fn-hp-x-words-is-take))
          ("Subgoal *1/2" :expand ((fn-hp-x-words src k pgs-mem) (:free (ws) (fn-hp-x-put dst ws pgs-mem))))))

(defthm fn-hp-x-zero-is-put
  (implies (natp j)
           (equal (fn-hp-x-zero j k pgs-mem) (fn-hp-x-put j (adt-zeros k) pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-zero j k pgs-mem) :in-theory (enable adt-zeros))))

(in-theory (disable fn-hp-x-copy-is-put fn-hp-x-zero-is-put))

(defthm fn-hp-x-copy-frame
  (implies (and (natp dst) (<= (+ dst (nfix k)) (pgs-w-length pgs-mem)) (<= (+ dst (nfix k)) (* 2048 (pgs-d-length pgs-mem))))
           (and (equal (pgs-w-length (fn-hp-x-copy src dst k pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-d-length (fn-hp-x-copy src dst k pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (fn-hp-x-copy src dst k pgs-mem)) (pgs-v-length pgs-mem))
                (equal (nth *pgs-vi* (fn-hp-x-copy src dst k pgs-mem)) (nth *pgs-vi* pgs-mem))))
  :hints (("Goal" :induct (fn-hp-x-copy src dst k pgs-mem))))

(defthm fn-hp-x-zero-frame
  (implies (and (natp j) (<= (+ j (nfix k)) (pgs-w-length pgs-mem)) (<= (+ j (nfix k)) (* 2048 (pgs-d-length pgs-mem))))
           (and (equal (pgs-w-length (fn-hp-x-zero j k pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-d-length (fn-hp-x-zero j k pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (fn-hp-x-zero j k pgs-mem)) (pgs-v-length pgs-mem))
                (equal (nth *pgs-vi* (fn-hp-x-zero j k pgs-mem)) (nth *pgs-vi* pgs-mem))))
  :hints (("Goal" :induct (fn-hp-x-zero j k pgs-mem))))

(defthm fn-hp-x-mark-frame
  (and (equal (nth *pgs-wi* (fn-hp-x-mark i k pgs-mem)) (nth *pgs-wi* pgs-mem))
       (equal (nth *pgs-vi* (fn-hp-x-mark i k pgs-mem)) (nth *pgs-vi* pgs-mem))
       (equal (nth *pgs-tvi* (fn-hp-x-mark i k pgs-mem)) (nth *pgs-tvi* pgs-mem))
       (equal (pgs-v-length (fn-hp-x-mark i k pgs-mem)) (pgs-v-length pgs-mem))
       (equal (pgs-w-length (fn-hp-x-mark i k pgs-mem)) (pgs-w-length pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-mark i k pgs-mem)
           :in-theory (enable update-pgs-di pgs-v-length pgs-w-length))))

(defthm fn-hp-x-mark-dirty
  (implies (and (natp i) (natp p)
                (equal (nth p (nth *pgs-di* (fn-hp-x-mark i k pgs-mem))) 1)
                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
           (and (<= i p) (< p (nfix k))))
  :hints (("Goal" :induct (fn-hp-x-mark i k pgs-mem) :in-theory (enable update-pgs-di)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; M. The page store's growth, as the relocation sees it.

(local
 (defthm fn-hp-resize-list-grows
   (implies (<= (len l) (nfix n))
            (equal (resize-list l n 0) (append (true-list-fix l) (adt-zeros (- (nfix n) (len l))))))
   :hints (("Goal" :induct (resize-list l n 0) :in-theory (enable adt-zeros)))))

(local
 (defun fn-hp-resize-ind (j l n)
   (if (zp n) (list j l) (fn-hp-resize-ind (1- j) (if (consp l) (cdr l) l) (1- n)))))

(local
 (defthm fn-hp-nth-resize-list
   (implies (natp j)
            (equal (nth j (resize-list l n d))
                   (if (< j (nfix n)) (if (< j (len l)) (nth j l) d) nil)))
   :hints (("Goal" :in-theory (enable nth) :induct (fn-hp-resize-ind j l n)))))

(defthm fn-hp-set-flags-frame
  (and (equal (nth *pgs-wi* (pgs-x-set-flags i k v pgs-mem)) (nth *pgs-wi* pgs-mem))
       (equal (nth *pgs-di* (pgs-x-set-flags i k v pgs-mem)) (nth *pgs-di* pgs-mem)))
  :hints (("Goal" :induct (pgs-x-set-flags i k v pgs-mem) :in-theory (enable update-pgs-vi))))

(defthm fn-hp-set-flags-length
  (implies (<= (nfix k) (pgs-v-length pgs-mem))
           (equal (pgs-v-length (pgs-x-set-flags i k v pgs-mem)) (pgs-v-length pgs-mem)))
  :hints (("Goal" :induct (pgs-x-set-flags i k v pgs-mem) :in-theory (enable update-pgs-vi pgs-v-length))))

(defthm fn-hp-set-flags-nth
  (implies (and (natp q) (natp i))
           (equal (nth q (nth *pgs-vi* (pgs-x-set-flags i k v pgs-mem)))
                  (if (and (<= i q) (< q (nfix k))) v (nth q (nth *pgs-vi* pgs-mem)))))
  :hints (("Goal" :induct (pgs-x-set-flags i k v pgs-mem) :in-theory (enable update-pgs-vi))))

(defthm fn-hp-set-tflags-frame
  (and (equal (nth *pgs-wi* (pgs-x-set-tflags i k v pgs-mem)) (nth *pgs-wi* pgs-mem))
       (equal (nth *pgs-di* (pgs-x-set-tflags i k v pgs-mem)) (nth *pgs-di* pgs-mem))
       (equal (nth *pgs-vi* (pgs-x-set-tflags i k v pgs-mem)) (nth *pgs-vi* pgs-mem)))
  :hints (("Goal" :induct (pgs-x-set-tflags i k v pgs-mem) :in-theory (enable update-pgs-tvi))))

(local
 (defthm fn-hp-nth-past-len
   (implies (and (natp q) (<= (len l) q)) (equal (nth q l) nil))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-hp-grow-step-lengths
  (and (equal (pgs-w-length (resize-pgs-w k pgs-mem)) (nfix k))
       (equal (pgs-d-length (resize-pgs-w k pgs-mem)) (pgs-d-length pgs-mem))
       (equal (pgs-w-length (resize-pgs-d k pgs-mem)) (pgs-w-length pgs-mem))
       (equal (pgs-d-length (resize-pgs-d k pgs-mem)) (nfix k))
       (equal (pgs-w-length (resize-pgs-v k pgs-mem)) (pgs-w-length pgs-mem))
       (equal (pgs-d-length (resize-pgs-v k pgs-mem)) (pgs-d-length pgs-mem))
       (equal (pgs-w-length (resize-pgs-tv k pgs-mem)) (pgs-w-length pgs-mem))
       (equal (pgs-d-length (resize-pgs-tv k pgs-mem)) (pgs-d-length pgs-mem))
       (equal (pgs-v-length (resize-pgs-tv k pgs-mem)) (pgs-v-length pgs-mem))
       (equal (pgs-w-length (pgs-x-set-flags i k v pgs-mem)) (pgs-w-length pgs-mem))
       (equal (pgs-d-length (pgs-x-set-flags i k v pgs-mem)) (pgs-d-length pgs-mem))
       (equal (pgs-w-length (pgs-x-set-tflags i k v pgs-mem)) (pgs-w-length pgs-mem))
       (equal (pgs-d-length (pgs-x-set-tflags i k v pgs-mem)) (pgs-d-length pgs-mem))
       (equal (pgs-v-length (pgs-x-set-tflags i k v pgs-mem)) (pgs-v-length pgs-mem)))
  :hints (("Goal" :in-theory (e/d (pgs-w-length pgs-d-length pgs-v-length resize-pgs-tv) (pgs-x-set-flags pgs-x-set-tflags))
           :use (fn-hp-set-flags-frame fn-hp-set-tflags-frame))))

(defthm fn-hp-resize-fields
  (and (equal (nth *pgs-wi* (resize-pgs-w k pgs-mem)) (resize-list (nth *pgs-wi* pgs-mem) k 0))
       (equal (nth *pgs-di* (resize-pgs-w k pgs-mem)) (nth *pgs-di* pgs-mem))
       (equal (nth *pgs-vi* (resize-pgs-w k pgs-mem)) (nth *pgs-vi* pgs-mem))
       (equal (nth *pgs-wi* (resize-pgs-d k pgs-mem)) (nth *pgs-wi* pgs-mem))
       (equal (nth *pgs-di* (resize-pgs-d k pgs-mem)) (resize-list (nth *pgs-di* pgs-mem) k 0))
       (equal (nth *pgs-vi* (resize-pgs-d k pgs-mem)) (nth *pgs-vi* pgs-mem))
       (equal (nth *pgs-wi* (resize-pgs-v k pgs-mem)) (nth *pgs-wi* pgs-mem))
       (equal (nth *pgs-di* (resize-pgs-v k pgs-mem)) (nth *pgs-di* pgs-mem))
       (equal (nth *pgs-vi* (resize-pgs-v k pgs-mem)) (resize-list (nth *pgs-vi* pgs-mem) k 0))
       (equal (nth *pgs-wi* (resize-pgs-tv k pgs-mem)) (nth *pgs-wi* pgs-mem))
       (equal (nth *pgs-di* (resize-pgs-tv k pgs-mem)) (nth *pgs-di* pgs-mem))
       (equal (nth *pgs-vi* (resize-pgs-tv k pgs-mem)) (nth *pgs-vi* pgs-mem)))
  :hints (("Goal" :in-theory (enable resize-pgs-w resize-pgs-d resize-pgs-v resize-pgs-tv))))

(local (in-theory (disable pgs-x-set-flags pgs-x-set-tflags pgs-ntables resize-pgs-w resize-pgs-d resize-pgs-v resize-pgs-tv)))

(defthm fn-hp-grow-image-lengths
  (implies (and (natp np) (natp npn) (<= np npn) (equal (pgs-v-length pgs-mem) np))
           (and (equal (pgs-v-length (pgs-x-grow-image npn pgs-mem)) npn)
                (implies (equal (pgs-w-length pgs-mem) (* 2048 np))
                         (equal (pgs-w-length (pgs-x-grow-image npn pgs-mem)) (* 2048 npn)))
                (implies (equal (pgs-d-length pgs-mem) np)
                         (equal (pgs-d-length (pgs-x-grow-image npn pgs-mem)) npn))))
  :hints (("Goal" :in-theory (enable))))

;; The fields through wrappers the prover does not open.
(local (defun fn-hp-fw (m) (nth *pgs-wi* m)))
(local (defun fn-hp-fd (m) (nth *pgs-di* m)))
(local (defun fn-hp-fv (m) (nth *pgs-vi* m)))

(local
 (defthm fn-hp-wrapped-frames
   (and (equal (fn-hp-fw (resize-pgs-w k m)) (resize-list (fn-hp-fw m) k 0))
        (equal (fn-hp-fd (resize-pgs-w k m)) (fn-hp-fd m))
        (equal (fn-hp-fv (resize-pgs-w k m)) (fn-hp-fv m))
        (equal (fn-hp-fw (resize-pgs-d k m)) (fn-hp-fw m))
        (equal (fn-hp-fd (resize-pgs-d k m)) (resize-list (fn-hp-fd m) k 0))
        (equal (fn-hp-fv (resize-pgs-d k m)) (fn-hp-fv m))
        (equal (fn-hp-fw (resize-pgs-v k m)) (fn-hp-fw m))
        (equal (fn-hp-fd (resize-pgs-v k m)) (fn-hp-fd m))
        (equal (fn-hp-fv (resize-pgs-v k m)) (resize-list (fn-hp-fv m) k 0))
        (equal (fn-hp-fw (resize-pgs-tv k m)) (fn-hp-fw m))
        (equal (fn-hp-fd (resize-pgs-tv k m)) (fn-hp-fd m))
        (equal (fn-hp-fv (resize-pgs-tv k m)) (fn-hp-fv m))
        (equal (fn-hp-fw (pgs-x-set-tflags i k v m)) (fn-hp-fw m))
        (equal (fn-hp-fd (pgs-x-set-tflags i k v m)) (fn-hp-fd m))
        (equal (fn-hp-fv (pgs-x-set-tflags i k v m)) (fn-hp-fv m))
        (equal (fn-hp-fw (pgs-x-set-flags i k v m)) (fn-hp-fw m))
        (equal (fn-hp-fd (pgs-x-set-flags i k v m)) (fn-hp-fd m))
        (implies (and (natp q) (natp i))
                 (equal (nth q (fn-hp-fv (pgs-x-set-flags i k v m)))
                        (if (and (<= i q) (< q (nfix k))) v (nth q (fn-hp-fv m))))))
   :hints (("Goal" :in-theory (e/d (fn-hp-fw fn-hp-fd fn-hp-fv) (pgs-x-set-flags pgs-x-set-tflags))
            :use ((:instance fn-hp-resize-fields (pgs-mem m))
                  (:instance fn-hp-set-tflags-frame (pgs-mem m))
                  (:instance fn-hp-set-flags-frame (pgs-mem m))
                  (:instance fn-hp-set-flags-nth (pgs-mem m)))))))

(local
 (defthm fn-hp-len-fv
   (equal (len (fn-hp-fv m)) (pgs-v-length m))
   :hints (("Goal" :in-theory (enable pgs-v-length fn-hp-fv)))))

(local (in-theory (disable fn-hp-fw fn-hp-fd fn-hp-fv)))

(local
 (defthm fn-hp-grow-image-wrapped
   (implies (and (natp npn) (< (pgs-v-length pgs-mem) npn))
            (and (equal (fn-hp-fw (pgs-x-grow-image npn pgs-mem)) (resize-list (fn-hp-fw pgs-mem) (* 2048 npn) 0))
                 (equal (fn-hp-fd (pgs-x-grow-image npn pgs-mem)) (resize-list (fn-hp-fd pgs-mem) npn 0))
                 (implies (natp q)
                          (equal (nth q (fn-hp-fv (pgs-x-grow-image npn pgs-mem)))
                                 (cond ((< q (pgs-v-length pgs-mem)) (nth q (fn-hp-fv pgs-mem))) ((< q npn) 2) (t nil))))))
   :hints (("Goal" :in-theory (disable fn-hp-resize-list-grows)))))
(defthm fn-hp-grow-image-words
  (implies (and (natp npn) (< (pgs-v-length pgs-mem) npn))
           (and (equal (nth *pgs-wi* (pgs-x-grow-image npn pgs-mem))
                       (resize-list (nth *pgs-wi* pgs-mem) (* 2048 npn) 0))
                (equal (nth *pgs-di* (pgs-x-grow-image npn pgs-mem))
                       (resize-list (nth *pgs-di* pgs-mem) npn 0))))
  :hints (("Goal" :use ((:instance fn-hp-grow-image-wrapped (q 0)))
           :in-theory (e/d (fn-hp-fw fn-hp-fd) (pgs-x-grow-image fn-hp-grow-image-wrapped fn-hp-resize-list-grows)))))

(defthm fn-hp-grow-image-vi
  (implies (and (natp q) (natp npn) (< (pgs-v-length pgs-mem) npn))
           (equal (pgs-vi q (pgs-x-grow-image npn pgs-mem))
                  (cond ((< q (pgs-v-length pgs-mem)) (pgs-vi q pgs-mem)) ((< q npn) 2) (t nil))))
  :hints (("Goal" :use ((:instance fn-hp-grow-image-wrapped))
           :in-theory (e/d (fn-hp-fv pgs-vi) (pgs-x-grow-image fn-hp-grow-image-wrapped fn-hp-resize-list-grows)))))

(local (in-theory (disable pgs-x-grow-image)))

; The grown store holds the image followed by zero pages.
(local
 (defthm fn-hp-take-nthcdr-append-front
   (implies (and (natp a) (natp n) (<= (+ a n) (len x)))
            (equal (take n (nthcdr a (append x y))) (take n (nthcdr a x))))
   :hints (("Goal" :in-theory (enable take nthcdr) :induct (nthcdr a x)))))

(local
 (defthm fn-hp-nthcdr-tlf
   (equal (nthcdr a (true-list-fix x)) (true-list-fix (nthcdr a x)))
   :hints (("Goal" :in-theory (enable nthcdr true-list-fix) :induct (nthcdr a x)))))

(local
 (defthm fn-hp-take-tlf
   (equal (take n (true-list-fix x)) (take n x))
   :hints (("Goal" :in-theory (enable take true-list-fix) :induct (take n x)))))

(local
 (defthm fn-hp-nthcdr-append-back
   (implies (and (natp a) (<= (len x) a))
            (equal (nthcdr a (append x y)) (nthcdr (- a (len x)) y)))
   :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr a x)))))

(local
 (defthm fn-hp-grown-page
   (implies (and (natp p) (natp npn) (< (pgs-v-length pgs-mem) npn)
                 (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem))))
            (equal (take 2048 (nthcdr (* 2048 p) (nth *pgs-wi* (pgs-x-grow-image npn pgs-mem))))
                   (if (< p (pgs-v-length pgs-mem))
                       (take 2048 (nthcdr (* 2048 p) (nth *pgs-wi* pgs-mem)))
                     (take 2048 (nthcdr (- (* 2048 p) (* 2048 (pgs-v-length pgs-mem)))
                                        (adt-zeros (* 2048 (- npn (pgs-v-length pgs-mem)))))))))
   :hints (("Goal" :cases ((< p (pgs-v-length pgs-mem))) :in-theory (e/d (pgs-w-length) (take nthcdr))))))

(local
 (defthm fn-hp-vhold-past
   (implies (<= (nfix np) (nfix p)) (fn-hp-vhold p np pgs-mem iw))
   :hints (("Goal" :expand ((fn-hp-vhold p np pgs-mem iw))))))

(local
 (defthm fn-hp-vhold-after-grow-p
   (implies (and (fn-hp-vhold p (pgs-v-length pgs-mem) pgs-mem iw) (natp p) (natp npn)
                 (< (pgs-v-length pgs-mem) npn)
                 (equal (pgs-w-length pgs-mem) (* 2048 (pgs-v-length pgs-mem)))
                 (equal (len iw) (* 2048 (pgs-v-length pgs-mem))))
            (fn-hp-vhold p npn (pgs-x-grow-image npn pgs-mem)
                         (append iw (adt-zeros (* 2048 (- npn (pgs-v-length pgs-mem)))))))
   :hints (("Goal" :induct (fn-hp-vhold p npn (pgs-x-grow-image npn pgs-mem)
                                        (append iw (adt-zeros (* 2048 (- npn (pgs-v-length pgs-mem))))))
            :in-theory (disable take nthcdr nth fn-hp-resize-list-grows fn-hp-grow-image-words)
            :expand ((fn-hp-vhold p (pgs-v-length pgs-mem) pgs-mem iw)
                     (fn-hp-vhold p npn (pgs-x-grow-image npn pgs-mem)
                                  (append iw (adt-zeros (* 2048 (- npn (pgs-v-length pgs-mem)))))))))))

; -----------------------------------------------------------------------------
; N. The words the copy reads are the region's padded words.

(local
 (defthm fn-hp-take-split
   (implies (and (natp n) (natp k))
            (equal (take (+ n k) l) (append (take n l) (take k (nthcdr n l)))))
   :hints (("Goal" :in-theory (enable take nthcdr) :induct (take n l)))))

(local
 (defun fn-hp-pages-ind (a m)
   (if (zp m) (list a m) (fn-hp-pages-ind (+ 1 (nfix a)) (1- m)))))

(local
 (defthm fn-hp-ready-range-next
   (implies (and (equal (fn-hp-x-ready-range a hi pgs-mem) :ok) (natp a))
            (equal (fn-hp-x-ready-range (+ 1 a) hi pgs-mem) :ok))
   :hints (("Goal" :expand ((fn-hp-x-ready-range a hi pgs-mem) (fn-hp-x-ready-range (+ 1 a) hi pgs-mem))
            :in-theory (disable fn-hp-x-ready)))))

(defthm fn-hp-store-pages-hold
  ; verified pages A .. A+M-1 of a store holding IW are IW's words there
  (implies (and (fn-hp-vhold 0 np pgs-mem iw) (natp a) (natp m) (<= (+ a m) (nfix np))
                (equal (fn-hp-x-ready-range a (+ a m) pgs-mem) :ok))
           (equal (take (* 2048 m) (nthcdr (* 2048 a) (nth *pgs-wi* pgs-mem)))
                  (take (* 2048 m) (nthcdr (* 2048 a) iw))))
  :hints (("Goal" :induct (fn-hp-pages-ind a m) :in-theory (disable take nthcdr nth fn-hp-x-ready-range fn-hp-vhold))
          ("Subgoal *1/2" :use ((:instance fn-hp-take-split (n 2048) (k (* 2048 (1- m))) (l (nthcdr (* 2048 a) (nth *pgs-wi* pgs-mem))))
                                (:instance fn-hp-take-split (n 2048) (k (* 2048 (1- m))) (l (nthcdr (* 2048 a) iw)))
                                (:instance fn-hp-vi-from-ready-range (lo a) (hi (+ a m)) (p a))
                                (:instance fn-hp-vhold-page (p 0) (q a)))
           :in-theory (disable take nthcdr nth fn-hp-x-ready-range fn-hp-vhold fn-hp-take-split fn-hp-vi-from-ready-range
                               fn-hp-vhold-page))
          ("Subgoal *1/1" :in-theory (enable take))))

(local
 (defun fn-hp-a2-ind (i n) (if (zp n) (list i n) (fn-hp-a2-ind (+ 1 (nfix i)) (1- n)))))

(local
 (defthm fn-hp-piw-region-agree2
   (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5) (natp r) (< r 5)
                 (natp i) (natp n) (<= (+ i n) (* 2048 (adt-cap (len (nth r (fn-hp-regs h salt)))))))
            (fn-hp-agree2 (+ (* 2048 (nth r starts)) i) i n (fn-hp-piw h salt starts np)
                          (fn-hp-wpad (nth r (fn-hp-regs h salt)))))
   :hints (("Goal" :induct (fn-hp-a2-ind i n)
            :in-theory (disable fn-hp-piw fn-hp-wpad fn-hp-regs fn-hp-lens adt-placement-ok adt-cap nth)
            :expand ((:free (a) (fn-hp-agree2 a i n (fn-hp-piw h salt starts np)
                                               (fn-hp-wpad (nth r (fn-hp-regs h salt)))))))
           ("Subgoal *1/2" :use ((:instance fn-hp-placement-natp-start (lens (fn-hp-lens h salt)))
                                 (:instance fn-hp-piw-region-word))))))

(local
 (defthm fn-hp-take-all
   (implies (true-listp x) (equal (take (len x) x) x))))

(local (defthm fn-hp-nthcdr-0 (equal (nthcdr 0 x) x)))

(defthm fn-hp-piw-region-take
  (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5) (natp r) (< r 5))
           (equal (take (* 2048 (adt-cap (len (nth r (fn-hp-regs h salt)))))
                        (nthcdr (* 2048 (nth r starts)) (fn-hp-piw h salt starts np)))
                  (fn-hp-wpad (nth r (fn-hp-regs h salt)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-piw-region-agree2 (i 0) (n (* 2048 (adt-cap (len (nth r (fn-hp-regs h salt)))))))
                 (:instance fn-hp-agree2-take (a (* 2048 (nth r starts))) (b 0)
                            (n (* 2048 (adt-cap (len (nth r (fn-hp-regs h salt))))))
                            (x (fn-hp-piw h salt starts np)) (y (fn-hp-wpad (nth r (fn-hp-regs h salt)))))
                 (:instance fn-hp-placement-natp-start (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-take-all (x (fn-hp-wpad (nth r (fn-hp-regs h salt))))))
           :in-theory (disable fn-hp-piw fn-hp-wpad fn-hp-regs fn-hp-lens adt-placement-ok adt-cap
                               fn-hp-piw-region-agree2 fn-hp-agree2-take fn-hp-take-all fn-hp-agree2 take nthcdr))))

; -----------------------------------------------------------------------------
; O. Moving region R to fresh pages at the image's end keeps the placement.

(local
 (defthm fn-hp-apart-at-end
   (implies (and (adt-placement-ok starts lens np) (natp np))
            (adt-apart np c starts lens))
   :hints (("Goal" :in-theory (disable adt-cap)))))

(local
 (defun fn-hp-pr-ind (r starts lens)
   (if (or (atom starts) (atom lens)) (list r starts lens)
     (fn-hp-pr-ind (1- r) (cdr starts) (cdr lens)))))

(local
 (defthm fn-hp-apart-update-at-end
   (implies (and (adt-apart s c starts lens) (natp s) (natp c) (<= (+ s c) np) (natp np) (natp j) (< j (len starts)))
            (adt-apart s c (update-nth j np starts) lens))
   :hints (("Goal" :induct (fn-hp-pr-ind j starts lens)
            :in-theory (e/d (update-nth) (adt-cap fn-hp-apart-at-end))))))

(local
 (defthm fn-hp-placement-mono
   (implies (and (adt-placement-ok starts lens np) (natp np) (natp np2) (<= np np2))
            (adt-placement-ok starts lens np2))
   :hints (("Goal" :induct (adt-placement-ok starts lens np) :in-theory (disable adt-cap adt-apart)))))

(defthm fn-hp-placement-relocated
  (implies (and (adt-placement-ok starts lens np) (natp np) (natp r) (< r (len starts)) (< r (len lens))
                (natp c) (<= (adt-cap (nfix (nth r lens))) c))
           (adt-placement-ok (update-nth r np starts) lens (+ np c)))
  :hints (("Goal" :induct (fn-hp-pr-ind r starts lens) :in-theory (e/d (update-nth nth) (adt-cap)))))

; -----------------------------------------------------------------------------
; P. The growth step as the host calls it.

(local
 (defthm fn-hp-natp-nth-nat-listp
   (implies (and (nat-listp l) (natp r) (< r (len l))) (natp (nth r l)))
   :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-hp-len-hdr-m-5
         (implies (equal (len starts) 5) (equal (len (fn-hp-hdr-m n lens starts np)) 13))))

(defun fn-hp-x-relocate (r c n lens starts np pgs-mem)
  ; Region R moved to C fresh pages appended at the image's end, when
  ; `fn-hp-x-append' answered (:grow R C): the pending append needs R to
  ; hold C pages (C >= R's cap; C > 0; progress:
  ; `fn-hp-grow-then-append').  N LENS STARTS NP: the open's
  ; header answer.  (mv VERDICT STARTS2 NP2 pgs-mem):
  ;   :ok     the image grew to NP2 = NP+C pages (`pgs-x-grow-image': zero,
  ;           verified); R's words were copied to page NP, its old pages
  ;           zeroed, header words 6-18 rewritten with R at NP; the copied,
  ;           zeroed and header pages and every new page are dirty.
  ;           STARTS2 = STARTS with R at NP is the placement to carry.
  ;   (:need-table T P) / (:need-page P PHYS) / :out-of-range
  ;           the header page or one of R's old pages is not ready: nothing
  ;           changed; the host fills it and asks again.
  ;   (:refused REASON)   nothing changed: :image (the store is not the
  ;           NP pages the header names), :capacity (C = 0 or below R's
  ;           cap), :placement (STARTS not placed in NP pages),
  ;           :out-of-range (a header word past 64 bits).
  ; Work: 2048 * cap word writes each for the copy and the zeroing, 13 for
  ; the header, C dirty marks, plus `pgs-x-grow-image''s resize (O(image)).
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp r) (< r 5) (natp c) (natp n) (nat-listp lens) (equal (len lens) 5)
                              (nat-listp starts) (equal (len starts) 5) (natp np))
                  :guard-hints (("Goal" :use ((:instance fn-hp-placement-natp-start (np (pgs-v-length pgs-mem)))
                                              (:instance fn-hp-natp-nth-nat-listp (l starts))
                                              (:instance fn-hp-natp-nth-nat-listp (l lens)))
                                 :in-theory (disable fn-hp-x-ready-range fn-hp-x-ready fn-hp-hdr-m adt-cap
                                                     adt-placement-ok fn-hp-u64-listp floor fn-hp-natp-nth-nat-listp)))))
  (let* ((old (nth r starts)) (cap (adt-cap (nth r lens))) (npn (+ np c))
         (starts2 (update-nth r np starts)) (hdr (fn-hp-hdr-m n lens starts2 npn)))
    (cond ((not (and (equal (pgs-v-length pgs-mem) np) (equal (pgs-d-length pgs-mem) np)
                     (equal (pgs-w-length pgs-mem) (* 2048 np))))
           (mv (list :refused :image) starts np pgs-mem))
          ((not (and (< 0 c) (<= cap c)))
           (mv (list :refused :capacity) starts np pgs-mem))
          ((not (adt-placement-ok starts lens np))
           (mv (list :refused :placement) starts np pgs-mem))
          ((not (fn-hp-u64-listp hdr))
           (mv (list :refused :out-of-range) starts np pgs-mem))
          (t
           (let ((v (fn-hp-x-ready 0 pgs-mem)))
             (if (not (eq v :ok))
                 (mv v starts np pgs-mem)
               (let ((v (fn-hp-x-ready-range old (+ old cap) pgs-mem)))
                 (if (not (eq v :ok))
                     (mv v starts np pgs-mem)
                   (let* ((pgs-mem (pgs-x-grow-image npn pgs-mem))
                          (pgs-mem (fn-hp-x-copy (* 2048 old) (* 2048 np) (* 2048 cap) pgs-mem))
                          (pgs-mem (fn-hp-x-zero (* 2048 old) (* 2048 cap) pgs-mem))
                          (pgs-mem (fn-hp-x-put 6 hdr pgs-mem))
                          (pgs-mem (fn-hp-x-mark np npn pgs-mem)))
                     (mv :ok starts2 npn pgs-mem))))))))))

; -----------------------------------------------------------------------------
; Q. The relocation's writes are the model's three blocks.

(defmacro fn-hp-x-reloc-writes (mem1)
  ; the relocation's writes after the growth, as `fn-hp-x-relocate' makes them
  `(fn-hp-x-mark np npn
                 (fn-hp-x-put 6 hdr
                              (fn-hp-x-zero (* 2048 old) (* 2048 cap)
                                            (fn-hp-x-copy (* 2048 old) (* 2048 np) (* 2048 cap) ,mem1)))))

(defmacro fn-hp-x-reloc-hyps ()
  '(and (natp old) (natp cap) (natp np) (natp npn) (<= 1 old) (<= (+ old cap) np) (<= (+ np cap) npn)
        (fn-hp-u64-listp hdr) (equal (len hdr) 13)
        (equal (pgs-w-length mem1) (* 2048 npn)) (equal (pgs-d-length mem1) npn)
        (true-listp (nth *pgs-wi* mem1))))

(local
 (defthm fn-hp-len-take-g
   (implies (natp n) (equal (len (take n x)) n))))

(defthm fn-hp-x-copy-words
  (implies (and (natp src) (natp dst) (natp k) (<= (+ src k) dst) (<= (+ dst k) (pgs-w-length pgs-mem)))
           (equal (nth *pgs-wi* (fn-hp-x-copy src dst k pgs-mem))
                  (fn-hp-rep (nth *pgs-wi* pgs-mem) dst (take k (nthcdr src (nth *pgs-wi* pgs-mem))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-copy-is-put)
                 (:instance fn-hp-x-put-words (j dst) (ws (fn-hp-x-words src k pgs-mem))))
           :in-theory (disable fn-hp-x-copy fn-hp-x-put fn-hp-x-put-words fn-hp-rep take nthcdr))))

(defthm fn-hp-x-zero-words
  (implies (and (natp j) (natp k) (<= (+ j k) (pgs-w-length pgs-mem)))
           (equal (nth *pgs-wi* (fn-hp-x-zero j k pgs-mem))
                  (fn-hp-rep (nth *pgs-wi* pgs-mem) j (adt-zeros k))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-zero-is-put)
                 (:instance fn-hp-x-put-words (ws (adt-zeros k))))
           :in-theory (disable fn-hp-x-zero fn-hp-x-put fn-hp-x-put-words fn-hp-rep))))

(local
 (defthm fn-hp-x-reloc-writes-reps
   (implies (fn-hp-x-reloc-hyps)
            (equal (nth *pgs-wi* (fn-hp-x-reloc-writes mem1))
                   (fn-hp-rep (fn-hp-rep (fn-hp-rep (nth *pgs-wi* mem1) (* 2048 np)
                                                    (take (* 2048 cap) (nthcdr (* 2048 old) (nth *pgs-wi* mem1))))
                                         (* 2048 old) (adt-zeros (* 2048 cap)))
                              6 hdr)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hp-x-copy-frame (src (* 2048 old)) (dst (* 2048 np)) (k (* 2048 cap)) (pgs-mem mem1))
                  (:instance fn-hp-x-zero-frame (j (* 2048 old)) (k (* 2048 cap))
                             (pgs-mem (fn-hp-x-copy (* 2048 old) (* 2048 np) (* 2048 cap) mem1))))
            :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-rep nth
                                take nthcdr fn-hp-u64-listp fn-hp-x-copy-frame fn-hp-x-zero-frame)))))

(local
 (defthm fn-hp-reloc-reps-commute
   (implies (and (true-listp w) (natp old) (natp cap) (natp np) (<= 1 old) (<= (+ old cap) np)
                 (<= (+ (* 2048 np) (* 2048 cap)) (len w)) (equal (len hdr) 13) (equal (len wr) (* 2048 cap)))
            (equal (fn-hp-rep (fn-hp-rep (fn-hp-rep w (* 2048 np) wr) (* 2048 old) (adt-zeros (* 2048 cap))) 6 hdr)
                   (fn-hp-rep (fn-hp-rep (fn-hp-rep w 6 hdr) (* 2048 old) (adt-zeros (* 2048 cap))) (* 2048 np) wr)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hp-rep-commute (w (fn-hp-rep w (* 2048 np) wr))
                             (a (* 2048 old)) (x (adt-zeros (* 2048 cap))) (b 6) (y hdr))
                  (:instance fn-hp-rep-commute (a (* 2048 np)) (x wr) (b 6) (y hdr))
                  (:instance fn-hp-rep-commute (w (fn-hp-rep w 6 hdr))
                             (a (* 2048 np)) (x wr) (b (* 2048 old)) (y (adt-zeros (* 2048 cap)))))
            :in-theory (disable fn-hp-rep)))))

(defthm fn-hp-x-reloc-writes-words
  (implies (fn-hp-x-reloc-hyps)
           (equal (nth *pgs-wi* (fn-hp-x-reloc-writes mem1))
                  (fn-hp-wreps (nth *pgs-wi* mem1)
                               (list (cons 6 hdr)
                                     (cons (* 2048 old) (adt-zeros (* 2048 cap)))
                                     (cons (* 2048 np) (take (* 2048 cap) (nthcdr (* 2048 old) (nth *pgs-wi* mem1))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-reloc-reps-commute (w (nth *pgs-wi* mem1))
                            (wr (take (* 2048 cap) (nthcdr (* 2048 old) (nth *pgs-wi* mem1))))))
           :in-theory (e/d (fn-hp-wreps pgs-w-length) (fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-rep nth
                                                       take nthcdr fn-hp-u64-listp fn-hp-reloc-reps-commute)))))

(local
 (defthm fn-hp-floor-2048-bounds
   (implies (natp x)
            (and (<= (* 2048 (floor x 2048)) x) (< x (+ 2048 (* 2048 (floor x 2048))))))
   :hints (("Goal" :in-theory (enable floor)))
   :rule-classes :linear))

(defthm fn-hp-x-copy-dirty
  (implies (and (natp dst) (natp p)
                (equal (nth p (nth *pgs-di* (fn-hp-x-copy src dst k pgs-mem))) 1)
                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
           (and (< dst (+ 2048 (* 2048 p))) (< (* 2048 p) (+ dst (nfix k)))))
  :hints (("Goal" :induct (fn-hp-x-copy src dst k pgs-mem) :in-theory (enable update-pgs-di update-pgs-wi)))
  :rule-classes nil)

(defthm fn-hp-x-zero-dirty
  (implies (and (natp j) (natp p)
                (equal (nth p (nth *pgs-di* (fn-hp-x-zero j k pgs-mem))) 1)
                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
           (and (< j (+ 2048 (* 2048 p))) (< (* 2048 p) (+ j (nfix k)))))
  :hints (("Goal" :induct (fn-hp-x-zero j k pgs-mem) :in-theory (enable update-pgs-di update-pgs-wi)))
  :rule-classes nil)

(defthm fn-hp-x-reloc-writes-dirty
  (implies (and (fn-hp-x-reloc-hyps) (natp p)
                (equal (nth p (nth *pgs-di* (fn-hp-x-reloc-writes mem1))) 1)
                (not (equal (nth p (nth *pgs-di* mem1)) 1)))
           (or (equal p 0) (and (<= old p) (< p (+ old cap))) (and (<= np p) (< p npn))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-mark-dirty (i np) (k npn)
                            (pgs-mem (fn-hp-x-put 6 hdr (fn-hp-x-zero (* 2048 old) (* 2048 cap)
                                                                      (fn-hp-x-copy (* 2048 old) (* 2048 np) (* 2048 cap) mem1)))))
                 (:instance fn-hp-x-put-dirty (j 6) (ws hdr)
                            (pgs-mem (fn-hp-x-zero (* 2048 old) (* 2048 cap)
                                                   (fn-hp-x-copy (* 2048 old) (* 2048 np) (* 2048 cap) mem1))))
                 (:instance fn-hp-x-zero-dirty (j (* 2048 old)) (k (* 2048 cap))
                            (pgs-mem (fn-hp-x-copy (* 2048 old) (* 2048 np) (* 2048 cap) mem1)))
                 (:instance fn-hp-x-copy-dirty (src (* 2048 old)) (dst (* 2048 np)) (k (* 2048 cap)) (pgs-mem mem1)))
           :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark nth fn-hp-u64-listp))))

(defthm fn-hp-x-reloc-writes-frame
  (implies (fn-hp-x-reloc-hyps)
           (and (equal (nth *pgs-vi* (fn-hp-x-reloc-writes mem1)) (nth *pgs-vi* mem1))
                (equal (pgs-v-length (fn-hp-x-reloc-writes mem1)) (pgs-v-length mem1))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-copy-frame (src (* 2048 old)) (dst (* 2048 np)) (k (* 2048 cap)) (pgs-mem mem1))
                 (:instance fn-hp-x-zero-frame (j (* 2048 old)) (k (* 2048 cap))
                            (pgs-mem (fn-hp-x-copy (* 2048 old) (* 2048 np) (* 2048 cap) mem1)))
                 (:instance fn-hp-x-put-lengths (j 6) (ws hdr)
                            (pgs-mem (fn-hp-x-zero (* 2048 old) (* 2048 cap)
                                                   (fn-hp-x-copy (* 2048 old) (* 2048 np) (* 2048 cap) mem1)))))
           :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark nth fn-hp-u64-listp
                               fn-hp-x-copy-frame fn-hp-x-zero-frame fn-hp-x-put-lengths))))

; -----------------------------------------------------------------------------
; R. The keystone.

(defthm fn-hp-x-relocate-ok-checks
  (implies (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok)
           (and (equal (pgs-v-length pgs-mem) np) (equal (pgs-d-length pgs-mem) np)
                (equal (pgs-w-length pgs-mem) (* 2048 np))
                (< 0 c) (<= (adt-cap (nth r lens)) c) (adt-placement-ok starts lens np)
                (fn-hp-u64-listp (fn-hp-hdr-m n lens (update-nth r np starts) (+ np c)))
                (equal (fn-hp-x-ready 0 pgs-mem) :ok)
                (equal (fn-hp-x-ready-range (nth r starts) (+ (nth r starts) (adt-cap (nth r lens))) pgs-mem) :ok)))
  :hints (("Goal" :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-x-ready fn-hp-x-ready-range
                                      fn-hp-hdr-m adt-cap adt-placement-ok fn-hp-u64-listp)))
  :rule-classes nil)

(defthm fn-hp-x-relocate-ok-unfolds
  (implies (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok)
           (and (equal (mv-nth 1 (fn-hp-x-relocate r c n lens starts np pgs-mem)) (update-nth r np starts))
                (equal (mv-nth 2 (fn-hp-x-relocate r c n lens starts np pgs-mem)) (+ np c))
                (equal (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))
                       (let ((old (nth r starts)) (cap (adt-cap (nth r lens))) (npn (+ np c))
                             (hdr (fn-hp-hdr-m n lens (update-nth r np starts) (+ np c))))
                         (fn-hp-x-reloc-writes (pgs-x-grow-image npn pgs-mem))))))
  :hints (("Goal" :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-x-ready fn-hp-x-ready-range
                                      fn-hp-hdr-m adt-cap adt-placement-ok fn-hp-u64-listp))))

(local
 (defthm fn-hp-nth-adt-lens-r
   (implies (and (natp r) (< r (len regs))) (equal (nth r (adt-lens regs)) (len (nth r regs))))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-hp-len-regs-5-r
   (equal (len (fn-hp-regs h salt)) 5)
   :hints (("Goal" :use ((:instance fn-hp-len-lens)) :in-theory (e/d (fn-hp-lens) (fn-hp-len-lens fn-hp-regs))))))

(defthm fn-hp-reloc-copied-words
  ; the words the copy reads from a grown store are the region's padded words
  (implies (and (fn-hp-vhold 0 np pgs-mem (fn-hp-piw h salt starts np))
                (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5) (natp r) (< r 5)
                (natp np) (natp npn) (< np npn)
                (equal (pgs-v-length pgs-mem) np) (equal (pgs-w-length pgs-mem) (* 2048 np))
                (equal (fn-hp-x-ready-range (nth r starts) (+ (nth r starts) (adt-cap (nth r (fn-hp-lens h salt)))) pgs-mem) :ok))
           (equal (take (* 2048 (adt-cap (nth r (fn-hp-lens h salt))))
                        (nthcdr (* 2048 (nth r starts)) (nth *pgs-wi* (pgs-x-grow-image npn pgs-mem))))
                  (fn-hp-wpad (nth r (fn-hp-regs h salt)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-placement-natp-start (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-store-pages-hold (a (nth r starts)) (m (adt-cap (nth r (fn-hp-lens h salt))))
                            (iw (fn-hp-piw h salt starts np)))
                 (:instance fn-hp-piw-region-take)
                 (:instance fn-hp-take-nthcdr-append-front (a (* 2048 (nth r starts)))
                            (n (* 2048 (adt-cap (nth r (fn-hp-lens h salt)))))
                            (x (true-list-fix (nth *pgs-wi* pgs-mem)))
                            (y (adt-zeros (- (* 2048 npn) (len (nth *pgs-wi* pgs-mem)))))))
           :in-theory (e/d (fn-hp-lens pgs-w-length)
                           (fn-hp-store-pages-hold fn-hp-piw-region-take fn-hp-take-nthcdr-append-front fn-hp-piw fn-hp-wpad
                            fn-hp-regs adt-cap adt-placement-ok take nthcdr fn-hp-vhold fn-hp-x-ready-range nth)))))

(defmacro fn-hp-x-reloc-key-hyps ()
  '(and (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
        (natp r) (< r 5) (natp c)
        (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
        (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok)))

(local
 (defthm fn-hp-x-relocate-facts
   (implies (fn-hp-x-reloc-key-hyps)
            (and (natp np) (natp (nth r starts)) (<= 1 (nth r starts))
                 (<= (+ (nth r starts) (adt-cap (nth r (fn-hp-lens h salt)))) np)
                 (adt-placement-ok starts (fn-hp-lens h salt) np)
                 (adt-placement-ok (update-nth r np starts) (fn-hp-lens h salt) (+ np c))
                 (equal (pgs-v-length pgs-mem) np) (equal (pgs-w-length pgs-mem) (* 2048 np))
                 (equal (pgs-d-length pgs-mem) np)
                 (< 0 c) (<= (adt-cap (nth r (fn-hp-lens h salt))) c)
                 (fn-hp-vhold 0 np pgs-mem (fn-hp-piw h salt starts np))
                 (equal (len (fn-hp-piw h salt starts np)) (* 2048 np))
                 (fn-hp-u64-listp (fn-hp-hdr-m (len h) (fn-hp-lens h salt) (update-nth r np starts) (+ np c)))
                 (equal (fn-hp-x-ready 0 pgs-mem) :ok)
                 (equal (fn-hp-x-ready-range (nth r starts) (+ (nth r starts) (adt-cap (nth r (fn-hp-lens h salt))))
                                             pgs-mem) :ok)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hp-x-relocate-ok-checks)
                  (:instance fn-hp-placement-natp-start (lens (fn-hp-lens h salt)))
                  (:instance fn-hp-placement-relocated (lens (fn-hp-lens h salt)))
                  (:instance fn-hp-len-piw (s starts))
                  (:instance fn-hp-natp-nth-nat-listp (l (fn-hp-lens h salt))))
            :in-theory (e/d (natp) (fn-hp-placement-relocated fn-hp-len-piw fn-hp-x-relocate
                                     fn-hp-piw fn-hp-lens fn-hp-regs adt-cap adt-placement-ok fn-hp-vhold nth update-nth
                                     fn-hp-natp-nth-nat-listp fn-hp-x-ready fn-hp-x-ready-range fn-hp-hdr-m fn-hp-u64-listp))))))

(local
 (defthm fn-hp-x-relocate-mem2-words
   (implies (fn-hp-x-reloc-key-hyps)
            (equal (nth *pgs-wi* (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem)))
                   (fn-hp-wreps (nth *pgs-wi* (pgs-x-grow-image (+ np c) pgs-mem))
                                (fn-hp-reloc-blocks (len h) (fn-hp-lens h salt) starts r np (+ np c)
                                                    (fn-hp-wpad (nth r (fn-hp-regs h salt)))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hp-x-relocate-facts)
                  (:instance fn-hp-grow-image-lengths (npn (+ np c)))
                  (:instance fn-hp-grow-image-words (npn (+ np c)))
                  (:instance fn-hp-reloc-copied-words (npn (+ np c)))
                  (:instance fn-hp-x-reloc-writes-words (old (nth r starts)) (cap (adt-cap (nth r (fn-hp-lens h salt))))
                             (npn (+ np c)) (hdr (fn-hp-hdr-m (len h) (fn-hp-lens h salt) (update-nth r np starts) (+ np c)))
                             (mem1 (pgs-x-grow-image (+ np c) pgs-mem))))
            :in-theory (e/d (fn-hp-reloc-blocks)
                            (fn-hp-x-relocate-facts fn-hp-grow-image-lengths
                             fn-hp-grow-image-words fn-hp-reloc-copied-words fn-hp-x-reloc-writes-words
                             fn-hp-x-relocate fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-piw fn-hp-wreps fn-hp-wpad
                             fn-hp-regs fn-hp-lens adt-cap adt-placement-ok fn-hp-vhold fn-hp-hdr-m fn-hp-u64-listp take nthcdr
                             fn-hp-x-ready fn-hp-x-ready-range pgs-x-grow-image nth update-nth resize-list))))))

; exported: the step (books/history-pages-step.lisp) keeps verified pages verified
(defthm fn-hp-x-relocate-mem2-frame
   (implies (fn-hp-x-reloc-key-hyps)
            (and (equal (nth *pgs-vi* (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem)))
                        (nth *pgs-vi* (pgs-x-grow-image (+ np c) pgs-mem)))
                 (equal (pgs-v-length (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))) (+ np c))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hp-x-relocate-facts)
                  (:instance fn-hp-grow-image-lengths (npn (+ np c)))
                  (:instance fn-hp-grow-image-words (npn (+ np c)))
                  (:instance fn-hp-x-reloc-writes-frame (old (nth r starts)) (cap (adt-cap (nth r (fn-hp-lens h salt))))
                             (npn (+ np c)) (hdr (fn-hp-hdr-m (len h) (fn-hp-lens h salt) (update-nth r np starts) (+ np c)))
                             (mem1 (pgs-x-grow-image (+ np c) pgs-mem))))
            :in-theory (e/d () (fn-hp-x-relocate-facts fn-hp-grow-image-lengths
                                fn-hp-grow-image-words fn-hp-x-reloc-writes-frame
                                fn-hp-x-relocate fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-piw fn-hp-wreps fn-hp-wpad
                                fn-hp-regs fn-hp-lens adt-cap adt-placement-ok fn-hp-vhold fn-hp-hdr-m fn-hp-u64-listp take nthcdr
                                fn-hp-x-ready fn-hp-x-ready-range pgs-x-grow-image nth update-nth resize-list)))))

(defthm fn-hp-x-relocate-vhold
  (implies (fn-hp-x-reloc-key-hyps)
           (let ((mem2 (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))))
             (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt (update-nth r np starts) (+ np c)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-relocate-facts)
                 (:instance fn-hp-x-relocate-mem2-words)
                 (:instance fn-hp-x-relocate-mem2-frame)
                 (:instance fn-hp-grow-image-lengths (npn (+ np c)))
                 (:instance fn-hp-vhold-after-grow-p (p 0) (npn (+ np c)) (iw (fn-hp-piw h salt starts np)))
                 (:instance fn-hp-vhold-of-wreps (p 0) (np (+ np c)) (pgs-mem (pgs-x-grow-image (+ np c) pgs-mem))
                            (mem2 (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem)))
                            (iw (append (fn-hp-piw h salt starts np) (adt-zeros (* 2048 (- (+ np c) np)))))
                            (bs (fn-hp-reloc-blocks (len h) (fn-hp-lens h salt) starts r np (+ np c)
                                                    (fn-hp-wpad (nth r (fn-hp-regs h salt))))))
                 (:instance fn-hp-piw-relocated (s starts) (tt np) (npn (+ np c))))
           :in-theory (union-theories '(fn-hp-starts-okp natp) (theory 'minimal-theory)))))

(local
 (defthm fn-hp-x-relocate-dirty-where
   (implies (and (fn-hp-x-reloc-key-hyps) (natp p)
                 (equal (nth p (nth *pgs-di* (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem)))) 1)
                 (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
            (or (equal p 0)
                (and (<= (nth r starts) p) (< p (+ (nth r starts) (adt-cap (nth r lens)))))
                (and (<= np p) (< p (+ np c)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hp-x-relocate-facts)
                  (:instance fn-hp-grow-image-lengths (npn (+ np c)))
                  (:instance fn-hp-grow-image-words (npn (+ np c)))
                  (:instance fn-hp-nth-resize-list (j p) (l (nth *pgs-di* pgs-mem)) (n (+ np c)) (d 0))
                  (:instance fn-hp-x-reloc-writes-dirty (old (nth r starts)) (cap (adt-cap (nth r (fn-hp-lens h salt))))
                             (npn (+ np c)) (hdr (fn-hp-hdr-m (len h) (fn-hp-lens h salt) (update-nth r np starts) (+ np c)))
                             (mem1 (pgs-x-grow-image (+ np c) pgs-mem))))
            :in-theory (e/d (pgs-d-length)
                            (fn-hp-x-relocate-facts fn-hp-grow-image-lengths fn-hp-nth-resize-list
                             fn-hp-grow-image-words fn-hp-x-reloc-writes-dirty
                             fn-hp-x-relocate fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-piw fn-hp-wreps fn-hp-wpad
                             fn-hp-regs fn-hp-lens adt-cap adt-placement-ok fn-hp-vhold fn-hp-hdr-m fn-hp-u64-listp take nthcdr
                             fn-hp-x-ready fn-hp-x-ready-range pgs-x-grow-image nth update-nth resize-list))))))

(local
 (defthm fn-hp-x-reloc-writes-vi
   (implies (fn-hp-x-reloc-hyps)
            (equal (pgs-vi p (fn-hp-x-reloc-writes mem1)) (pgs-vi p mem1)))
   :hints (("Goal" :use ((:instance fn-hp-x-reloc-writes-frame))
            :in-theory (e/d (pgs-vi) (fn-hp-x-reloc-writes-frame fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark
                                      fn-hp-u64-listp nth))))))

(local
 (defthm fn-hp-x-relocate-dirty-verified
   (implies (and (fn-hp-x-reloc-key-hyps) (natp p)
                 (or (equal p 0)
                     (and (<= (nth r starts) p) (< p (+ (nth r starts) (adt-cap (nth r lens)))))
                     (and (<= np p) (< p (+ np c)))))
            (equal (pgs-vi p (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))) 2))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hp-x-relocate-facts)
                  (:instance fn-hp-grow-image-lengths (npn (+ np c)))
                  (:instance fn-hp-grow-image-words (npn (+ np c)))
                  (:instance fn-hp-x-reloc-writes-vi (old (nth r starts)) (cap (adt-cap (nth r (fn-hp-lens h salt))))
                             (npn (+ np c)) (hdr (fn-hp-hdr-m (len h) (fn-hp-lens h salt) (update-nth r np starts) (+ np c)))
                             (mem1 (pgs-x-grow-image (+ np c) pgs-mem)))
                  (:instance fn-hp-grow-image-vi (q p) (npn (+ np c)))
                  (:instance fn-hp-x-ready-ok (p 0))
                  (:instance fn-hp-vi-from-ready-range (lo (nth r starts))
                             (hi (+ (nth r starts) (adt-cap (nth r (fn-hp-lens h salt)))))))
            :in-theory (e/d ()
                            (fn-hp-x-relocate-facts fn-hp-x-ready-ok fn-hp-vi-from-ready-range fn-hp-grow-image-lengths
                             fn-hp-grow-image-words fn-hp-x-reloc-writes-vi fn-hp-grow-image-vi fn-hp-natp-nth-nat-listp
                             fn-hp-x-relocate fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-piw fn-hp-wreps fn-hp-wpad
                             fn-hp-regs fn-hp-lens adt-cap adt-placement-ok fn-hp-vhold fn-hp-hdr-m fn-hp-u64-listp take nthcdr
                             fn-hp-x-ready fn-hp-x-ready-range pgs-x-grow-image nth update-nth resize-list))))))

(local
 (defthm fn-hp-nat-listp-update-nth
   (implies (and (nat-listp l) (natp v) (natp r) (< r (len l))) (nat-listp (update-nth r v l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

; KEYSTONE (the growth step): over any page store state whose verified
; pages hold the history's image placed at STARTS in NP pages, a relocation
; of region R to C fresh pages that answers :ok answers STARTS2 = STARTS
; with R at NP and NP2 = NP+C, keeps the placement valid, leaves the store
; NP2 pages long with every verified page holding the image at the new
; placement, and marks dirty only the header page, R's old pages and the
; new pages, each verified.
(defthm fn-hp-x-relocate-refines
  (implies (and (equal n (len h)) (equal lens (fn-hp-lens h salt)) (fn-hp-starts-okp starts)
                (natp r) (< r 5) (natp c)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
           (let ((starts2 (mv-nth 1 (fn-hp-x-relocate r c n lens starts np pgs-mem)))
                 (np2 (mv-nth 2 (fn-hp-x-relocate r c n lens starts np pgs-mem)))
                 (mem2 (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))))
             (and (equal starts2 (update-nth r np starts))
                  (equal np2 (+ np c))
                  (fn-hp-starts-okp starts2)
                  (adt-placement-ok starts2 lens np2)
                  (equal (pgs-v-length mem2) np2)
                  (fn-hp-vhold 0 (pgs-v-length mem2) mem2 (fn-hp-piw h salt starts2 np2))
                  (implies (and (natp p) (equal (nth p (nth *pgs-di* mem2)) 1)
                                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
                           (and (or (equal p 0)
                                    (and (<= (nth r starts) p) (< p (+ (nth r starts) (adt-cap (nth r lens)))))
                                    (and (<= np p) (< p np2)))
                                (equal (pgs-vi p mem2) 2))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-relocate-facts)
                 (:instance fn-hp-x-relocate-mem2-frame)
                 (:instance fn-hp-x-relocate-vhold)
                 (:instance fn-hp-x-relocate-dirty-where)
                 (:instance fn-hp-x-relocate-dirty-verified))
           :in-theory (e/d (fn-hp-starts-okp)
                           (fn-hp-x-relocate-facts fn-hp-x-relocate-mem2-frame fn-hp-x-relocate-vhold
                            fn-hp-x-relocate-dirty-where fn-hp-x-relocate-dirty-verified
                            fn-hp-x-relocate fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-piw fn-hp-wreps fn-hp-wpad
                            fn-hp-regs fn-hp-lens adt-cap adt-placement-ok fn-hp-vhold fn-hp-hdr-m fn-hp-u64-listp take nthcdr
                            fn-hp-x-ready fn-hp-x-ready-range pgs-x-grow-image nth resize-list)))))

; An answer other than :ok changes nothing: the page store, the placement
; and the page count come back as given.
(defthm fn-hp-x-relocate-not-ok-unchanged
  (implies (not (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
           (and (equal (mv-nth 1 (fn-hp-x-relocate r c n lens starts np pgs-mem)) starts)
                (equal (mv-nth 2 (fn-hp-x-relocate r c n lens starts np pgs-mem)) np)
                (equal (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem)) pgs-mem)))
  :hints (("Goal" :in-theory (disable fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark fn-hp-x-ready fn-hp-x-ready-range
                                      fn-hp-hdr-m adt-cap adt-placement-ok fn-hp-u64-listp pgs-x-grow-image))))

(in-theory (disable fn-hp-x-relocate-mem2-frame))
