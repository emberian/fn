;; fn: the history's writer over the page store's stobj, as the host calls
;; it (lane arena-store-3, 2026-09-28).  Prefix fn-hp-.  The model (the
;; appended image's words are the old words with six blocks replaced) is
;; books/history-pages-write.lisp; this book is the stobj side and the
;; keystones.
(in-package "ACL2")
(include-book "history-pages-write")
(include-book "history-pages-arith")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-scc-octet-listp-true)
                          (:rewrite pgs-true-list-fix-when-true-listp))))

; -----------------------------------------------------------------------------
; F. The writes over the page store's words.

(local
 (defthm fn-hp-take-update-nth-last
   (implies (and (natp j) (< j (len w)))
            (equal (take (+ 1 j) (update-nth j v w)) (append (take j w) (list v))))
   :hints (("Goal" :in-theory (enable take update-nth)))))

(local
 (defthm fn-hp-nthcdr-update-nth-past
   (implies (and (natp j) (natp m) (< j m))
            (equal (nthcdr m (update-nth j v w)) (nthcdr m w)))
   :hints (("Goal" :in-theory (enable nthcdr update-nth)))))

(defthm fn-hp-rep-cons
  (implies (and (natp j) (< j (len w)))
           (equal (fn-hp-rep w j (cons v ws))
                  (fn-hp-rep (update-nth j v w) (+ 1 j) ws)))
  :hints (("Goal" :in-theory (enable fn-hp-rep))))

(local
 (defthm fn-hp-append-take-nthcdr
   (implies (and (natp j) (<= j (len w)))
            (equal (append (take j w) (nthcdr j w)) w))
   :hints (("Goal" :in-theory (enable take nthcdr)))))

(defthm fn-hp-rep-nil
  (implies (and (natp j) (<= j (len w)))
           (equal (fn-hp-rep w j nil) w))
  :hints (("Goal" :in-theory (enable fn-hp-rep))))

(defun fn-hp-x-put (j ws pgs-mem)
  ; words J .. J+|WS|-1 := WS, each one's page dirty
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp j) (fn-hp-u64-listp ws)
                              (<= (+ j (len ws)) (pgs-w-length pgs-mem))
                              (or (atom ws) (< (floor (+ j (len ws) -1) 2048) (pgs-d-length pgs-mem))))
                  :guard-hints (("Goal" :in-theory (disable floor)))))
  (if (atom ws)
      pgs-mem
    (let* ((pgs-mem (update-pgs-wi j (car ws) pgs-mem))
           (pgs-mem (update-pgs-di (floor j 2048) 1 pgs-mem)))
      (fn-hp-x-put (+ 1 j) (cdr ws) pgs-mem))))
(local (in-theory (disable floor)))

(defthm fn-hp-fields-of-update-w-d
  (and (equal (nth *pgs-vi* (update-pgs-wi i v pgs-mem)) (nth *pgs-vi* pgs-mem))
       (equal (nth *pgs-tvi* (update-pgs-wi i v pgs-mem)) (nth *pgs-tvi* pgs-mem))
       (equal (nth *pgs-di* (update-pgs-wi i v pgs-mem)) (nth *pgs-di* pgs-mem))
       (equal (nth *pgs-wi* (update-pgs-wi i v pgs-mem)) (update-nth i v (nth *pgs-wi* pgs-mem)))
       (equal (nth *pgs-vi* (update-pgs-di i v pgs-mem)) (nth *pgs-vi* pgs-mem))
       (equal (nth *pgs-tvi* (update-pgs-di i v pgs-mem)) (nth *pgs-tvi* pgs-mem))
       (equal (nth *pgs-wi* (update-pgs-di i v pgs-mem)) (nth *pgs-wi* pgs-mem))
       (equal (nth *pgs-di* (update-pgs-di i v pgs-mem)) (update-nth i v (nth *pgs-di* pgs-mem))))
  :hints (("Goal" :in-theory (enable update-pgs-wi update-pgs-di))))

(defthm fn-hp-x-put-lengths
  (implies (and (natp j) (<= (+ j (len ws)) (pgs-w-length pgs-mem))
                (or (atom ws) (< (floor (+ j (len ws) -1) 2048) (pgs-d-length pgs-mem))))
           (and (equal (pgs-w-length (fn-hp-x-put j ws pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-d-length (fn-hp-x-put j ws pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (fn-hp-x-put j ws pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (fn-hp-x-put j ws pgs-mem)) (pgs-tv-length pgs-mem))
                (equal (nth *pgs-vi* (fn-hp-x-put j ws pgs-mem)) (nth *pgs-vi* pgs-mem))
                (equal (nth *pgs-tvi* (fn-hp-x-put j ws pgs-mem)) (nth *pgs-tvi* pgs-mem))))
  :hints (("Goal" :induct (fn-hp-x-put j ws pgs-mem))
          ("Subgoal *1/2" :use ((:instance fn-hp-floor-2048-mono (a j) (b (+ j (len ws) -1)))))))
(defthm fn-hp-x-put-words
  (implies (and (natp j) (true-listp ws)
                (<= (+ j (len ws)) (pgs-w-length pgs-mem)))
           (equal (nth *pgs-wi* (fn-hp-x-put j ws pgs-mem))
                  (fn-hp-rep (nth *pgs-wi* pgs-mem) j ws)))
  :hints (("Goal" :induct (fn-hp-x-put j ws pgs-mem) :in-theory (enable pgs-w-length))))

(defthm fn-hp-x-put-dirty
  (implies (and (natp j) (natp p)
                (equal (nth p (nth *pgs-di* (fn-hp-x-put j ws pgs-mem))) 1)
                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
           (and (consp ws) (<= (floor j 2048) p) (<= p (floor (+ j (len ws) -1) 2048))))
  :hints (("Goal" :induct (fn-hp-x-put j ws pgs-mem))
          ("Subgoal *1/2" :use ((:instance fn-hp-floor-2048-mono (a j) (b (+ 1 j)))
                                (:instance fn-hp-floor-2048-mono (a j) (b (+ j (len ws) -1))))))
  :rule-classes nil)
; -----------------------------------------------------------------------------
; G. The writer as the host calls it.

(defun fn-hp-x-add (lens dl)
  (declare (xargs :guard (and (nat-listp lens) (nat-listp dl))))
  (if (or (atom lens) (atom dl)) nil
    (cons (+ (car lens) (car dl)) (fn-hp-x-add (cdr lens) (cdr dl)))))

(defun fn-hp-x-caps-ok (lens lens2)
  ; every region word-aligned and none changes its cap
  (declare (xargs :guard (and (nat-listp lens) (nat-listp lens2))))
  (if (or (atom lens) (atom lens2)) t
    (and (equal (mod (car lens) 8) 0)
         (equal (adt-cap (car lens2)) (adt-cap (car lens)))
         (fn-hp-x-caps-ok (cdr lens) (cdr lens2)))))

(defun fn-hp-x-grow-region (r lens lens2)
  ; the first region whose cap changes, counted from R
  (declare (xargs :guard (and (natp r) (nat-listp lens) (nat-listp lens2))))
  (if (or (atom lens) (atom lens2)) r
    (if (equal (adt-cap (car lens2)) (adt-cap (car lens)))
        (fn-hp-x-grow-region (+ 1 r) (cdr lens) (cdr lens2))
      r)))

(defun fn-hp-bb-list (starts lens wls)
  ; per region its block: its words WL at the region's end
  (declare (xargs :guard (and (true-listp starts) (true-listp lens) (true-listp wls))))
  (if (or (atom starts) (atom lens) (atom wls)) nil
    (cons (cons (+ (* 2048 (nfix (car starts))) (floor (nfix (car lens)) 8)) (car wls))
          (fn-hp-bb-list (cdr starts) (cdr lens) (cdr wls)))))

(defun fn-hp-x-blocks (n lens lens2 starts mkey tl pw)
  ; the six blocks of an append, from the open's header answer (N LENS
  ; STARTS), the new lengths LENS2, and the row: MKEY, the tree's length
  ; TL, the padded tree as words PW
  (declare (xargs :guard (and (natp n) (nat-listp lens) (nat-listp lens2) (nat-listp starts))))
  (cons (cons 6 (fn-hp-hb (+ 1 n) starts lens2))
        (fn-hp-bb-list starts lens (list (list mkey) (list tl) (list (nth 4 lens)) (list (* 8 (len pw))) pw))))

(defun fn-hp-x-blocks-ready (blocks pgs-mem)
  ; :ok when every page a block touches is resident and verified, else the
  ; first verdict the host serves (a fill, then it asks again)
  (declare (xargs :stobjs pgs-mem :guard (alistp blocks)))
  (if (atom blocks) :ok
    (let ((j (nfix (car (car blocks)))) (k (len (cdr (car blocks)))))
      (if (zp k)
          (fn-hp-x-blocks-ready (cdr blocks) pgs-mem)
        (let ((v (fn-hp-x-pool-ready j k pgs-mem)))
          (cond ((not (eq v :ok)) v)
                ((not (< (floor (+ j k -1) 2048) (pgs-d-length pgs-mem))) :out-of-range)
                (t (fn-hp-x-blocks-ready (cdr blocks) pgs-mem))))))))

(defthm fn-hp-u64-listp-true-listp
  (implies (fn-hp-u64-listp x) (true-listp x))
  :rule-classes :forward-chaining)

(defun fn-hp-x-put-blocks (blocks pgs-mem)
  ; each block written (a block that is not u64 words in range is skipped:
  ; unreachable after `fn-hp-x-blocks-ready' and the writer's checks)
  (declare (xargs :stobjs pgs-mem :guard (alistp blocks)))
  (if (atom blocks) pgs-mem
    (let ((j (nfix (car (car blocks)))) (ws (cdr (car blocks))))
      (if (and (fn-hp-u64-listp ws) (<= (+ j (len ws)) (pgs-w-length pgs-mem))
               (or (atom ws) (< (floor (+ j (len ws) -1) 2048) (pgs-d-length pgs-mem))))
          (let ((pgs-mem (fn-hp-x-put j ws pgs-mem)))
            (fn-hp-x-put-blocks (cdr blocks) pgs-mem))
        (fn-hp-x-put-blocks (cdr blocks) pgs-mem)))))
(local
 (defthm fn-hp-unle-bound
   (implies (and (adt-octetsp b) (natp w))
            (< (adt-unle w b) (expt 256 w)))
   :hints (("Goal" :induct (adt-unle w b) :in-theory (enable adt-unle adt-octetsp expt)))
   :rule-classes :linear))

(defthm fn-hp-u64-listp-pack8
  (implies (adt-octetsp b) (fn-hp-u64-listp (fn-hp-pack8 k b)))
  :hints (("Goal" :induct (fn-hp-pack8 k b))
          ("Subgoal *1/2" :use ((:instance fn-hp-unle-bound (w 8))))))

(defthm fn-hp-len-pack8-x (equal (len (fn-hp-pack8 k b)) (nfix k)))
(defthm fn-hp-nat-listp-x-add
  (implies (and (nat-listp a) (nat-listp b)) (nat-listp (fn-hp-x-add a b))))

(defthm fn-hp-alistp-bb-list (alistp (fn-hp-bb-list starts lens wls)))

(defthm fn-hp-alistp-x-blocks
  (alistp (fn-hp-x-blocks n lens lens2 starts mkey tl pw)))

(defun fn-hp-x-aligned (lens)
  (declare (xargs :guard (nat-listp lens)))
  (if (atom lens) t (and (equal (mod (nfix (car lens)) 8) 0) (fn-hp-x-aligned (cdr lens)))))

(defthm fn-hp-true-listp-scc-encode
  (true-listp (fn-scc-encode x))
  :rule-classes :type-prescription)

(defun fn-hp-x-append-plan (ev salt n lens starts)
  ; The append's checks and blocks, changing nothing: (mv VERDICT BLOCKS
  ; LENS2), VERDICT nil when BLOCKS are to be written, else
  ;   (:grow R)           region R's cap would change (the growth path
  ;                       relocates the region, FNADTSN2)
  ;   (:refused REASON)   :event (not encodable), :alignment, :out-of-range
  (declare (xargs :guard (and (natp n) (nat-listp lens) (equal (len lens) 5)
                              (nat-listp starts) (equal (len starts) 5))
                  :guard-hints (("Goal" :in-theory (disable fn-scc-encode fn-hp-pad8 fn-hp-x-caps-ok adt-cap
                                                            fn-hp-hb fn-hp-pack8 floor mod fn-hp-x-blocks
                                                            fn-hp-x-grow-region fn-sccb-treep fn-hp-mkey
                                                            fn-hp-u64-listp fn-scc-program fn-hp-x-aligned)))))
  (if (not (fn-sccb-treep ev))
      (mv (list :refused :event) nil lens)
    (let* ((enc (fn-scc-encode ev)) (tl (len enc)))
      (if (not (unsigned-byte-p 64 tl))
          (mv (list :refused :event) nil lens)
        (let* ((pe (fn-hp-pad8 enc)) (plen (len pe))
               (lens2 (fn-hp-x-add lens (list 8 8 8 8 plen))))
          (cond ((not (fn-hp-x-aligned lens))
                 (mv (list :refused :alignment) nil lens))
                ((not (fn-hp-x-caps-ok lens lens2))
                 (mv (list :grow (fn-hp-x-grow-region 0 lens lens2)) nil lens))
                ((not (and (unsigned-byte-p 64 (+ 1 n)) (fn-hp-u64-listp lens2) (fn-hp-u64-listp starts)))
                 (mv (list :refused :out-of-range) nil lens))
                (t (mv nil
                       (fn-hp-x-blocks n lens lens2 starts (fn-hp-mkey ev salt) tl
                                       (fn-hp-pack8 (floor plen 8) pe))
                       lens2))))))))

(defthm fn-hp-alistp-x-append-plan
  (alistp (mv-nth 1 (fn-hp-x-append-plan ev salt n lens starts)))
  :hints (("Goal" :in-theory (disable fn-hp-x-blocks fn-scc-encode fn-hp-pad8 fn-hp-x-caps-ok fn-hp-pack8 fn-scc-program fn-sccb-treep))))

(defun fn-hp-x-append (ev salt n lens starts pgs-mem)
  ; The append of the event EV, as the host calls it, over the open's header
  ; answer (N LENS STARTS) the host carries: (mv VERDICT N2 LENS2 pgs-mem).
  ;   :ok                 the six blocks are written into the page store's
  ;                       words and their pages marked dirty; (N2 LENS2
  ;                       STARTS) is the new header answer to carry
  ;   (:need-table T P) / (:need-page P PHYS) / :out-of-range
  ;                       a page a block touches is not ready: nothing
  ;                       written; the host fills it and asks again
  ;   (:grow R), (:refused REASON)   as `fn-hp-x-append-plan': nothing written
  ; Every write lands on a verified page: the check precedes every write.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp n) (nat-listp lens) (equal (len lens) 5)
                              (nat-listp starts) (equal (len starts) 5))
                  :guard-hints (("Goal" :in-theory (disable fn-hp-x-append-plan fn-hp-x-blocks-ready
                                                            fn-hp-x-put-blocks)))))
  (mv-let (verdict blocks lens2)
    (fn-hp-x-append-plan ev salt n lens starts)
    (if verdict
        (mv verdict n lens pgs-mem)
      (let ((v (fn-hp-x-blocks-ready blocks pgs-mem)))
        (if (not (eq v :ok))
            (mv v n lens pgs-mem)
          (let ((pgs-mem (fn-hp-x-put-blocks blocks pgs-mem)))
            (mv :ok (+ 1 n) lens2 pgs-mem)))))))
; -----------------------------------------------------------------------------
; I. The writes over the stobj are the model's replacements.

(defun fn-hp-blocks-fit (blocks wlen dlen)
  ; every block nonempty u64 words inside WLEN words and DLEN pages
  (declare (xargs :verify-guards nil))
  (if (atom blocks) t
    (let ((j (car (car blocks))) (ws (cdr (car blocks))))
      (and (consp (car blocks)) (natp j) (consp ws) (fn-hp-u64-listp ws)
           (natp wlen) (natp dlen)
           (<= (+ j (len ws)) wlen) (< (floor (+ j (len ws) -1) 2048) dlen)
           (fn-hp-blocks-fit (cdr blocks) wlen dlen)))))

(local (in-theory (disable fn-hp-x-pool-ready-bound fn-hp-x-pool-ready fn-hp-x-ready-range fn-cp-id-length-bound
                          pgs-ptab-p-true-listp)))

(defthm fn-hp-x-put-blocks-frame
  (implies (fn-hp-blocks-fit blocks (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
           (and (equal (nth *pgs-vi* (fn-hp-x-put-blocks blocks pgs-mem)) (nth *pgs-vi* pgs-mem))
                (equal (nth *pgs-tvi* (fn-hp-x-put-blocks blocks pgs-mem)) (nth *pgs-tvi* pgs-mem))
                (equal (pgs-v-length (fn-hp-x-put-blocks blocks pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-w-length (fn-hp-x-put-blocks blocks pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-d-length (fn-hp-x-put-blocks blocks pgs-mem)) (pgs-d-length pgs-mem))))
  :hints (("Goal" :induct (fn-hp-x-put-blocks blocks pgs-mem)
           :in-theory (disable fn-hp-x-put floor fn-hp-rep fn-hp-u64-listp))
          ("Subgoal *1/2" :use ((:instance fn-hp-x-put-lengths (j (car (car blocks))) (ws (cdr (car blocks)))))
           :in-theory (disable fn-hp-x-put floor fn-hp-rep fn-hp-x-put-lengths fn-hp-u64-listp nth))))

(defthm fn-hp-x-put-blocks-words
  (implies (fn-hp-blocks-fit blocks (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
           (equal (nth *pgs-wi* (fn-hp-x-put-blocks blocks pgs-mem))
                  (fn-hp-wreps (nth *pgs-wi* pgs-mem) blocks)))
  :hints (("Goal" :induct (fn-hp-x-put-blocks blocks pgs-mem)
           :in-theory (disable fn-hp-x-put floor fn-hp-rep fn-hp-u64-listp))
          ("Subgoal *1/2" :use ((:instance fn-hp-x-put-lengths (j (car (car blocks))) (ws (cdr (car blocks))))
                                (:instance fn-hp-x-put-words (j (car (car blocks))) (ws (cdr (car blocks)))))
           :in-theory (disable fn-hp-x-put floor fn-hp-rep fn-hp-x-put-lengths fn-hp-x-put-words fn-hp-u64-listp nth))))
(local
 (defthm fn-hp-pages-agree-of-wreps
   (implies (and (natp a)
                 (equal (take 2048 (nthcdr a x)) (take 2048 (nthcdr a y))))
            (equal (take 2048 (nthcdr a (fn-hp-wreps x bs))) (take 2048 (nthcdr a (fn-hp-wreps y bs)))))
   :hints (("Goal" :use ((:instance fn-hp-agree-is-take (n 2048))
                         (:instance fn-hp-agree-is-take (n 2048) (x (fn-hp-wreps x bs)) (y (fn-hp-wreps y bs)))
                         (:instance fn-hp-agree-of-wreps (n 2048)))
            :in-theory (theory (quote minimal-theory))))
   :rule-classes nil))

(defthm fn-hp-vhold-of-wreps
  (implies (and (fn-hp-vhold p np pgs-mem iw)
                (equal (nth *pgs-wi* mem2) (fn-hp-wreps (nth *pgs-wi* pgs-mem) bs))
                (equal (nth *pgs-vi* mem2) (nth *pgs-vi* pgs-mem)))
           (fn-hp-vhold p np mem2 (fn-hp-wreps iw bs)))
  :hints (("Goal" :induct (fn-hp-vhold p np pgs-mem iw)
           :in-theory (e/d (pgs-vi) (fn-hp-wreps take nthcdr adt-nth-0)))
          ("Subgoal *1/2" :use ((:instance fn-hp-pages-agree-of-wreps (a (* 2048 (nfix p)))
                                           (x (nth *pgs-wi* pgs-mem)) (y iw))))))
(defun fn-hp-blocks-shape (blocks)
  (declare (xargs :guard t))
  (if (atom blocks) t
    (and (consp (car blocks)) (natp (car (car blocks))) (consp (cdr (car blocks)))
         (fn-hp-u64-listp (cdr (car blocks)))
         (fn-hp-blocks-shape (cdr blocks)))))

(defthm fn-hp-blocks-fit-when-ready
  (implies (and (equal (fn-hp-x-blocks-ready blocks pgs-mem) :ok) (fn-hp-blocks-shape blocks))
           (fn-hp-blocks-fit blocks (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-blocks-ready blocks pgs-mem)
           :in-theory (e/d (fn-hp-x-pool-ready-bound) (fn-hp-x-pool-ready floor)))))

(in-theory (disable fn-hp-blocks-fit-when-ready))

; K. The pages the writer marks dirty are in the proved dirty list, and
;    verified.

(defun fn-hp-blocks-pagep (p blocks)
  ; page P holds a word of some block
  (declare (xargs :verify-guards nil))
  (if (atom blocks) nil
    (or (let ((j (car (car blocks))) (ws (cdr (car blocks))))
          (and (consp ws) (<= (floor j 2048) p) (<= p (floor (+ j (len ws) -1) 2048))))
        (fn-hp-blocks-pagep p (cdr blocks)))))

(defthm fn-hp-x-put-blocks-dirty
  (implies (and (fn-hp-blocks-fit blocks (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)) (natp p)
                (equal (nth p (nth *pgs-di* (fn-hp-x-put-blocks blocks pgs-mem))) 1)
                (not (equal (nth p (nth *pgs-di* pgs-mem)) 1)))
           (fn-hp-blocks-pagep p blocks))
  :hints (("Goal" :induct (fn-hp-x-put-blocks blocks pgs-mem)
           :in-theory (disable fn-hp-x-put floor fn-hp-u64-listp))
          ("Subgoal *1/2" :use ((:instance fn-hp-x-put-lengths (j (car (car blocks))) (ws (cdr (car blocks))))
                                (:instance fn-hp-x-put-dirty (j (car (car blocks))) (ws (cdr (car blocks)))))
           :in-theory (disable fn-hp-x-put floor fn-hp-x-put-lengths fn-hp-u64-listp nth))))
(defthm fn-hp-vi-from-ready-range
  (implies (and (equal (fn-hp-x-ready-range lo hi pgs-mem) :ok) (natp lo) (natp p) (<= lo p) (< p (nfix hi)))
           (equal (pgs-vi p pgs-mem) 2))
  :hints (("Goal" :use ((:instance fn-hp-x-ready-range-each (p lo) (q p)) (:instance fn-hp-x-ready-ok))
           :in-theory (disable fn-hp-x-ready-range-each fn-hp-x-ready-ok fn-hp-x-ready fn-hp-x-ready-range))))

(local (defthm fn-hp-len-consp-pos (implies (consp x) (< 0 (len x))) :rule-classes :linear))

(defthm fn-hp-blocks-ready-verified
  (implies (and (equal (fn-hp-x-blocks-ready blocks pgs-mem) :ok) (fn-hp-blocks-pagep p blocks) (natp p)
                (fn-hp-blocks-shape blocks))
           (equal (pgs-vi p pgs-mem) 2))
  :hints (("Goal" :induct (fn-hp-x-blocks-ready blocks pgs-mem)
           :in-theory (e/d (fn-hp-x-pool-ready) (fn-hp-x-ready floor fn-hp-x-ready-range fn-hp-u64-listp)))))
