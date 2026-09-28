; fn: the history's rows read through the page store as the host calls it
; (lane arena-store-2, 2026-09-28).  Prefix fn-hp-.
;
; The reads return NEED-VERDICTS (coordinator decision 2026-09-28, (6)):
; they never fill a page; a page not yet verified answers `pgs-x-read''s
; shapes (:need-table T PHYS) / (:need-page P PHYS) and the host fills it
; with its two byte primitives, verifies it (`pgs-x-open-page' :eager, the
; digest against its table entry), and asks again.  So the open touches no
; row page; the first read of a row pays at most its four cells' pages and
; its pool entry's pages.
;
; KEYSTONE fn-hp-x-at-is-nth: over any page store state whose VERIFIED pages
; hold the image's words (`fn-hp-vhold'), an answer (VERDICT :ok) is the
; history's event at SEQ.
(in-package "ACL2")
(include-book "history-pages-row")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; D. The reads as the host calls them: need-verdicts, never a fill.

(defun fn-hp-starts-okp (starts)
  (declare (xargs :guard t))
  (and (nat-listp starts) (equal (len starts) 5)))

(defun fn-hp-x-cell (r seq starts pgs-mem)
  ; cell SEQ of column R: (mv VERDICT WORD); VERDICT :ok once its page is
  ; ready, else what the host serves first
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp r) (< r 5) (natp seq) (fn-hp-starts-okp starts))))
  (let* ((i (+ (* 2048 (nfix (nth r starts))) seq))
         (v (fn-hp-x-ready (floor i 2048) pgs-mem)))
    (cond ((not (eq v :ok)) (mv v 0))
          ((not (< i (pgs-w-length pgs-mem))) (mv :out-of-range 0))
          (t (mv :ok (pgs-wi i pgs-mem))))))


(defthm fn-hp-x-cell-natp
  (implies (and (pgs-memp pgs-mem) (natp seq)) (natp (mv-nth 1 (fn-hp-x-cell r seq starts pgs-mem))))
  :rule-classes :type-prescription)


(defthm fn-hp-starts-okp-true-listp
  (implies (fn-hp-starts-okp s) (true-listp s))
  :rule-classes :forward-chaining)


(defthm fn-hp-x-ready-range-ok
  (implies (and (equal (fn-hp-x-ready-range p hi pgs-mem) :ok) (natp p) (natp hi) (< p hi))
           (<= (* 2048 hi) (pgs-w-length pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-ready-range p hi pgs-mem)))
  :rule-classes nil)

(defun fn-hp-pool-lo (off starts)
  ; the first word of the pool entry at octet OFFSET OFF
  (declare (xargs :guard (and (natp off) (fn-hp-starts-okp starts))))
  (+ (* 2048 (nfix (nth 4 starts))) (floor (nfix off) 8)))

(defun fn-hp-x-pool-ready (lo k pgs-mem)
  ; every page of words LO .. LO+K-1 ready (K > 0)
  (declare (xargs :stobjs pgs-mem :guard (and (natp lo) (natp k))))
  (fn-hp-x-ready-range (floor lo 2048) (+ 1 (floor (+ lo k -1) 2048)) pgs-mem))

(defthm fn-hp-x-pool-ready-bound
  (implies (and (equal (fn-hp-x-pool-ready lo k pgs-mem) :ok) (natp lo) (posp k))
           (<= (+ lo k) (pgs-w-length pgs-mem)))
  :hints (("Goal" :in-theory (disable floor)
           :use ((:instance fn-hp-x-ready-range-ok (p (floor lo 2048)) (hi (+ 1 (floor (+ lo k -1) 2048))))
                 (:instance fn-hp-page-start-below-word (w lo))
                 (:instance fn-hp-word-below-next-page (w (+ lo k -1)))
                 (:instance fn-hp-page-start-below-word (w (+ lo k -1)))
                 (:instance fn-hp-word-below-next-page (w lo))))))

(defun fn-hp-x-at (seq salt n lens starts pgs-mem)
  ; The event at SEQ, as the host calls it: (mv VERDICT RESULT).  VERDICT
  ; :ok and RESULT (:ok EV) or (:refused REASON) once every page the row
  ; touches is ready (its four cells' pages and its pool entry's pages);
  ; else VERDICT is what the host serves (a fill, then it asks again).
  ; N, LENS, STARTS: the open's header answer.  Changes nothing.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp seq) (natp n) (true-listp lens) (fn-hp-starts-okp starts))
                  :guard-hints (("Goal" :in-theory (disable fn-hp-x-cell fn-hp-x-ready fn-hp-x-pool-ready
                                                            fn-hp-at-core floor mod fn-hp-starts-okp nth)))))
  (if (not (< seq n))
      (mv :ok (list :refused :seq))
    (mv-let (v0 mkey) (fn-hp-x-cell 0 seq starts pgs-mem)
      (mv-let (v1 tl) (fn-hp-x-cell 1 seq starts pgs-mem)
        (mv-let (v2 off) (fn-hp-x-cell 2 seq starts pgs-mem)
          (mv-let (v3 plen) (fn-hp-x-cell 3 seq starts pgs-mem)
            (cond ((not (eq v0 :ok)) (mv v0 nil))
                  ((not (eq v1 :ok)) (mv v1 nil))
                  ((not (eq v2 :ok)) (mv v2 nil))
                  ((not (eq v3 :ok)) (mv v3 nil))
                  ((not (and (equal (mod off 8) 0) (equal (mod plen 8) 0) (<= tl plen)
                             (<= (+ off plen) (nfix (nth 4 lens))) (< 0 plen)))
                   (mv :ok (fn-hp-at-core seq n lens salt mkey tl off plen nil)))
                  (t
                   (let* ((lo (fn-hp-pool-lo off starts))
                          (k (floor plen 8))
                          (v (fn-hp-x-pool-ready lo k pgs-mem)))
                     (cond ((not (eq v :ok)) (mv v nil))
                           ((not (<= (+ lo k) (pgs-w-length pgs-mem))) (mv :out-of-range nil))
                           (t (mv :ok (fn-hp-at-core seq n lens salt mkey tl off plen
                                                     (fn-hp-x-words lo k pgs-mem))))))))))))))


; The read against the verified pages.

(defun-nx fn-hp-vhold (p np pgs-mem iw)
  ; every VERIFIED page P..NP-1 of the store holds the image's words IW there
  (declare (xargs :measure (nfix (- (nfix np) (nfix p)))))
  (if (zp (- (nfix np) (nfix p)))
      t
    (and (implies (equal (pgs-vi p pgs-mem) 2)
                  (equal (take 2048 (nthcdr (* 2048 (nfix p)) (nth *pgs-wi* pgs-mem)))
                         (take 2048 (nthcdr (* 2048 (nfix p)) iw))))
         (fn-hp-vhold (+ 1 (nfix p)) np pgs-mem iw))))

(local
 (defthm fn-hp-nth-of-take-nthcdr
   (implies (and (natp a) (natp j) (< j k) (natp k))
            (equal (nth j (take k (nthcdr a x))) (nth (+ a j) x)))
   :hints (("Goal" :in-theory (enable nth take nthcdr)))))

(defthm fn-hp-vhold-page
  (implies (and (fn-hp-vhold p np pgs-mem iw) (natp p) (natp q) (<= p q) (< q (nfix np))
                (equal (pgs-vi q pgs-mem) 2))
           (equal (take 2048 (nthcdr (* 2048 q) (nth *pgs-wi* pgs-mem)))
                  (take 2048 (nthcdr (* 2048 q) iw))))
  :hints (("Goal" :induct (fn-hp-vhold p np pgs-mem iw) :in-theory (disable take nthcdr))))

(defthm fn-hp-vhold-word
  (implies (and (fn-hp-vhold p np pgs-mem iw) (natp p) (natp q) (<= p q) (< q (nfix np))
                (equal (pgs-vi q pgs-mem) 2) (natp j) (< j 2048))
           (equal (nth (+ (* 2048 q) j) (nth *pgs-wi* pgs-mem)) (nth (+ (* 2048 q) j) iw)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-vhold-page)
                 (:instance fn-hp-nth-of-take-nthcdr (a (* 2048 q)) (k 2048) (x (nth *pgs-wi* pgs-mem)))
                 (:instance fn-hp-nth-of-take-nthcdr (a (* 2048 q)) (k 2048) (x iw)))
           :in-theory (disable fn-hp-vhold-page fn-hp-nth-of-take-nthcdr fn-hp-vhold take nthcdr))))
(defthm fn-hp-vhold-index
  (implies (and (fn-hp-vhold 0 np pgs-mem iw) (natp i) (< (floor i 2048) (nfix np))
                (equal (pgs-vi (floor i 2048) pgs-mem) 2))
           (equal (nth i (nth *pgs-wi* pgs-mem)) (nth i iw)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-vhold-word (p 0) (q (floor i 2048)) (j (mod i 2048))))
           :in-theory (disable fn-hp-vhold-word fn-hp-vhold))))

(defthm fn-hp-x-ready-range-each
  (implies (and (equal (fn-hp-x-ready-range p hi pgs-mem) :ok) (natp p) (natp q) (<= p q) (< q (nfix hi)))
           (equal (fn-hp-x-ready q pgs-mem) :ok))
  :hints (("Goal" :induct (fn-hp-x-ready-range p hi pgs-mem) :in-theory (disable fn-hp-x-ready))))
(defthm fn-hp-floor-in-pages
  (implies (and (natp i) (natp p) (natp h) (<= (* 2048 p) i) (< i (* 2048 h)))
           (and (<= p (floor i 2048)) (< (floor i 2048) h)))
  :hints (("Goal" :use ((:instance fn-hp-word-below-next-page (w i))
                        (:instance fn-hp-page-start-below-word (w i)))
           :in-theory (disable floor)))
  :rule-classes nil)

(defthm fn-hp-x-words-from-ready
  (implies (and (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw) (natp lo) (natp k) (natp p) (natp h)
                (equal (fn-hp-x-ready-range p h pgs-mem) :ok)
                (<= (* 2048 p) lo) (<= (+ lo k) (* 2048 h)))
           (equal (fn-hp-x-words lo k pgs-mem) (take k (nthcdr lo iw))))
  :hints (("Goal" :induct (fn-hp-x-words lo k pgs-mem)
           :in-theory (e/d (take nthcdr) (fn-hp-x-ready fn-hp-x-ready-range fn-hp-vhold floor)))
          ("Subgoal *1/2" :use ((:instance fn-hp-floor-in-pages (i lo))
                                (:instance fn-hp-x-ready-range-each (q (floor lo 2048)))
                                (:instance fn-hp-x-ready-ok (p (floor lo 2048)))
                                (:instance fn-hp-vhold-index (i lo) (np (pgs-v-length pgs-mem)))))))
(defthm fn-hp-x-cell-from-ready
  (implies (and (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw) (natp seq)
                (equal (mv-nth 0 (fn-hp-x-cell r seq starts pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-cell r seq starts pgs-mem))
                  (nth (+ (* 2048 (nfix (nth r starts))) seq) iw)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-ready-ok (p (floor (+ (* 2048 (nfix (nth r starts))) seq) 2048)))
                 (:instance fn-hp-vhold-index (i (+ (* 2048 (nfix (nth r starts))) seq)) (np (pgs-v-length pgs-mem))))
           :in-theory (e/d (pgs-wi) (fn-hp-x-ready fn-hp-vhold fn-hp-x-ready-ok fn-hp-vhold-index floor)))))

(defthm fn-hp-x-words-from-pool-ready
  (implies (and (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem iw) (natp lo) (posp k)
                (equal (fn-hp-x-pool-ready lo k pgs-mem) :ok))
           (equal (fn-hp-x-words lo k pgs-mem) (take k (nthcdr lo iw))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-words-from-ready (p (floor lo 2048)) (h (+ 1 (floor (+ lo k -1) 2048))))
                 (:instance fn-hp-page-start-below-word (w lo))
                 (:instance fn-hp-word-below-next-page (w (+ lo k -1))))
           :in-theory (disable fn-hp-x-words-from-ready fn-hp-x-words fn-hp-x-ready-range fn-hp-vhold floor))))

(defthm fn-hp-x-at-ok-cells
  (implies (and (natp seq) (natp n) (< seq n)
                (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem)) :ok))
           (and (equal (mv-nth 0 (fn-hp-x-cell 0 seq starts pgs-mem)) :ok)
                (equal (mv-nth 0 (fn-hp-x-cell 1 seq starts pgs-mem)) :ok)
                (equal (mv-nth 0 (fn-hp-x-cell 2 seq starts pgs-mem)) :ok)
                (equal (mv-nth 0 (fn-hp-x-cell 3 seq starts pgs-mem)) :ok)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hp-x-cell fn-hp-x-pool-ready fn-hp-x-words fn-hp-at-core fn-hp-pool-lo floor mod mv-nth))))

(defthm fn-hp-x-at-ok-pool
  (implies (and (natp seq) (natp n) (< seq n)
                (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem)) :ok)
                (equal off (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)))
                (equal plen (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)))
                (equal (mod off 8) 0) (equal (mod plen 8) 0)
                (<= (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem)) plen)
                (<= (+ off plen) (nfix (nth 4 lens))) (< 0 plen))
           (and (equal (fn-hp-x-pool-ready (fn-hp-pool-lo off starts) (floor plen 8) pgs-mem) :ok)
                (equal (mv-nth 1 (fn-hp-x-at seq salt n lens starts pgs-mem))
                       (fn-hp-at-core seq n lens salt
                                      (mv-nth 1 (fn-hp-x-cell 0 seq starts pgs-mem))
                                      (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem)) off plen
                                      (fn-hp-x-words (fn-hp-pool-lo off starts) (floor plen 8) pgs-mem)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hp-x-cell fn-hp-x-pool-ready fn-hp-x-words fn-hp-at-core fn-hp-pool-lo floor mod))))

(defthm fn-hp-x-at-ok-nopool
  (implies (and (natp seq) (natp n) (< seq n)
                (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem)) :ok)
                (not (and (equal (mod (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)) 8) 0)
                          (equal (mod (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)) 8) 0)
                          (<= (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem)) (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)))
                          (<= (+ (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)) (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)))
                              (nfix (nth 4 lens)))
                          (< 0 (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem))))))
           (equal (mv-nth 1 (fn-hp-x-at seq salt n lens starts pgs-mem))
                  (fn-hp-at-core seq n lens salt
                                 (mv-nth 1 (fn-hp-x-cell 0 seq starts pgs-mem))
                                 (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem))
                                 (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem))
                                 (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-hp-x-cell fn-hp-x-pool-ready fn-hp-x-words fn-hp-at-core fn-hp-pool-lo floor mod))))

(defthm fn-hp-consp-program
  (consp (fn-scc-program x))
  :hints (("Goal" :in-theory (enable fn-scc-program fn-scc-atom-octets))))

(defthm fn-hp-len-pe-pos
  (< 0 (len (fn-hp-pe ev)))
  :hints (("Goal" :in-theory (enable fn-hp-pe fn-hp-pad8)))
  :rule-classes :linear)

(local
 (defthm fn-hp-natp-nth-nat-listp
   (implies (and (nat-listp l) (natp r) (< r (len l))) (natp (nth r l)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-hp-nfix-nth-starts
  (implies (and (fn-hp-starts-okp starts) (natp r) (< r 5)) (equal (nfix (nth r starts)) (nth r starts)))
  :hints (("Goal" :use ((:instance fn-hp-natp-nth-nat-listp (l starts))) :in-theory (disable fn-hp-natp-nth-nat-listp))))

(local
 (defthm fn-hp-nat-listp-starts-l
   (implies (natp s) (nat-listp (adt-starts-l lens s)))))

(defthm fn-hp-starts-okp-of-starts
  (fn-hp-starts-okp (fn-hp-starts h salt))
  :hints (("Goal" :in-theory (disable fn-hp-lens adt-starts-l))))

(defthm fn-hp-floor-pe-posp
  (posp (floor (len (fn-hp-pe ev)) 8))
  :hints (("Goal" :use ((:instance fn-hp-floor-8-exact (x (len (fn-hp-pe ev))))
                        (:instance fn-hp-pe-mod-8) (:instance fn-hp-len-pe-pos))
           :in-theory (disable fn-hp-floor-8-exact fn-hp-pe-mod-8 fn-hp-len-pe-pos floor mod)))
  :rule-classes :type-prescription)

(defthm fn-hp-pes-len-natp (natp (fn-hp-pes-len h)) :rule-classes :type-prescription)

(defthm fn-hp-x-cell-of-image
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)) (natp r) (< r 4)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                (equal (mv-nth 0 (fn-hp-x-cell r seq (fn-hp-starts h salt) pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-cell r seq (fn-hp-starts h salt) pgs-mem))
                  (nth r (fn-hp-cells-of (nth seq h) salt (fn-hp-pes-len (take seq h))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-cell-from-ready (starts (fn-hp-starts h salt)) (iw (fn-hp-iw h salt)))
                 (:instance fn-hp-nfix-nth-starts (starts (fn-hp-starts h salt)))
                 (:instance fn-hp-iw-cell (i seq)))
           :in-theory (disable fn-hp-x-cell-from-ready fn-hp-nfix-nth-starts fn-hp-iw-cell fn-hp-x-cell
                               fn-hp-iw fn-hp-okp fn-hp-starts fn-hp-vhold fn-hp-cells-of))))


(defthm fn-hp-x-cells-of-image
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h))
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) lens (fn-hp-starts h salt) pgs-mem)) :ok))
           (and (equal (mv-nth 1 (fn-hp-x-cell 0 seq (fn-hp-starts h salt) pgs-mem)) (fn-hp-mkey (nth seq h) salt))
                (equal (mv-nth 1 (fn-hp-x-cell 1 seq (fn-hp-starts h salt) pgs-mem)) (len (fn-scc-encode (nth seq h))))
                (equal (mv-nth 1 (fn-hp-x-cell 2 seq (fn-hp-starts h salt) pgs-mem)) (fn-hp-pes-len (take seq h)))
                (equal (mv-nth 1 (fn-hp-x-cell 3 seq (fn-hp-starts h salt) pgs-mem)) (len (fn-hp-pe (nth seq h))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-at-ok-cells (n (len h)) (starts (fn-hp-starts h salt)))
                 (:instance fn-hp-x-cell-of-image (r 0)) (:instance fn-hp-x-cell-of-image (r 1))
                 (:instance fn-hp-x-cell-of-image (r 2)) (:instance fn-hp-x-cell-of-image (r 3))
                 (:instance fn-hp-cells-of-is (ev (nth seq h)) (pos (fn-hp-pes-len (take seq h)))))
           :in-theory (union-theories '(car-cons cdr-cons nth-0-cons nth-add1 natp zp (:e zp) (:e natp) (:e <) (:e nth)
                                         (:e len) nth len (:e car) (:e cdr) (:t len) fn-hp-pes-len-natp nfix (:e nfix))
                                      (theory 'minimal-theory)))))

(defthm fn-hp-floor-8-natp (implies (natp x) (natp (floor x 8))) :rule-classes :type-prescription)

(defthm fn-hp-floor-8-nonneg (implies (natp x) (<= 0 (floor x 8))) :rule-classes :linear)

; KEYSTONE (the row read, m2): whenever the read the host calls answers
; (VERDICT :ok), its answer is the history's event at SEQ -- over ANY page
; store state whose VERIFIED pages hold the image's words.  A page not yet
; verified is never read: the read answers a need-verdict instead, and the
; host's fill + `pgs-x-open-page' check is where a page becomes verified.
(defthm fn-hp-x-at-is-nth
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h))
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) pgs-mem))
                  (list :ok (nth seq h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-cells-of-image (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-x-at-ok-pool (n (len h)) (lens (fn-hp-lens h salt)) (starts (fn-hp-starts h salt))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h)))))
                 (:instance fn-hp-x-words-from-pool-ready (iw (fn-hp-iw h salt))
                            (lo (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take seq h)) 8)))
                            (k (floor (len (fn-hp-pe (nth seq h))) 8)))
                 (:instance fn-hp-nfix-nth-starts (r 4) (starts (fn-hp-starts h salt)))
                 (:instance fn-hp-starts-okp-of-starts)
                 (:instance fn-hp-at-core-when (n (len h)) (lens (fn-hp-lens h salt)) (ev (nth seq h))
                            (mkey (fn-hp-mkey (nth seq h) salt)) (tl (len (fn-scc-encode (nth seq h))))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h))))
                            (pw (take (floor (len (fn-hp-pe (nth seq h))) 8)
                                      (nthcdr (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take seq h)) 8))
                                              (fn-hp-iw h salt))))
                            (bytes (fn-hp-pe (nth seq h))))
                 (:instance fn-hp-iw-pool (i seq))
                 (:instance fn-hp-evp-nth (i seq))
                 (:instance fn-hp-take-of-pe (ev (nth seq h)))
                 (:instance fn-hp-pe-def (ev (nth seq h)))
                 (:instance fn-hp-decode-enc (ev (nth seq h)))
                 (:instance fn-hp-lens-4)
                 (:instance fn-hp-pes-len-take-bound (i seq))
                 (:instance fn-hp-pes-len-mod-8 (h (take seq h)))
                 (:instance fn-hp-pe-mod-8 (ev (nth seq h)))
                 (:instance fn-hp-len-pe-pos (ev (nth seq h)))
                 (:instance fn-hp-floor-pe-posp (ev (nth seq h)))
                 (:instance fn-hp-len-enc-le-pe (ev (nth seq h))))
           :in-theory (union-theories '(fn-hp-pool-lo nfix natp posp fn-hp-pes-len-natp (:t len) (:e <) (:e natp)
                                        (:t floor) fn-hp-okp-events fn-hp-floor-8-natp fn-hp-floor-8-nonneg)
                                      (theory 'minimal-theory)))))

; KEYSTONE (the open's header, over verified pages): once page 0 is ready
; (verdict :ok), the header check answers the history's N and regions over
; any state whose verified pages hold the image; the open reads page 0 and
; nothing else.
(defthm fn-hp-x-header-is-image
  (implies (and (fn-hp-okp h salt) (equal npages (fn-hp-npages h salt))
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-iw h salt))
                (equal (mv-nth 0 (fn-hp-x-header npages pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-header npages pgs-mem))
                  (list :ok (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-header-of-image)
                 (:instance fn-hp-vhold-page (p 0) (q 0) (np (pgs-v-length pgs-mem)) (iw (fn-hp-iw h salt)))
                 (:instance fn-hp-x-ready-ok (p 0)))
           :in-theory (disable fn-hp-x-header-of-image fn-hp-vhold-page fn-hp-x-ready-ok fn-hp-vhold
                               fn-hp-iw fn-hp-okp fn-hp-npages fn-hp-lens fn-hp-starts fn-hp-x-ready fn-hp-w-header
                               fn-hp-x-words take))))

; An executable twin of `fn-hp-vhold' over the stobj as a list (for ground
; witnesses; no host calls either).
(defun fn-hp-vhold-x (p np mem iw)
  (declare (xargs :measure (nfix (- (nfix np) (nfix p))) :verify-guards nil))
  (if (zp (- (nfix np) (nfix p)))
      t
    (and (implies (equal (nth p (nth *pgs-vi* mem)) 2)
                  (equal (take 2048 (nthcdr (* 2048 (nfix p)) (nth *pgs-wi* mem)))
                         (take 2048 (nthcdr (* 2048 (nfix p)) iw))))
         (fn-hp-vhold-x (+ 1 (nfix p)) np mem iw))))

(defthmd fn-hp-vhold-is-x
  (equal (fn-hp-vhold p np pgs-mem iw) (fn-hp-vhold-x p np pgs-mem iw))
  :hints (("Goal" :in-theory (e/d (pgs-vi) (take nthcdr)) :induct (fn-hp-vhold-x p np pgs-mem iw)
           :expand ((fn-hp-vhold p np pgs-mem iw) (fn-hp-vhold-x p np pgs-mem iw)))))
