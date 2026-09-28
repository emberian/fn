; fn: the history's rows read back from the image's words, and the open's
; header check as the host calls it (lane arena-store-2, 2026-09-28).
; Prefix fn-hp-.  Split from books/history-pages-exec.lisp (certification
; time).
(in-package "ACL2")
(include-book "history-pages-exec")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-scc-octet-listp)
                          (:rewrite fn-scc-octet-listp-facts . 1)
                          (:rewrite fn-scc-octet-listp-facts . 2)
                          (:rewrite fn-scc-octet-listp-true)
                          (:rewrite fn-sccb-scc-octetp-is-cbor-octetp)
                          (:rewrite pgs-x-nfix-when-natp))))

(local
 (defun fn-hp-tt-ind (n l y)
   (if (or (zp n) (zp l)) (list n l y) (fn-hp-tt-ind (1- n) (1- l) (cdr y)))))

(local
 (defthm fn-hp-take-take-below
   (implies (and (natp n) (natp l) (<= n l))
            (equal (take n (take l y)) (take n y)))
   :hints (("Goal" :in-theory (enable take) :induct (fn-hp-tt-ind n l y)))))

(local
 (defthm fn-hp-natp-nth-starts-l
   (implies (and (nat-listp lens) (natp s) (natp r) (< r (len lens)))
            (natp (nth r (adt-starts-l lens s))))
   :hints (("Goal" :in-theory (enable nth)))))

; -----------------------------------------------------------------------------
; C. The row reader over the words: the event at SEQ.

(defthm fn-hp-evp-nth
  (implies (and (fn-hp-events-okp h) (natp i) (< i (len h)))
           (fn-hp-evp (nth i h)))
  :hints (("Goal" :in-theory (e/d (nth) (fn-hp-evp)))))

(defthm fn-hp-len-pad8
  (equal (len (fn-hp-pad8 x)) (+ (len x) (fn-hp-pad8-count (len x))))
  :hints (("Goal" :in-theory (enable fn-hp-pad8))))

(defthm fn-hp-pe-mod-8
  (equal (mod (len (fn-hp-pe ev)) 8) 0)
  :hints (("Goal" :in-theory (e/d (fn-hp-pe) (mod))
           :use ((:instance fn-hp-pad-to-8 (n (len (fn-scc-encode ev))))))))

(defthm fn-hp-pes-len-mod-8
  (equal (mod (fn-hp-pes-len h) 8) 0)
  :hints (("Goal" :in-theory (disable fn-hp-pe-mod-8 mod) :induct (fn-hp-pes-len h))
          ("Subgoal *1/2" :use ((:instance fn-hp-pe-mod-8 (ev (car h)))
                                (:instance fn-hp-mod-8-sum (x (len (fn-hp-pe (car h)))) (y (fn-hp-pes-len (cdr h))))))))

(defthm fn-hp-lens-4
  (equal (nth 4 (fn-hp-lens h salt)) (fn-hp-pes-len h))
  :hints (("Goal" :in-theory (e/d (adt-regs) (fn-hp-rows)))))

(defthm fn-hp-take-of-pe
  (implies (fn-hp-evp ev)
           (equal (take (len (fn-scc-encode ev)) (fn-hp-pe ev)) (fn-scc-encode ev)))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe fn-hp-pad8) (fn-scc-encode)))))

(defthm fn-hp-len-enc-le-pe
  (<= (len (fn-scc-encode ev)) (len (fn-hp-pe ev)))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe fn-hp-pad8) (fn-scc-encode))))
  :rule-classes :linear)

(defthm fn-hp-pe-is-pad8
  (equal (fn-hp-pad8 (fn-scc-encode ev)) (fn-hp-pe ev))
  :hints (("Goal" :in-theory (enable fn-hp-pe))))

(defthm fn-hp-decode-enc
  (implies (fn-hp-evp ev)
           (equal (fn-scc-decode-tree (fn-scc-encode ev)) (list :ok ev)))
  :hints (("Goal" :use ((:instance fn-scc-decode-tree-of-encode (x ev)))
           :in-theory (disable fn-scc-decode-tree-of-encode fn-scc-decode-tree fn-scc-encode))))

(defun fn-hp-w-at (seq w salt n lens starts)
  ; the event at SEQ read from the image's words W, given the header's N,
  ; LENS and STARTS: (:ok EV) or (:refused REASON)
  (declare (xargs :verify-guards nil))
  (let* ((mkey (nth (+ (* 2048 (nth 0 starts)) seq) w))
         (tl (nth (+ (* 2048 (nth 1 starts)) seq) w))
         (off (nth (+ (* 2048 (nth 2 starts)) seq) w))
         (plen (nth (+ (* 2048 (nth 3 starts)) seq) w)))
    (cond ((not (and (natp seq) (< seq (nfix n)))) (list :refused :seq))
          ((not (and (natp off) (natp plen) (natp tl) (equal (mod off 8) 0) (equal (mod plen 8) 0)
                     (<= tl plen) (<= (+ off plen) (nfix (nth 4 lens)))))
           (list :refused :cells))
          (t (let ((bytes (pgs-words-le-octets
                           (take (floor plen 8) (nthcdr (+ (* 2048 (nth 4 starts)) (floor off 8)) w)))))
               (if (not (equal bytes (fn-hp-pad8 (take tl bytes))))
                   (list :refused :padding)
                 (let ((d (fn-scc-decode-tree (take tl bytes))))
                   (cond ((not (eq (car d) :ok)) (list :refused :tree))
                         ((not (equal mkey (fn-hp-mkey (cadr d) salt))) (list :refused :mkey))
                         (t d)))))))))

(local
 (defthm fn-hp-octetsp-meta
   (adt-octetsp (adt-meta starts lens))
   :hints (("Goal" :in-theory (enable adt-meta)))))

(defthm fn-hp-octetsp-header
  (adt-octetsp (adt-header *fn-hp-schema* n regs))
  :hints (("Goal" :in-theory (e/d (adt-header adt-header-content adt-hdr-const (:executable-counterpart adt-hdr-const))
                                  (adt-zeros adt-le)))))

(local
 (defthm fn-hp-octetsp-col-regs
   (adt-all-octetsp (adt-col-regs ws cols))
   :hints (("Goal" :in-theory (enable adt-all-octetsp)))))

(local
 (defthm fn-hp-all-octetsp-append
   (implies (and (adt-all-octetsp x) (adt-all-octetsp y)) (adt-all-octetsp (append x y)))
   :hints (("Goal" :in-theory (enable adt-all-octetsp)))))


(local
 (defthm fn-hp-octetsp-of-scc-octets-x
   (implies (fn-scc-octet-listp x) (adt-octetsp x))))

(defthm fn-hp-octetsp-pe
  (implies (fn-hp-evp ev) (adt-octetsp (fn-hp-pe ev)))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe) (fn-scc-program)))))

(defthm fn-hp-octetsp-pes
  (implies (fn-hp-events-okp h) (adt-octetsp (fn-hp-pes h)))
  :hints (("Goal" :in-theory (disable fn-hp-evp))))

(defthm fn-hp-octetsp-image
  (implies (fn-hp-events-okp h) (adt-octetsp (fn-hp-image h salt)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (adt-ser adt-regs adt-all-octetsp) (adt-ser-is-header-body adt-header fn-hp-rows)))))

(defthm fn-hp-len-image
  (equal (len (fn-hp-image h salt)) (* 16384 (fn-hp-npages h salt)))
  :hints (("Goal" :in-theory (disable adt-ser adt-regs fn-hp-rows adt-end-is-end-l))))

(defthm fn-hp-npages-is-end-l
  (equal (fn-hp-npages h salt) (adt-end-l (fn-hp-lens h salt) 1))
  :hints (("Goal" :in-theory (disable adt-regs fn-hp-rows))))

(defthm fn-hp-nat-listp-lens
  (nat-listp (fn-hp-lens h salt)))

(defthm fn-hp-iw-cell
  (implies (and (fn-hp-okp h salt) (natp r) (< r 4) (natp i) (< i (len h)))
           (equal (nth (+ (* 2048 (nth r (fn-hp-starts h salt))) i) (fn-hp-iw h salt))
                  (nth r (fn-hp-cells-of (nth i h) salt (fn-hp-pes-len (take i h))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-iw-word (j (+ (* 2048 (nth r (fn-hp-starts h salt))) i)))
                 (:instance fn-hp-col-octets)
                 (:instance fn-hp-region-within-end (lens (fn-hp-lens h salt)) (start 1))
                 (:instance fn-hp-lens-col-sizes)
                 (:instance fn-hp-natp-nth-starts-l (lens (fn-hp-lens h salt)) (s 1))
                 (:instance fn-hp-starts-is))
           :in-theory (disable fn-hp-iw-word fn-hp-col-octets fn-hp-region-within-end fn-hp-lens-col-sizes
                               fn-hp-natp-nth-starts-l fn-hp-iw fn-hp-image fn-hp-okp fn-hp-cells-of
                               fn-hp-starts fn-hp-lens fn-hp-npages adt-unle adt-starts-l adt-end-l))))

(defthm fn-hp-octetsp-nthcdr-x
  (implies (adt-octetsp b) (adt-octetsp (nthcdr n b)))
  :hints (("Goal" :in-theory (enable nthcdr))))
(defthm fn-hp-words-slice
  (implies (and (natp e) (adt-octetsp b) (equal (len b) (* 16384 e)) (natp s) (natp o) (natp p)
                (equal (mod o 8) 0) (equal (mod p 8) 0) (<= (+ (* 16384 s) o p) (* 16384 e)))
           (equal (pgs-words-le-octets (take (floor p 8) (nthcdr (+ (* 2048 s) (floor o 8)) (fn-hp-pack8 (* 2048 e) b))))
                  (take p (nthcdr (+ (* 16384 s) o) b))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-floor-8-exact (x o)) (:instance fn-hp-floor-8-exact (x p))
                 (:instance fn-hp-nthcdr-pack8 (m (+ (* 2048 s) (floor o 8))) (n (* 2048 e)))
                 (:instance fn-hp-take-pack8 (m (floor p 8)) (n (- (* 2048 e) (+ (* 2048 s) (floor o 8))))
                            (b (nthcdr (* 8 (+ (* 2048 s) (floor o 8))) b)))
                 (:instance fn-hp-words-le-octets-of-pack8 (n (floor p 8)) (b (nthcdr (* 8 (+ (* 2048 s) (floor o 8))) b))))
           :in-theory (disable floor mod fn-hp-floor-8-exact fn-hp-nthcdr-pack8 fn-hp-take-pack8
                               fn-hp-words-le-octets-of-pack8 pgs-words-le-octets fn-hp-pack8))))

(defthm fn-hp-okp-events
  (implies (fn-hp-okp h salt) (fn-hp-events-okp h))
  :rule-classes :forward-chaining)

(defthm fn-hp-iw-pool
  (implies (and (fn-hp-okp h salt) (natp i) (< i (len h)))
           (equal (pgs-words-le-octets
                   (take (floor (len (fn-hp-pe (nth i h))) 8)
                         (nthcdr (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take i h)) 8))
                                 (fn-hp-iw h salt))))
                  (fn-hp-pe (nth i h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-pool-octets) (:instance fn-hp-octetsp-image)
                 (:instance fn-hp-region-within-end (lens (fn-hp-lens h salt)) (start 1) (r 4))
                 (:instance fn-hp-pes-len-take-bound)
                 (:instance fn-hp-natp-start-4)
                 (:instance fn-hp-starts-is)
                 (:instance fn-hp-words-slice (e (fn-hp-npages h salt)) (b (fn-hp-image h salt))
                            (s (nth 4 (fn-hp-starts h salt))) (o (fn-hp-pes-len (take i h)))
                            (p (len (fn-hp-pe (nth i h))))))
           :in-theory (disable fn-hp-pool-octets fn-hp-region-within-end fn-hp-pes-len-take-bound fn-hp-natp-start-4
                               fn-hp-words-slice floor mod
                               fn-hp-image fn-hp-okp fn-hp-starts fn-hp-lens fn-hp-npages adt-starts-l adt-end-l
                               fn-hp-pes-len pgs-words-le-octets fn-hp-pack8))))

(defthmd fn-hp-cells-of-is
  (equal (fn-hp-cells-of ev salt pos)
         (list (fn-hp-mkey ev salt) (len (fn-scc-encode ev)) (nfix pos) (len (fn-hp-pe ev))))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe) (fn-scc-encode fn-hp-len-pad8)))))

(defthm fn-hp-w-at-when
  (implies (and (natp seq) (< seq (nfix n))
                (equal (nth (+ (* 2048 (nth 0 starts)) seq) w) k)
                (equal (nth (+ (* 2048 (nth 1 starts)) seq) w) tl)
                (equal (nth (+ (* 2048 (nth 2 starts)) seq) w) off)
                (equal (nth (+ (* 2048 (nth 3 starts)) seq) w) plen)
                (natp off) (natp plen) (natp tl) (equal (mod off 8) 0) (equal (mod plen 8) 0)
                (<= tl plen) (<= (+ off plen) (nfix (nth 4 lens)))
                (equal (pgs-words-le-octets (take (floor plen 8) (nthcdr (+ (* 2048 (nth 4 starts)) (floor off 8)) w)))
                       bytes)
                (equal bytes (fn-hp-pad8 (take tl bytes)))
                (equal (fn-scc-decode-tree (take tl bytes)) (list :ok ev))
                (equal k (fn-hp-mkey ev salt)))
           (equal (fn-hp-w-at seq w salt n lens starts) (list :ok ev)))
  :hints (("Goal" :in-theory (disable fn-hp-mkey fn-scc-decode-tree pgs-words-le-octets floor mod take nthcdr nth))))

(defthmd fn-hp-pe-def
  (equal (fn-hp-pe ev) (fn-hp-pad8 (fn-scc-encode ev)))
  :hints (("Goal" :in-theory (enable fn-hp-pe))))

(defthm fn-hp-w-at-of-image
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)))
           (equal (fn-hp-w-at seq (fn-hp-iw h salt) salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))
                  (list :ok (nth seq h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-w-at-when (w (fn-hp-iw h salt)) (n (len h)) (lens (fn-hp-lens h salt))
                            (starts (fn-hp-starts h salt)) (ev (nth seq h))
                            (k (fn-hp-mkey (nth seq h) salt)) (tl (len (fn-scc-encode (nth seq h))))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h))))
                            (bytes (fn-hp-pe (nth seq h))))
                 (:instance fn-hp-iw-cell (r 0) (i seq)) (:instance fn-hp-iw-cell (r 1) (i seq))
                 (:instance fn-hp-iw-cell (r 2) (i seq)) (:instance fn-hp-iw-cell (r 3) (i seq))
                 (:instance fn-hp-cells-of-is (ev (nth seq h)) (pos (fn-hp-pes-len (take seq h))))
                 (:instance fn-hp-iw-pool (i seq))
                 (:instance fn-hp-evp-nth (i seq))
                 (:instance fn-hp-pes-len-take-bound (i seq))
                 (:instance fn-hp-pes-len-mod-8 (h (take seq h)))
                 (:instance fn-hp-pe-mod-8 (ev (nth seq h)))
                 (:instance fn-hp-take-of-pe (ev (nth seq h)))
                 (:instance fn-hp-pe-def (ev (nth seq h)))
                 (:instance fn-hp-decode-enc (ev (nth seq h)))
                 (:instance fn-hp-len-enc-le-pe (ev (nth seq h))))
           :in-theory (theory 'minimal-theory))
          ("Goal'" :in-theory (e/d (fn-hp-lens-4) (fn-hp-w-at fn-hp-iw fn-hp-image fn-hp-okp fn-hp-starts fn-hp-lens
                                   fn-hp-npages fn-hp-pes-len fn-hp-pe fn-scc-encode fn-scc-decode-tree fn-hp-evp
                                   pgs-words-le-octets floor mod fn-hp-mkey fn-hp-cells-of fn-hp-len-pad8 fn-scc-program adt-len-region-below-body adt-body
                                   fn-hp-pad8-count fn-hp-pe-is-pad8 fn-hp-pad8 nth take nthcdr fn-hp-events-okp)))))

(defun fn-hp-x-ready (p pgs-mem)
  ; :ok when logical page P is resident and verified; otherwise what the
  ; host serves before it asks again, in `pgs-x-read''s shapes:
  ; (:need-table T PHYS), (:need-page P PHYS) (fill the page from PHYS and
  ; call `pgs-x-open-page' with :eager, which verifies it against its table
  ; entry), or :out-of-range.  Reads the stobj; changes nothing.
  (declare (xargs :stobjs pgs-mem :guard (natp p)))
  (let ((tp (floor p 341)))
    (cond ((not (and (< p (pgs-v-length pgs-mem))
                     (<= (* 2048 (+ 1 p)) (pgs-w-length pgs-mem))
                     (< tp (pgs-tv-length pgs-mem))))
           :out-of-range)
          ((not (equal (pgs-tvi tp pgs-mem) 2))
           (list :need-table tp (first (pgs-x-get-entry 1 *pgs-x-dir-base* tp pgs-mem))))
          ((not (equal (pgs-vi p pgs-mem) 2))
           (list :need-page p (first (pgs-x-get-entry 2 0 p pgs-mem))))
          (t :ok))))

(defthm fn-hp-x-ready-ok
  (implies (equal (fn-hp-x-ready p pgs-mem) :ok)
           (and (< p (pgs-v-length pgs-mem))
                (<= (* 2048 (+ 1 p)) (pgs-w-length pgs-mem))
                (equal (pgs-vi p pgs-mem) 2)))
  :rule-classes :forward-chaining)

(defun fn-hp-x-ready-range (p hi pgs-mem)
  ; :ok when every page in [P, HI) is ready, else the first one's verdict
  (declare (xargs :stobjs pgs-mem :guard (and (natp p) (natp hi))
                  :measure (nfix (- (nfix hi) (nfix p)))))
  (if (mbe :logic (zp (- (nfix hi) (nfix p))) :exec (<= hi p))
      :ok
    (let ((v (fn-hp-x-ready p pgs-mem)))
      (if (eq v :ok) (fn-hp-x-ready-range (+ 1 (nfix p)) hi pgs-mem) v))))

(defun fn-hp-x-words (i k pgs-mem)
  ; words I .. I+K-1 of the image, as a list
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp k) (<= (+ i k) (pgs-w-length pgs-mem)))))
  (if (zp k) nil (cons (pgs-wi i pgs-mem) (fn-hp-x-words (+ 1 i) (1- k) pgs-mem))))

(defthm fn-hp-x-words-is-take
  (implies (natp i)
           (equal (fn-hp-x-words i k pgs-mem) (take k (nthcdr i (nth *pgs-wi* pgs-mem)))))
  :hints (("Goal" :in-theory (enable pgs-wi take nthcdr) :induct (fn-hp-x-words i k pgs-mem))))

; The open's header check as the host calls it.
(verify-guards fn-hp-w-header)

(defun fn-hp-x-header (npages pgs-mem)
  ; The open's header check, as the host calls it: (mv VERDICT RESULT).
  ; VERDICT :ok and RESULT (:ok N LENS STARTS) or (:refused REASON) once
  ; page 0 is ready; else VERDICT is what the host serves first.
  (declare (xargs :stobjs pgs-mem :guard (natp npages)))
  (let ((v (fn-hp-x-ready 0 pgs-mem)))
    (if (eq v :ok)
        (mv :ok (fn-hp-w-header (fn-hp-x-words 0 19 pgs-mem) npages))
      (mv v nil))))

(local
 (defthm fn-hp-nth-take-below
   (implies (and (natp j) (natp k) (< j k))
            (equal (nth j (take k w)) (nth j w)))
   :hints (("Goal" :in-theory (enable nth take)))))

(defthm fn-hp-w-header-take-19
  (equal (fn-hp-w-header (take 19 w) npages) (fn-hp-w-header w npages))
  :hints (("Goal" :in-theory (disable take adt-starts-l adt-end-l adt-placement-ok))))

(local
 (defthm fn-hp-take-19-of-take-2048
   (equal (take 19 (take 2048 w)) (take 19 w))
   :hints (("Goal" :in-theory (enable take)))))

; KEYSTONE (the open's header, m2): when page 0 of the page store's image
; holds page 0 of the history's image and the store holds the image's page
; count, the header check the host calls answers the history's N and
; regions; no row page is read.
(defthm fn-hp-x-header-of-image
  (implies (and (fn-hp-okp h salt)
                (equal (take 2048 (nth *pgs-wi* pgs-mem)) (take 2048 (fn-hp-iw h salt)))
                (equal npages (fn-hp-npages h salt))
                (equal (mv-nth 0 (fn-hp-x-header npages pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-header npages pgs-mem))
                  (list :ok (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-w-header-of-image)
                 (:instance fn-hp-w-header-take-19 (w (nth *pgs-wi* pgs-mem)) (npages (fn-hp-npages h salt)))
                 (:instance fn-hp-w-header-take-19 (w (fn-hp-iw h salt)) (npages (fn-hp-npages h salt)))
                 (:instance fn-hp-take-19-of-take-2048 (w (nth *pgs-wi* pgs-mem)))
                 (:instance fn-hp-take-19-of-take-2048 (w (fn-hp-iw h salt))))
           :in-theory (disable fn-hp-w-header-of-image fn-hp-w-header-take-19 fn-hp-take-19-of-take-2048
                               fn-hp-w-header fn-hp-iw fn-hp-okp fn-hp-npages fn-hp-lens fn-hp-starts take))))

(local
 (defthm fn-hp-octetp-sha-byte
   (fn-scc-octetp (pgs-octet x))
   :hints (("Goal" :in-theory (enable pgs-octet fn-scc-octetp)))))
(local
 (defthm fn-hp-scc-octets-of-word
   (fn-scc-octet-listp (pgs-word-le-octets w))
   :hints (("Goal" :in-theory (disable pgs-octet ash)))))
(local
 (defthm fn-hp-scc-octet-listp-append
   (implies (and (fn-scc-octet-listp x) (fn-scc-octet-listp y)) (fn-scc-octet-listp (append x y)))))
(defthm fn-hp-scc-octets-of-words
  (fn-scc-octet-listp (pgs-words-le-octets ws))
  :hints (("Goal" :in-theory (disable pgs-word-le-octets))))

(defun fn-hp-at-core (seq n lens salt mkey tl off plen pw)
  ; the decision of the row read, given the row's four cells and PW, the
  ; words of its pool entry
  (declare (xargs :guard (and (true-listp lens) (true-listp pw))))
  (cond ((not (and (natp seq) (< seq (nfix n)))) (list :refused :seq))
        ((not (and (natp off) (natp plen) (natp tl) (equal (mod off 8) 0) (equal (mod plen 8) 0)
                   (<= tl plen) (<= (+ off plen) (nfix (nth 4 lens)))))
         (list :refused :cells))
        (t (let ((bytes (pgs-words-le-octets pw)))
             (if (not (and (<= tl (len bytes)) (equal bytes (fn-hp-pad8 (take tl bytes)))))
                 (list :refused :padding)
               (let ((d (fn-scc-decode-tree (take tl bytes))))
                 (cond ((not (eq (car d) :ok)) (list :refused :tree))
                       ((not (equal mkey (fn-hp-mkey (cadr d) salt))) (list :refused :mkey))
                       (t d))))))))

(defthm fn-hp-at-core-when
  (implies (and (natp seq) (< seq (nfix n))
                (natp off) (natp plen) (natp tl) (equal (mod off 8) 0) (equal (mod plen 8) 0)
                (<= tl plen) (<= (+ off plen) (nfix (nth 4 lens)))
                (equal (pgs-words-le-octets pw) bytes)
                (<= tl (len bytes))
                (equal bytes (fn-hp-pad8 (take tl bytes)))
                (equal (fn-scc-decode-tree (take tl bytes)) (list :ok ev))
                (equal mkey (fn-hp-mkey ev salt)))
           (equal (fn-hp-at-core seq n lens salt mkey tl off plen pw) (list :ok ev)))
  :hints (("Goal" :in-theory (disable fn-hp-mkey fn-scc-decode-tree pgs-words-le-octets mod take nth))))

(defun fn-hp-cell-word (r seq w starts)
  ; cell SEQ of column R, as the reader finds it in the words W
  (declare (xargs :verify-guards nil))
  (nth (+ (* 2048 (nth r starts)) seq) w))

(defun fn-hp-pool-words (seq w starts)
  ; the words of row SEQ's pool entry, as the reader finds them in W
  (declare (xargs :verify-guards nil))
  (let ((off (fn-hp-cell-word 2 seq w starts)) (plen (fn-hp-cell-word 3 seq w starts)))
    (take (floor plen 8) (nthcdr (+ (* 2048 (nth 4 starts)) (floor off 8)) w))))

(defun fn-hp-w-row (seq w salt n lens starts)
  ; the row read over the words W: the core over what W holds at the row
  (declare (xargs :verify-guards nil))
  (fn-hp-at-core seq n lens salt
                 (fn-hp-cell-word 0 seq w starts) (fn-hp-cell-word 1 seq w starts)
                 (fn-hp-cell-word 2 seq w starts) (fn-hp-cell-word 3 seq w starts)
                 (fn-hp-pool-words seq w starts)))

(defthm fn-hp-len-pe-bound
  (<= (len (fn-scc-encode ev)) (len (fn-hp-pe ev)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-hp-len-enc-le-pe)))))

(defthm fn-hp-w-row-of-image
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)))
           (equal (fn-hp-w-row seq (fn-hp-iw h salt) salt (len h) (fn-hp-lens h salt) (fn-hp-starts h salt))
                  (list :ok (nth seq h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-at-core-when (n (len h)) (lens (fn-hp-lens h salt)) (ev (nth seq h))
                            (mkey (fn-hp-mkey (nth seq h) salt)) (tl (len (fn-scc-encode (nth seq h))))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h))))
                            (pw (take (floor (len (fn-hp-pe (nth seq h))) 8)
                                      (nthcdr (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take seq h)) 8))
                                              (fn-hp-iw h salt))))
                            (bytes (fn-hp-pe (nth seq h))))
                 (:instance fn-hp-iw-cell (r 0) (i seq)) (:instance fn-hp-iw-cell (r 1) (i seq))
                 (:instance fn-hp-iw-cell (r 2) (i seq)) (:instance fn-hp-iw-cell (r 3) (i seq))
                 (:instance fn-hp-cells-of-is (ev (nth seq h)) (pos (fn-hp-pes-len (take seq h))))
                 (:instance fn-hp-iw-pool (i seq))
                 (:instance fn-hp-evp-nth (i seq))
                 (:instance fn-hp-pes-len-take-bound (i seq))
                 (:instance fn-hp-pes-len-mod-8 (h (take seq h)))
                 (:instance fn-hp-pe-mod-8 (ev (nth seq h)))
                 (:instance fn-hp-take-of-pe (ev (nth seq h)))
                 (:instance fn-hp-pe-def (ev (nth seq h)))
                 (:instance fn-hp-decode-enc (ev (nth seq h)))
                 (:instance fn-hp-len-enc-le-pe (ev (nth seq h))))
           :in-theory (theory 'minimal-theory))
          ("Goal'" :in-theory (e/d (fn-hp-lens-4 fn-hp-w-row fn-hp-cell-word fn-hp-pool-words)
                                   (fn-hp-at-core fn-hp-iw fn-hp-image fn-hp-okp fn-hp-starts fn-hp-lens
                                   fn-hp-npages fn-hp-pes-len fn-hp-pe fn-scc-encode fn-scc-decode-tree fn-hp-evp
                                   pgs-words-le-octets floor mod fn-hp-mkey fn-hp-cells-of fn-hp-len-pad8 fn-scc-program
                                   adt-len-region-below-body adt-body
                                   fn-hp-pad8-count fn-hp-pe-is-pad8 fn-hp-pad8 nth take nthcdr fn-hp-events-okp)))))

