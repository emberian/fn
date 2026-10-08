; fn: staging a checkpoint's root region into the page store's image (lane
; s-pck-2c, 2026-10-08; STORAGE-PROGRAM-20261006.md section 3.3, 2c).
;
; The root region is pages 0..7 of the image: the root row (`fn-pck-enc-root'
; of the root tree: the four fold roots, F and the payload file's length) in
; the tape's row schema, padded with zero words to K = 8 pages
; (`fn-pck-root-pages-of-tree').  `fn-pck-x-stage-root' encodes the tree into
; the octet buffer and writes ALL 8 * 2048 words, one `pgs-x-write' each, so
; the pages the commit digests are the new root whatever the old root held (a
; shorter root clears the old one's tail).  A root of more than K pages is
; refused by name before anything is written.
;
;   fn-pck-x-stage-root-is-the-root-pages   the keystone.
;
; Scope, named.  Premises: the tree is encodable (`fn-sccb-treep'), the root
; fits K pages (`fn-pck-root-fitsp-tree': the publication plan's :commit arm),
; the row's words are u64 (`adt-tp-seq-lens-ok': the generator's premise), and
; root pages 0..7 are resident and writable (`pcr-res': the resident-open
; scope; a non-resident page answers (:need-page LP) under lazy open, owed
; with PCK-STAGE-NEED-PAGE).

(in-package "ACL2")
(include-book "paged-checkpoint-stage")
(include-book "paged-checkpoint-open")
(local (include-book "arithmetic/top" :dir :system))

(defconst *pcr-words* 16384)

(defun fn-pck-x-root-word (j nw fn-octets)
  ; Word J of the root region: the root row's word, then zeros.
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (if (< (nfix j) (nfix nw))
      (fn-pck-x-row-word j 0 0 0 0 0 0 fn-octets)
    0))

(defun fn-pck-x-put-root (j nw fn-octets pgs-mem)
  ; Words J..8*2048-1 of the root region, each to its page and offset.
  (declare (xargs :stobjs (fn-octets pgs-mem) :verify-guards nil
                  :measure (nfix (- 16384 (nfix j)))))
  (if (and (natp j) (< j 16384))
      (mv-let (v pgs-mem)
        (pgs-x-write (floor j 2048) (mod j 2048) (fn-pck-x-root-word j nw fn-octets) pgs-mem)
        (if (eq v :ok)
            (fn-pck-x-put-root (1+ j) nw fn-octets pgs-mem)
          (mv v pgs-mem)))
    (mv :ok pgs-mem)))

(defun fn-pck-x-stage-root (tree fn-octets pgs-mem)
  ; (mv VERDICT fn-octets pgs-mem).  A root over K pages is refused before a
  ; word is written.
  (declare (xargs :stobjs (fn-octets pgs-mem) :verify-guards nil))
  (let* ((fn-octets (fn-pck-x-encode tree fn-octets))
         (nw (fn-pck-x-row-words (fn-octets-len fn-octets))))
    (if (< 16384 nw)
        (mv :checkpoint-root-over-k fn-octets pgs-mem)
      (mv-let (v pgs-mem)
        (fn-pck-x-put-root 0 nw fn-octets pgs-mem)
        (mv v fn-octets pgs-mem)))))

(defun pcr-page-res (lp pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (natp lp) :verify-guards nil))
  (and (< lp (pgs-d-length pgs-mem)) (< lp (pgs-v-length pgs-mem))
       (<= (* 2048 (+ 1 lp)) (pgs-w-length pgs-mem))
       (equal (pgs-vi lp pgs-mem) 2)))

(defun pcr-res (pgs-mem)
  ; Root pages 0..7 are in the image, resident.
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (and (pcr-page-res 0 pgs-mem) (pcr-page-res 1 pgs-mem) (pcr-page-res 2 pgs-mem) (pcr-page-res 3 pgs-mem)
       (pcr-page-res 4 pgs-mem) (pcr-page-res 5 pgs-mem) (pcr-page-res 6 pgs-mem) (pcr-page-res 7 pgs-mem)))

(in-theory (disable pckx-npk-step pckx-npk-bound))

(defthm pcr-res-of-write
  (implies (and (natp lp) (natp off)
                (equal (mv-nth 0 (pgs-x-write lp off v pgs-mem)) :ok))
           (equal (pcr-res (mv-nth 1 (pgs-x-write lp off v pgs-mem)))
                  (pcr-res pgs-mem)))
  :hints (("Goal" :in-theory (e/d (pcr-res pcr-page-res) (pgs-x-write))
           :use ((:instance pgs-x-write-facts (a 0) (j 0))
                 (:instance pgs-x-write-facts (a 0) (j 1))
                 (:instance pgs-x-write-facts (a 0) (j 2))
                 (:instance pgs-x-write-facts (a 0) (j 3))
                 (:instance pgs-x-write-facts (a 0) (j 4))
                 (:instance pgs-x-write-facts (a 0) (j 5))
                 (:instance pgs-x-write-facts (a 0) (j 6))
                 (:instance pgs-x-write-facts (a 0) (j 7))))))

(defthm pcr-page-of-addr
  (implies (and (natp j) (< j 16384) (pcr-res pgs-mem))
           (pcr-page-res (floor j 2048) pgs-mem))
  :hints (("Goal" :in-theory (e/d (pcr-res) (pcr-page-res))
           :cases ((equal (floor j 2048) 0) (equal (floor j 2048) 1) (equal (floor j 2048) 2) (equal (floor j 2048) 3)
                   (equal (floor j 2048) 4) (equal (floor j 2048) 5) (equal (floor j 2048) 6) (equal (floor j 2048) 7)))))

(defthm pcr-write-ok
  (implies (and (natp j) (< j 16384) (pcr-res pgs-mem))
           (equal (mv-nth 0 (pgs-x-write (floor j 2048) (mod j 2048) v pgs-mem)) :ok))
  :hints (("Goal" :use ((:instance pgs-x-write-ok (lp (floor j 2048)) (off (mod j 2048)))
                        pcr-page-of-addr)
           :in-theory (e/d (pcr-page-res) (pgs-x-write-ok pgs-x-write pcr-page-of-addr)))))

(defthm pcr-addr (implies (natp j) (equal (+ (* 2048 (floor j 2048)) (mod j 2048)) j))
  :hints (("Goal" :in-theory (enable mod floor))))

(defthm pcr-words-of-write
  (implies (and (natp j) (< j 16384) (pcr-res pgs-mem) (natp a) (natp k))
           (equal (pgs-x-words 0 a k (mv-nth 1 (pgs-x-write (floor j 2048) (mod j 2048) v pgs-mem)))
                  (if (and (<= a j) (< j (+ a k)))
                      (update-nth (- j a) (pgs-dlo v) (pgs-x-words 0 a k pgs-mem))
                    (pgs-x-words 0 a k pgs-mem))))
  :hints (("Goal" :use ((:instance pgs-x-words-of-write (lp (floor j 2048)) (off (mod j 2048)))
                        pcr-write-ok pcr-addr)
           :in-theory (disable pgs-x-words-of-write pcr-write-ok pcr-addr pgs-x-write pgs-dlo pgs-x-words))))

(defun pcr-agree (j nw fn-octets w)
  (declare (xargs :stobjs fn-octets :verify-guards nil :measure (nfix (- 16384 (nfix j)))))
  (if (and (natp j) (< j 16384))
      (and (equal (fn-pck-x-root-word j nw fn-octets) (nth j w))
           (pcr-agree (1+ j) nw fn-octets w))
    t))

(defun pcr-ind (j w l0) (if (zp j) (list w l0) (pcr-ind (1- j) (cdr w) (cdr l0))))

(defthm pcr-list-step
  (implies (and (natp j) (< j (len w)) (< j (len l0)) (equal x (nth j w)))
           (equal (append (take (1+ j) (update-nth j x l0)) (nthcdr (1+ j) w))
                  (append (take j l0) (nthcdr j w))))
  :rule-classes nil
  :hints (("Goal" :induct (pcr-ind j w l0) :in-theory (enable update-nth take nth))))

(defthm pcr-dlo-nth
  (implies (and (adt-tp-u64s w) (natp j) (< j (len w)))
           (equal (pgs-dlo (nth j w)) (nth j w)))
  :hints (("Goal" :induct (nth j w) :in-theory (enable adt-tp-u64s pgs-dlo unsigned-byte-p nth))))

(defun pcr-l (pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (pgs-x-words 0 0 16384 pgs-mem))

(defthm pcr-len-l (equal (len (pcr-l pgs-mem)) 16384)
  :hints (("Goal" :use ((:instance pcks-len-words (a 0) (k 16384))) :in-theory (e/d (pcr-l) (pcks-len-words)))))

(defthm pcr-agree-here
  (implies (and (natp j) (< j 16384) (pcr-agree j nw fn-octets w))
           (equal (fn-pck-x-root-word j nw fn-octets) (nth j w)))
  :rule-classes nil
  :hints (("Goal" :expand ((pcr-agree j nw fn-octets w)))))

(defthm pcr-agree-next
  (implies (and (natp j) (< j 16384) (pcr-agree j nw fn-octets w))
           (pcr-agree (1+ j) nw fn-octets w))
  :rule-classes nil
  :hints (("Goal" :expand ((pcr-agree j nw fn-octets w)))))

(defthm pcr-step-l
  (implies (and (natp j) (< j 16384) (pcr-res pgs-mem) (adt-tp-u64s w) (equal (len w) 16384)
                (equal (fn-pck-x-root-word j nw fn-octets) (nth j w)))
           (equal (pcr-l (mv-nth 1 (pgs-x-write (floor j 2048) (mod j 2048) (fn-pck-x-root-word j nw fn-octets) pgs-mem)))
                  (update-nth j (nth j w) (pcr-l pgs-mem))))
  :hints (("Goal" :in-theory (disable pcr-res pgs-x-write pgs-dlo pgs-x-words pcr-write-ok pcr-res-of-write pcr-words-of-write pcr-dlo-nth)
           :use ((:instance pcr-words-of-write (a 0) (k 16384) (v (nth j w)))
                 (:instance pcr-dlo-nth)))))

(defthm pcr-true-listp-l (true-listp (pcr-l pgs-mem))
  :hints (("Goal" :in-theory (enable pcr-l))))

(defthm pcr-take-all (implies (and (true-listp l) (equal (len l) n)) (equal (take n l) l)))

(defthm pcr-nthcdr-all (implies (and (true-listp w) (natp n) (<= (len w) n)) (equal (nthcdr n w) nil)))

(defun pcr-wr (j nw fn-octets pgs-mem)
  (declare (xargs :stobjs (fn-octets pgs-mem) :verify-guards nil))
  (pgs-x-write (floor j 2048) (mod j 2048) (fn-pck-x-root-word j nw fn-octets) pgs-mem))

(defthm pcr-put-open
  (implies (and (natp j) (< j 16384))
           (equal (fn-pck-x-put-root j nw fn-octets pgs-mem)
                  (mv-let (v m) (pcr-wr j nw fn-octets pgs-mem)
                    (if (eq v :ok) (fn-pck-x-put-root (1+ j) nw fn-octets m) (mv v m)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-pck-x-put-root j nw fn-octets pgs-mem)) :in-theory (enable pcr-wr))))

(defthm pcr-put-done
  (implies (not (and (natp j) (< j 16384)))
           (equal (fn-pck-x-put-root j nw fn-octets pgs-mem) (mv :ok pgs-mem)))
  :hints (("Goal" :expand ((fn-pck-x-put-root j nw fn-octets pgs-mem)))))

(defthm pcr-wr-ok
  (implies (and (natp j) (< j 16384) (pcr-res pgs-mem))
           (equal (mv-nth 0 (pcr-wr j nw fn-octets pgs-mem)) :ok))
  :hints (("Goal" :in-theory (disable pcr-res pgs-x-write) :use (:instance pcr-write-ok (v (fn-pck-x-root-word j nw fn-octets))) :expand ((pcr-wr j nw fn-octets pgs-mem)))))

(defthm pcr-wr-res
  (implies (and (natp j) (< j 16384) (pcr-res pgs-mem))
           (pcr-res (mv-nth 1 (pcr-wr j nw fn-octets pgs-mem))))
  :hints (("Goal" :in-theory (disable pcr-res pgs-x-write) :use ((:instance pcr-res-of-write (lp (floor j 2048)) (off (mod j 2048)) (v (fn-pck-x-root-word j nw fn-octets))) pcr-wr-ok) :expand ((pcr-wr j nw fn-octets pgs-mem)))))

(defthm pcr-wr-l
  (implies (and (natp j) (< j 16384) (pcr-res pgs-mem) (adt-tp-u64s w) (equal (len w) 16384) (pcr-agree j nw fn-octets w))
           (equal (pcr-l (mv-nth 1 (pcr-wr j nw fn-octets pgs-mem)))
                  (update-nth j (nth j w) (pcr-l pgs-mem))))
  :hints (("Goal" :in-theory (disable pcr-res pgs-x-write pcr-l pcr-agree) :use (pcr-agree-here pcr-step-l) :expand ((pcr-wr j nw fn-octets pgs-mem)))))

(in-theory (disable pcr-wr))

(defun pcr-ind2 (j nw fn-octets pgs-mem)
  (declare (xargs :stobjs (fn-octets pgs-mem) :verify-guards nil :measure (nfix (- 16384 (nfix j)))))
  (if (and (natp j) (< j 16384))
      (mv-let (v pgs-mem) (pcr-wr j nw fn-octets pgs-mem)
        (if (eq v :ok) (pcr-ind2 (1+ j) nw fn-octets pgs-mem) (mv v pgs-mem)))
    (mv :ok pgs-mem)))

(defthm pcr-put-root-words
  (implies (and (natp j) (<= j 16384) (pcr-res pgs-mem)
                (pcr-agree j nw fn-octets w) (true-listp w) (equal (len w) 16384) (adt-tp-u64s w))
           (and (equal (mv-nth 0 (fn-pck-x-put-root j nw fn-octets pgs-mem)) :ok)
                (pcr-res (mv-nth 1 (fn-pck-x-put-root j nw fn-octets pgs-mem)))
                (equal (pcr-l (mv-nth 1 (fn-pck-x-put-root j nw fn-octets pgs-mem)))
                       (append (take j (pcr-l pgs-mem)) (nthcdr j w)))))
  :hints (("Goal" :induct (pcr-ind2 j nw fn-octets pgs-mem)
           :in-theory (disable pcr-res pgs-x-write pgs-x-words pgs-dlo pcr-l pcr-agree fn-pck-x-root-word
                               fn-pck-x-put-root))
          ("Subgoal *1/1" :in-theory (disable pcr-res pgs-x-write pgs-x-words pgs-dlo pcr-l pcr-agree fn-pck-x-root-word fn-pck-x-put-root)
           :do-not '(eliminate-destructors generalize fertilize)
           :use ((:instance pcr-list-step (x (nth j w)) (l0 (pcr-l pgs-mem)))
                 (:instance pcr-put-open (j j) (nw nw) (fn-octets fn-octets) (pgs-mem pgs-mem))
                 (:instance pcr-agree-next (j j) (nw nw) (fn-octets fn-octets) (w w)) (:instance pcr-agree-here (j j) (nw nw) (fn-octets fn-octets) (w w))))))

; -----------------------------------------------------------------------------
; The target: the root region's words.

(defun pcr-rw (tree) (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-root tree)))

(defun pcr-w (tree) (append (pcr-rw tree) (adt-tp-zeros (- 16384 (len (pcr-rw tree))))))

(in-theory (disable pcr-rw))

(defthm pcr-rw-of-program
  (equal (pcr-rw tree)
         (cons 1 (cons (len (fn-scc-program tree))
                       (append (adt-tp-pack (fn-scc-program tree)) (list 0 0 0 0 0 0)))))
  :hints (("Goal" :in-theory (e/d (pcr-rw fn-pck-enc-root adt-tp-rw adt-tp-fw adt-enc) (adt-tp-pack adt-tp-npk)))))

(defthm pcr-len-rw
  (equal (len (pcr-rw tree)) (fn-pck-x-row-words (len (fn-scc-program tree))))
  :hints (("Goal" :in-theory (e/d (fn-pck-x-row-words) (adt-tp-pack adt-tp-npk))
           :use ((:instance adt-tp-len-pack (o (fn-scc-program tree)))))))

(defthm pcr-true-listp-rw (true-listp (pcr-rw tree))
  :hints (("Goal" :in-theory (enable pcr-rw))))

(defthm pcr-fits
  (implies (fn-pck-root-fitsp-tree tree)
           (<= (len (pcr-rw tree)) 16384))
  :hints (("Goal" :in-theory (e/d (fn-pck-root-fitsp-tree fn-pck-row-pages-of adt-tp-pages-of adt-tp-seq-words pcr-rw) (adt-tp-pages))
           :use ((:instance pcko-flat-fit (w (pcr-rw tree)))))))

(defthm pcr-len-w
  (implies (<= (len (pcr-rw tree)) 16384) (equal (len (pcr-w tree)) 16384)))

(defthm pcr-true-listp-w (true-listp (pcr-w tree)))

(defthm pcr-zeros-u64 (adt-tp-u64s (adt-tp-zeros n))
  :hints (("Goal" :in-theory (enable adt-tp-zeros adt-tp-u64s))))

(defthm pcr-u64s-append (implies (and (adt-tp-u64s a) (adt-tp-u64s b)) (adt-tp-u64s (append a b)))
  :hints (("Goal" :in-theory (enable adt-tp-u64s))))

(defthm pcr-u64s-rw
  (implies (and (fn-sccb-treep tree) (adt-tp-seq-lens-ok *fn-pck-row-schema* (list (fn-pck-enc-root tree))))
           (adt-tp-u64s (pcr-rw tree)))
  :hints (("Goal" :in-theory (e/d (adt-tp-seq-words) (pcr-rw-of-program))
           :use ((:instance adt-tp-u64s-seq-words (s *fn-pck-row-schema*) (a (list (fn-pck-enc-root tree))))
                 (:instance pck-ap-enc-root (x tree))))
          ("Goal'" :in-theory (enable pcr-rw))))

(defthm pcr-u64s-w
  (implies (and (fn-sccb-treep tree) (adt-tp-seq-lens-ok *fn-pck-row-schema* (list (fn-pck-enc-root tree))))
           (adt-tp-u64s (pcr-w tree))))

; The buffer after encoding.

(defthm pcr-encode-len
  (implies (fn-sccb-treep tree)
           (equal (fn-octets-len (fn-pck-x-encode tree fn-octets)) (len (fn-scc-program tree))))
  :hints (("Goal" :use ((:instance fn-pck-x-encode-is-the-program (x tree))
                        (:instance fn-oct-len-is-len (fn-octets (fn-pck-x-encode tree fn-octets)))
                        (:instance fn-oct-list-is-identity (fn-octets (fn-pck-x-encode tree fn-octets))))
           :in-theory (disable fn-pck-x-encode-is-the-program fn-pck-x-encode fn-oct-len-is-len fn-oct-list-is-identity))))

(defun pcr-ind3 (i n) (if (zp i) (list i n) (pcr-ind3 (1- i) (1- n))))

(defthm pcr-nth-zeros (implies (and (natp i) (natp n) (< i n)) (equal (nth i (adt-tp-zeros n)) 0))
  :hints (("Goal" :induct (pcr-ind3 i n) :expand ((adt-tp-zeros n)) :in-theory (enable adt-tp-zeros nth))))

(defthm pcr-nth-append-left
  (implies (and (natp j) (< j (len a))) (equal (nth j (append a b)) (nth j a))))

(defthm pcr-nth-append-right
  (implies (and (natp j) (<= (len a) j) (true-listp a)) (equal (nth j (append a b)) (nth (- j (len a)) b))))

(defthm pcr-word-is-w
  (implies (and (fn-sccb-treep tree) (natp j) (< j 16384) (<= (len (pcr-rw tree)) 16384))
           (equal (fn-pck-x-root-word j (fn-pck-x-row-words (len (fn-scc-program tree)))
                                      (fn-pck-x-encode tree fn-octets))
                  (nth j (pcr-w tree))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-x-root-word) (fn-pck-x-row-word pcr-rw-of-program pcr-len-rw adt-tp-pack adt-tp-npk fn-pck-x-encode))
           :use ((:instance pckx-word-of-list (prog (fn-scc-program tree)) (fn-octets (fn-pck-x-encode tree fn-octets))
                            (off 0) (plen 0) (d0 0) (d1 0) (d2 0) (d3 0))
                 (:instance fn-pck-x-encode-is-the-program (x tree))
                 pcr-len-rw pcr-rw-of-program))))

(defthm pcr-agree-all
  (implies (and (fn-sccb-treep tree) (natp j) (<= (len (pcr-rw tree)) 16384))
           (pcr-agree j (fn-pck-x-row-words (len (fn-scc-program tree)))
                      (fn-pck-x-encode tree fn-octets) (pcr-w tree)))
  :hints (("Goal" :induct (pcr-agree j (fn-pck-x-row-words (len (fn-scc-program tree)))
                                     (fn-pck-x-encode tree fn-octets) (pcr-w tree))
           :in-theory (disable pcr-word-is-w))
          ("Subgoal *1/2" :expand ((pcr-agree j (fn-pck-x-row-words (len (fn-scc-program tree)))
                                              (fn-pck-x-encode tree fn-octets) (pcr-w tree)))
           :use pcr-word-is-w)
          ("Subgoal *1/1" :expand ((pcr-agree j (fn-pck-x-row-words (len (fn-scc-program tree)))
                                              (fn-pck-x-encode tree fn-octets) (pcr-w tree))))))

; Pages.

(defun pcr-pagesp (ps)
  (if (atom ps) (null ps)
    (and (true-listp (car ps)) (equal (len (car ps)) 2048) (pcr-pagesp (cdr ps)))))

(defthm pcr-pages-of-flat
  (implies (pcr-pagesp ps) (equal (adt-tp-pages (adt-tp-flat ps)) ps))
  :hints (("Goal" :induct (pcr-pagesp ps) :in-theory (disable adt-tp-pages))
          ("Subgoal *1/2" :use ((:instance pcks-pages-of-block (blk (car ps)) (rest (adt-tp-flat (cdr ps))))))))

(defthm pcr-pagesp-of-pages
  (implies (true-listp w) (pcr-pagesp (adt-tp-pages w)))
  :hints (("Goal" :induct (adt-tp-pages w) :in-theory (disable adt-tp-page))
          ("Subgoal *1/2" :expand ((adt-tp-pages w)) :use adt-tp-len-page)))

(defthm pcr-pagesp-zero (pcr-pagesp (fn-pck-zero-pages n))
  :hints (("Goal" :in-theory (enable fn-pck-zero-pages))))

(defthm pcr-pagesp-append (implies (and (pcr-pagesp a) (pcr-pagesp b)) (pcr-pagesp (append a b))))

(defthm pcr-root-pagesp
  (implies (fn-pck-root-fitsp-tree tree)
           (pcr-pagesp (fn-pck-root-pages-of-tree tree)))
  :hints (("Goal" :in-theory (e/d (fn-pck-root-pages-of-tree fn-pck-root-fitsp-tree fn-pck-fit fn-pck-row-pages-of adt-tp-pages-of adt-tp-seq-words)
                                  (adt-tp-pages pcr-pagesp-of-pages))
           :use ((:instance pcr-pagesp-of-pages (w (pcr-rw tree)))))))

(defthm pcr-root-flat
  (implies (fn-pck-root-fitsp-tree tree)
           (equal (adt-tp-flat (fn-pck-root-pages-of-tree tree)) (pcr-w tree)))
  :hints (("Goal" :in-theory (e/d (fn-pck-root-pages-of-tree fn-pck-root-fitsp-tree fn-pck-row-pages-of adt-tp-pages-of adt-tp-seq-words)
                                  (adt-tp-pages adt-tp-flat pcko-flat-fit))
           :use ((:instance pcko-flat-fit (w (pcr-rw tree)))))))

(defthm pcr-root-pages-of-w
  (implies (fn-pck-root-fitsp-tree tree)
           (equal (adt-tp-pages (pcr-w tree)) (fn-pck-root-pages-of-tree tree)))
  :hints (("Goal" :use (pcr-root-flat pcr-root-pagesp (:instance pcr-pages-of-flat (ps (fn-pck-root-pages-of-tree tree))))
           :in-theory (disable pcr-root-flat pcr-root-pagesp pcr-pages-of-flat))))

(defthm pcr-stage-root-words
  (implies (and (fn-sccb-treep tree) (fn-pck-root-fitsp-tree tree)
                (adt-tp-seq-lens-ok *fn-pck-row-schema* (list (fn-pck-enc-root tree)))
                (pcr-res pgs-mem))
           (let ((r (fn-pck-x-stage-root tree fn-octets pgs-mem)))
             (and (equal (mv-nth 0 r) :ok)
                  (equal (pcr-l (mv-nth 2 r)) (pcr-w tree)))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-pck-x-stage-root tree fn-octets pgs-mem))
           :in-theory (e/d () (pcr-put-root-words pcr-res pcr-l pcr-w pcr-agree-all pcr-encode-len pcr-len-rw pcr-fits fn-pck-x-put-root fn-pck-x-encode
                                                  fn-pck-x-row-words))
           :use ((:instance pcr-put-root-words (j 0) (nw (fn-pck-x-row-words (len (fn-scc-program tree))))
                            (fn-octets (fn-pck-x-encode tree fn-octets)) (w (pcr-w tree)))
                 (:instance pcr-agree-all (j 0))
                 pcr-encode-len pcr-len-rw pcr-fits pcr-len-w pcr-true-listp-w pcr-u64s-w))))

(defthm pcr-abs-dirty-root
  (equal (pgs-x-abs-dirty '(0 1 2 3 4 5 6 7) pgs-mem)
         (adt-tp-number 0 (adt-tp-pages (pcr-l pgs-mem))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcks-abs-dirty-iota (lp0 0) (n 8)))
           :in-theory (e/d (pcr-l) (pcks-abs-dirty-iota pgs-x-words adt-tp-pages adt-tp-number)))))

(defthm fn-pck-x-stage-root-is-the-root-pages
  ; KEYSTONE.  Staging the root tree writes all of pages 0..7: the pages the
  ; commit will digest hold the root pages the model's `fn-pck-dirty' names
  ; (the root part, `adt-tp-number 0' of `fn-pck-root-pages-of-tree'),
  ; whatever the root region held before.  The verdict is :ok.
  (implies (and (fn-sccb-treep tree) (fn-pck-root-fitsp-tree tree)
                (adt-tp-seq-lens-ok *fn-pck-row-schema* (list (fn-pck-enc-root tree)))
                (pcr-res pgs-mem))
           (and (equal (mv-nth 0 (fn-pck-x-stage-root tree fn-octets pgs-mem)) :ok)
                (equal (pgs-x-abs-dirty '(0 1 2 3 4 5 6 7) (mv-nth 2 (fn-pck-x-stage-root tree fn-octets pgs-mem)))
                       (adt-tp-number 0 (fn-pck-root-pages-of-tree tree)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcr-stage-root-words pcr-l pcr-w fn-pck-x-stage-root pcr-res pcr-abs-dirty-root)
           :use (pcr-stage-root-words pcr-root-pages-of-w
                 (:instance pcr-abs-dirty-root (pgs-mem (mv-nth 2 (fn-pck-x-stage-root tree fn-octets pgs-mem))))))))
