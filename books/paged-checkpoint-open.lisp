(in-package "ACL2")
(include-book "paged-checkpoint-image")
(include-book "paged-checkpoint-exec")
(include-book "statement-recover-stream")
(include-book "consumer-event-index")
(local (include-book "arithmetic/top" :dir :system))

; Inherited rules that loop on a symbolic length.
(in-theory (disable pckx-npk-step pckx-npk-bound))

(defconst *pcko-stub* t)

; -----------------------------------------------------------------------------
; The exec.  Every word of the image is read by `pcko-w' at the call site that
; also counts it (the READS threaded through), so the returned count is the
; number of words the open read.

(defun pcko-w (i pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (and (natp i) (< i (pgs-x-len 0 pgs-mem)))))
  (pgs-x-word 0 i pgs-mem))

(defun pcko-copy (pos n reads pgs-mem fn-octets)
  ; The N octets of the payload words from POS on into the buffer, eight to a
  ; word, the last word's low octets (`adt-tp-unpack').
  (declare (xargs :stobjs (pgs-mem fn-octets)
                  :measure (nfix n)
                  :guard (and (natp pos) (natp n) (natp reads)
                              (<= (+ pos (floor (+ n 7) 8)) (pgs-x-len 0 pgs-mem))
                              (fn-octets-p fn-octets))
                  :verify-guards nil))
  (if (and (natp n) (< 0 n))
      (let ((fn-octets (fn-octets-append-word (pcko-w pos pgs-mem) (min n 8) fn-octets)))
        (pcko-copy (1+ pos) (nfix (- n 8)) (1+ reads) pgs-mem fn-octets))
    (mv reads fn-octets)))

(defun pcko-nw (n)
  ; The words N octets take.
  (declare (xargs :guard (natp n)))
  (floor (+ n 7) 8))

(defun pcko-tree (fn-octets)
  ; The tree the buffer's program decodes to, or :refused.
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((d (fn-scc-decode-tree (fn-octets-list fn-octets))))
    (if (and (consp d) (eq (car d) :ok) (consp (cdr d))) (list :ok (cadr d)) :refused)))

(defun pcko-tape (pos lim seq acc index reads pgs-mem fn-arena fn-octets)
  ; The events tape from word POS to LIM: tag, octet count, packed octets, one
  ; record at a time, until a word that is not the tag.
  ; (mv verdict acc index reads fn-arena fn-octets).
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets)
                  :measure (nfix (- (nfix lim) (nfix pos)))
                  :verify-guards nil))
  (if (and (natp pos) (natp lim) (< pos lim))
      (if (eql (pcko-w pos pgs-mem) 1)
          (if (< (+ pos 1) lim)
              (let* ((n (nfix (pcko-w (+ pos 1) pgs-mem)))
                     (nw (pcko-nw n))
                     (npos (+ pos 2 nw)))
                (if (<= npos lim)
                    (let ((fn-octets (fn-octets-clear fn-octets)))
                      (mv-let (reads fn-octets)
                        (pcko-copy (+ pos 2) n (+ reads 2) pgs-mem fn-octets)
                        (let ((d (pcko-tree fn-octets)))
                          (if (eq d :refused)
                              (mv :record acc index reads fn-arena fn-octets)
                            (mv-let (acc2 fn-arena)
                              (fn-ssr-intern-step acc (list (cadr d)) nil nil :resident nil fn-arena)
                              (if (eq acc2 :bad)
                                  (mv :intern acc2 index reads fn-arena fn-octets)
                                (pcko-tape npos lim (1+ seq) acc2
                                           (fn-cei-put seq (cadr d) index) reads
                                           pgs-mem fn-arena fn-octets)))))))
                  (mv :truncated acc index (+ reads 2) fn-arena fn-octets)))
            (mv :truncated acc index (+ reads 1) fn-arena fn-octets))
        (mv :ok acc index (+ reads 1) fn-arena fn-octets))
    (mv :ok acc index reads fn-arena fn-octets)))

(defun fn-pck-x-open (npg pgs-mem fn-arena fn-octets)
  ; The open of the NPG-page image in PGS-MEM: the root row from words 0 ..
  ; 8*2048, then the events tape from word 8*2048 to NPG*2048, record by record.
  ; (mv VERDICT ROWS ROOTS INDEX READS fn-arena fn-octets): VERDICT :ok or a
  ; refusal by name; ROWS the arena rows, ROOTS the four fold roots, INDEX the
  ; event index, READS the words read.
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets) :verify-guards nil))
  (if (and (natp npg) (<= 8 npg) (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
           (eql (pcko-w 0 pgs-mem) 1))
      (let* ((n (nfix (pcko-w 1 pgs-mem)))
             (nw (pcko-nw n)))
        (if (<= (+ 2 nw) 16384)
            (let ((fn-octets (fn-octets-clear fn-octets)))
              (mv-let (reads fn-octets)
                (pcko-copy 2 n 2 pgs-mem fn-octets)
                (let ((d (pcko-tree fn-octets)))
                  (if (eq d :refused)
                      (mv :root nil nil nil reads fn-arena fn-octets)
                    (let ((root (cadr d)))
                      (mv-let (verdict acc index reads fn-arena fn-octets)
                        (pcko-tape 16384 (* 2048 npg) 0 (fn-ssr-seed (nth 1 root)) nil reads
                                   pgs-mem fn-arena fn-octets)
                        (mv verdict (fn-ssr-rows acc)
                            (list (nth 0 root) (nth 1 root) (nth 2 root) (nth 3 root))
                            index reads fn-arena fn-octets)))))))
          (mv :root nil nil nil 2 fn-arena fn-octets)))
    (mv :root nil nil nil (if (and (natp npg) (<= 8 npg) (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))) 1 0)
        fn-arena fn-octets)))

; -----------------------------------------------------------------------------
; The image as a list, and the copy.

(defun pcko-img (w pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard t :verify-guards nil))
  (equal (pgs-x-words 0 0 (len w) pgs-mem) w))

(defun pcko-ind (a k i)
  (if (zp i) (list a k) (pcko-ind (1+ a) (1- k) (1- i))))

(defthm pcko-nth-of-words
  (implies (and (natp a) (natp k) (natp i) (< i k))
           (equal (nth i (pgs-x-words 0 a k pgs-mem))
                  (pgs-x-word 0 (+ a i) pgs-mem)))
  :hints (("Goal" :induct (pcko-ind a k i)
           :expand ((pgs-x-words 0 a k pgs-mem)))))

(defthm pcko-w-is-nth
  (implies (and (pcko-img w pgs-mem) (natp i) (< i (len w)))
           (equal (pcko-w i pgs-mem) (nth i w)))
  :hints (("Goal" :use ((:instance pcko-nth-of-words (a 0) (k (len w))))
           :in-theory (e/d (pcko-img pcko-w) (pcko-nth-of-words))))
  :rule-classes ((:rewrite :match-free :all)))

(in-theory (disable pcko-w pcko-img))

(defthm pcko-unw-is-word-octets
  (equal (adt-tp-unw k w) (fn-oct-word-octets w k))
  :hints (("Goal" :in-theory (enable adt-tp-unw fn-oct-word-octets))))

(defthm pcko-npk-natp (natp (adt-tp-npk n))
  :hints (("Goal" :in-theory (enable adt-tp-npk)))
  :rule-classes (:rewrite :type-prescription))

(defthm pcko-unpack-step
  (implies (posp n)
           (equal (adt-tp-unpack n ws)
                  (append (adt-tp-unw (min n 8) (car ws))
                          (adt-tp-unpack (nfix (- n 8)) (cdr ws)))))
  :hints (("Goal" :expand ((adt-tp-unpack n ws)))))

(defthm pcko-npk-step
  (implies (posp n) (equal (adt-tp-npk n) (+ 1 (adt-tp-npk (nfix (- n 8))))))
  :hints (("Goal" :expand ((adt-tp-npk n)))))

(defthm pcko-car-nthcdr (equal (car (nthcdr i w)) (nth i w)))

(defthm pcko-unpack-zero (equal (adt-tp-unpack 0 ws) nil)
  :hints (("Goal" :expand ((adt-tp-unpack 0 ws)))))
(defthm pcko-npk-zero (equal (adt-tp-npk 0) 0)
  :hints (("Goal" :expand ((adt-tp-npk 0)))))

(defthm pcko-copy-is-unpack
  (implies (and (pcko-img w pgs-mem) (natp pos) (natp n) (natp reads) (true-listp buf)
                (<= (+ pos (adt-tp-npk n)) (len w)))
           (and (equal (mv-nth 0 (pcko-copy pos n reads pgs-mem buf))
                       (+ reads (adt-tp-npk n)))
                (equal (mv-nth 1 (pcko-copy pos n reads pgs-mem buf))
                       (append buf (adt-tp-unpack n (nthcdr pos w))))))
  :hints (("Goal" :induct (pcko-copy pos n reads pgs-mem buf)
           :in-theory (e/d (pcko-unpack-step pcko-npk-step) (nth nthcdr adt-tp-unpack adt-tp-npk)))))

(defthm pcko-copy-reads-car
  (implies (and (pcko-img w pgs-mem) (natp pos) (natp n) (natp reads) (true-listp buf)
                (<= (+ pos (adt-tp-npk n)) (len w)))
           (equal (car (pcko-copy pos n reads pgs-mem buf)) (+ reads (adt-tp-npk n))))
  :hints (("Goal" :use pcko-copy-is-unpack :in-theory (disable pcko-copy-is-unpack pcko-copy))))

(defthm pcko-copy-buf-cadr
  (implies (and (pcko-img w pgs-mem) (natp pos) (natp n) (natp reads) (true-listp buf)
                (<= (+ pos (adt-tp-npk n)) (len w)))
           (equal (cadr (pcko-copy pos n reads pgs-mem buf))
                  (append buf (adt-tp-unpack n (nthcdr pos w)))))
  :hints (("Goal" :use pcko-copy-is-unpack :in-theory (disable pcko-copy-is-unpack pcko-copy))))

(in-theory (disable pcko-unpack-step pcko-npk-step))

; -----------------------------------------------------------------------------
; The model of the tape.  L is the words from the tape's start; a row starts
; with the tag 1.

(defun pcko-ok-treep (d)
  (and (consp d) (eq (car d) :ok) (consp (cdr d))))

(defun pcko-trees (l)
  ; The trees of the rows of L: what `fn-pck-capture-of-pages' makes of the tape.
  (declare (xargs :measure (len l) :verify-guards nil))
  (if (and (consp l) (equal (car l) 1))
      (let ((d (fn-scc-decode-tree (adt-tp-unpack (cadr l) (cddr l)))))
        (cons (if (pcko-ok-treep d) (cadr d) nil)
              (pcko-trees (adt-tp-restf *fn-pck-row-schema* (cdr l)))))
    nil))

(defun pcko-wellp (l)
  ; Every row of L lies within L and decodes.
  (declare (xargs :measure (len l) :verify-guards nil))
  (if (and (consp l) (equal (car l) 1))
      (and (consp (cdr l))
           (<= (+ 2 (adt-tp-npk (cadr l))) (len l))
           (pcko-ok-treep (fn-scc-decode-tree (adt-tp-unpack (cadr l) (cddr l))))
           (pcko-wellp (adt-tp-restf *fn-pck-row-schema* (cdr l))))
    t))

(defun pcko-cost (l)
  ; The words the open reads over L: each row's words, then the one word that
  ; is not a tag.
  (declare (xargs :measure (len l) :verify-guards nil))
  (cond ((atom l) 0)
        ((equal (car l) 1)
         (+ 2 (adt-tp-npk (cadr l)) (pcko-cost (adt-tp-restf *fn-pck-row-schema* (cdr l)))))
        (t 1)))

(defthm pcko-restf-is-nthcdr
  (equal (adt-tp-restf *fn-pck-row-schema* w)
         (nthcdr (adt-tp-npk (car w)) (cdr w)))
  :hints (("Goal" :expand ((adt-tp-restf *fn-pck-row-schema* w)))))

(defthm pcko-trees-is-the-model
  (equal (pcko-trees l)
         (fn-pck-dec-rows (adt-tp-dseq *fn-pck-row-schema* l)))
  :hints (("Goal" :induct (pcko-trees l)
           :in-theory (e/d (fn-pck-dec-row) (adt-tp-restf))
           :expand ((adt-tp-dseq *fn-pck-row-schema* l)
                    (adt-tp-decf *fn-pck-row-schema* (cdr l))))))

(defthm pcko-nw-is-npk
  (implies (natp n) (equal (pcko-nw n) (adt-tp-npk n)))
  :hints (("Goal" :induct (adt-tp-npk n)
           :in-theory (e/d (adt-tp-npk pcko-nw) ()))))

(in-theory (disable pcko-nw))

(defthm pcko-tree-of-list
  (equal (pcko-tree buf)
         (let ((d (fn-scc-decode-tree buf)))
           (if (pcko-ok-treep d) (list :ok (cadr d)) :refused)))
  :hints (("Goal" :in-theory (enable pcko-tree pcko-ok-treep fn-oct-list-is-identity))))

(in-theory (disable pcko-tree pcko-trees-is-the-model))

(defthm pcko-intern-bad-is-absorbing
  (equal (fn-ssr-intern-step :bad ws rs ps mode dicts fn-arena) (mv :bad fn-arena))
  :hints (("Goal" :in-theory (enable fn-ssr-intern-step))))

(defthm pcko-intern-nil
  (equal (fn-ssr-intern-step acc nil rs ps mode dicts fn-arena) (mv acc fn-arena))
  :hints (("Goal" :in-theory (enable fn-ssr-intern-step))))

(defthm pcko-intern-cons
  (implies (syntaxp (not (equal ts ''nil)))
   (equal (fn-ssr-intern-step acc (cons x ts) nil nil :resident nil fn-arena)
         (mv-let (mid fn-arena)
           (fn-ssr-intern-step acc (list x) nil nil :resident nil fn-arena)
           (fn-ssr-intern-step mid ts nil nil :resident nil fn-arena))))
  :hints (("Goal" :use ((:instance fn-ssr-resident-step-of-append (a (list x)) (b ts) (dicts nil)))
           :in-theory (disable fn-ssr-resident-step-of-append))))

(defun pcko-x (pos w)
  ; The tree of the row at POS.
  (declare (xargs :verify-guards nil))
  (cadr (fn-scc-decode-tree (adt-tp-unpack (nfix (nth (+ pos 1) w)) (nthcdr (+ pos 2) w)))))

(defthm pcko-tape-step
  (implies (and (pcko-img w pgs-mem) (natp pos) (< (+ pos 1) (len w)) (equal (nth pos w) 1)
                (natp reads)
                (<= (+ pos 2 (adt-tp-npk (nfix (nth (+ pos 1) w)))) (len w))
                (pcko-ok-treep (fn-scc-decode-tree (adt-tp-unpack (nfix (nth (+ pos 1) w))
                                                                  (nthcdr (+ pos 2) w)))))
           (equal (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets)
                  (mv-let (acc2 fn-arena)
                    (fn-ssr-intern-step acc (list (pcko-x pos w)) nil nil :resident nil fn-arena)
                    (if (eq acc2 :bad)
                        (mv :intern acc2 index (+ reads 2 (adt-tp-npk (nfix (nth (+ pos 1) w))))
                            fn-arena
                            (adt-tp-unpack (nfix (nth (+ pos 1) w)) (nthcdr (+ pos 2) w)))
                      (pcko-tape (+ pos 2 (adt-tp-npk (nfix (nth (+ pos 1) w)))) (len w) (1+ seq) acc2
                                 (fn-cei-put seq (pcko-x pos w) index)
                                 (+ reads 2 (adt-tp-npk (nfix (nth (+ pos 1) w))))
                                 pgs-mem fn-arena
                                 (adt-tp-unpack (nfix (nth (+ pos 1) w)) (nthcdr (+ pos 2) w)))))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :expand ((pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets))
           :in-theory (e/d (pcko-x) (nth nthcdr adt-tp-unpack adt-tp-npk fn-scc-decode-tree
                                     pcko-copy pcko-tape nfix)))))

(defthm pcko-tape-end
  (implies (and (pcko-img w pgs-mem) (natp pos) (<= (len w) pos))
           (equal (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets)
                  (mv :ok acc index reads fn-arena fn-octets)))
  :hints (("Goal" :expand ((pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets)))))

(defthm pcko-tape-not-a-tag
  (implies (and (pcko-img w pgs-mem) (natp pos) (< pos (len w)) (not (equal (nth pos w) 1)))
           (equal (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets)
                  (mv :ok acc index (+ reads 1) fn-arena fn-octets)))
  :hints (("Goal" :expand ((pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets)))))

(defthm pcko-unpack-nfix
  (equal (adt-tp-unpack (nfix n) ws) (adt-tp-unpack n ws))
  :hints (("Goal" :in-theory (enable adt-tp-unpack))))
(defthm pcko-npk-nfix
  (equal (adt-tp-npk (nfix n)) (adt-tp-npk n))
  :hints (("Goal" :in-theory (enable adt-tp-npk))))

(defthm pcko-cdr-nthcdr (implies (natp i) (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l))))
(defthm pcko-cadr-nthcdr (implies (natp i) (equal (cadr (nthcdr i l)) (nth (+ 1 i) l))))
(defthm pcko-nthcdr-nthcdr2 (implies (and (natp i) (natp j)) (equal (nthcdr i (nthcdr j l)) (nthcdr (+ i j) l))))
(defthm pcko-car-nthcdr2 (implies (natp i) (equal (car (nthcdr i l)) (nth i l))))
(defthm pcko-consp-nthcdr (implies (natp i) (equal (consp (nthcdr i l)) (< i (len l)))))

(defthm pcko-tape-stop
  (implies (and (pcko-img w pgs-mem) (natp pos) (<= pos (len w))
                (not (and (< pos (len w)) (equal (nth pos w) 1))))
           (equal (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets)
                  (mv :ok acc index (if (< pos (len w)) (+ reads 1) reads) fn-arena fn-octets)))
  :hints (("Goal" :cases ((< pos (len w)))
           :in-theory (disable pcko-tape))))

(defthm pcko-nfix-natp (implies (natp x) (equal (nfix x) x)))
(defthm pcko-nfix-diff
  (implies (and (natp a) (natp b) (<= b a)) (equal (nfix (+ a (- b))) (+ a (- b)))))

(defun-nx pcko-ind2 (pos seq acc index reads fn-arena fn-octets w)
  (declare (xargs :verify-guards nil :measure (nfix (- (len w) (nfix pos))))
           (ignorable seq index reads fn-octets))
  (if (and (natp pos) (< (+ pos 1) (len w)) (equal (nth pos w) 1)
           (<= (+ pos 2 (adt-tp-npk (nth (+ pos 1) w))) (len w)))
      (mv-let (acc2 fn-arena)
        (fn-ssr-intern-step acc (list (pcko-x pos w)) nil nil :resident nil fn-arena)
        (pcko-ind2 (+ pos 2 (adt-tp-npk (nth (+ pos 1) w))) (1+ seq) acc2
                   (fn-cei-put seq (pcko-x pos w) index)
                   (+ reads 2 (adt-tp-npk (nth (+ pos 1) w))) fn-arena
                   (adt-tp-unpack (nfix (nth (+ pos 1) w)) (nthcdr (+ pos 2) w)) w))
    (mv 0 fn-arena)))

(defthm pcko-tape-is-the-fold
  (implies (and (pcko-img w pgs-mem) (natp pos) (<= pos (len w)) (natp seq) (natp reads)
                (pcko-wellp (nthcdr pos w))
                (not (eq (mv-nth 0 (fn-ssr-intern-step acc (pcko-trees (nthcdr pos w))
                                                       nil nil :resident nil fn-arena))
                         :bad)))
           (let ((ts (pcko-trees (nthcdr pos w))))
             (and (equal (mv-nth 0 (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets))
                         :ok)
                  (equal (mv-nth 1 (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets))
                         (mv-nth 0 (fn-ssr-intern-step acc ts nil nil :resident nil fn-arena)))
                  (equal (mv-nth 2 (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets))
                         (fn-cei-build-aux ts seq index))
                  (equal (mv-nth 3 (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets))
                         (+ reads (pcko-cost (nthcdr pos w))))
                  (equal (mv-nth 4 (pcko-tape pos (len w) seq acc index reads pgs-mem fn-arena fn-octets))
                         (mv-nth 1 (fn-ssr-intern-step acc ts nil nil :resident nil fn-arena))))))
  :hints (("Goal" :induct (pcko-ind2 pos seq acc index reads fn-arena fn-octets w)
           :do-not-induct t
           :in-theory (disable nth nthcdr adt-tp-unpack adt-tp-npk fn-scc-decode-tree
                               pcko-tape pcko-trees pcko-wellp pcko-cost nfix)
           :expand ((pcko-trees (nthcdr pos w)) (pcko-wellp (nthcdr pos w))
                    (pcko-cost (nthcdr pos w))))))

; -----------------------------------------------------------------------------
; The root row, then the tape.

(defun pcko-root (w)
  ; The tree of the root row at the start of W.
  (declare (xargs :verify-guards nil))
  (cadr (fn-scc-decode-tree (adt-tp-unpack (nth 1 w) (nthcdr 2 w)))))

(defthm pcko-open-is-the-fold
  (implies (and (pcko-img w pgs-mem) (natp npg) (<= 8 npg) (equal (len w) (* 2048 npg))
                (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                (equal (nth 0 w) 1)
                (<= (+ 2 (adt-tp-npk (nth 1 w))) 16384)
                (pcko-ok-treep (fn-scc-decode-tree (adt-tp-unpack (nth 1 w) (nthcdr 2 w))))
                (pcko-wellp (nthcdr 16384 w))
                (not (eq (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed (nth 1 (pcko-root w)))
                                                       (pcko-trees (nthcdr 16384 w))
                                                       nil nil :resident nil fn-arena))
                         :bad)))
           (let* ((ts (pcko-trees (nthcdr 16384 w)))
                  (x (pcko-root w))
                  (seed (fn-ssr-seed (nth 1 x))))
             (and (equal (mv-nth 0 (fn-pck-x-open npg pgs-mem fn-arena fn-octets)) :ok)
                  (equal (mv-nth 1 (fn-pck-x-open npg pgs-mem fn-arena fn-octets))
                         (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step seed ts nil nil :resident nil fn-arena))))
                  (equal (mv-nth 2 (fn-pck-x-open npg pgs-mem fn-arena fn-octets))
                         (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x)))
                  (equal (mv-nth 3 (fn-pck-x-open npg pgs-mem fn-arena fn-octets))
                         (fn-cei-build-aux ts 0 nil))
                  (equal (mv-nth 4 (fn-pck-x-open npg pgs-mem fn-arena fn-octets))
                         (+ 2 (adt-tp-npk (nth 1 w)) (pcko-cost (nthcdr 16384 w))))
                  (equal (mv-nth 5 (fn-pck-x-open npg pgs-mem fn-arena fn-octets))
                         (mv-nth 1 (fn-ssr-intern-step seed ts nil nil :resident nil fn-arena))))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-pck-x-open npg pgs-mem fn-arena fn-octets))
           :use ((:instance pcko-tape-is-the-fold (pos 16384) (seq 0) (index nil)
                            (reads (+ 2 (adt-tp-npk (nth 1 w))))
                            (acc (fn-ssr-seed (nth 1 (pcko-root w))))
                            (fn-octets (adt-tp-unpack (nth 1 w) (nthcdr 2 w)))))
           :in-theory (e/d (pcko-root) (nth nthcdr adt-tp-unpack adt-tp-npk fn-scc-decode-tree
                                        pcko-tape pcko-tape-is-the-fold pcko-trees pcko-wellp pcko-cost
                                        fn-ssr-intern-step fn-ssr-seed nfix)))))

; -----------------------------------------------------------------------------
; The rows the writer made are well: the model's own roundtrip, read through the
; exec's accessors.

(defthm pcko-decode-of-program
  (implies (fn-sccb-treep x)
           (equal (fn-scc-decode-tree (fn-scc-program x)) (list :ok x)))
  :hints (("Goal" :use ((:instance fn-scc-decode-tree-of-encode)
                        (:instance fn-sccb-treep-is-treep))
           :in-theory (disable fn-scc-decode-tree-of-encode fn-sccb-treep-is-treep))))

(defthm pcko-wellp-of-seq-words
  (implies (and (fn-pck-sccb-listp recs) (or (atom tail) (not (equal (car tail) 1))))
           (and (pcko-wellp (append (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs)) tail))
                (equal (pcko-trees (append (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs)) tail))
                       recs)))
  :hints (("Goal" :induct (fn-pck-sccb-listp recs)
           :in-theory (e/d (fn-pck-rows fn-pck-sccb-listp fn-pck-enc-row adt-tp-seq-words adt-tp-rw adt-tp-fw)
                           (adt-tp-unpack adt-tp-npk fn-scc-decode-tree)))))

; -----------------------------------------------------------------------------
; The shape of the image the writer's pages flatten to.

(defthm pcko-pad-arith
  (implies (natp n) (equal (+ n (adt-tp-pad n)) (* 2048 (adt-tp-npages n))))
  :hints (("Goal" :induct (adt-tp-npages n)
           :in-theory (enable adt-tp-npages adt-tp-pad))))

(defun pcko-rw0 (tree)
  (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row tree)))

(defthm pcko-rw0-true-listp (true-listp (pcko-rw0 tree)))

(defthm pcko-flat-fit
  (implies (and (true-listp w) (<= (len (adt-tp-pages w)) 8))
           (and (<= (len w) 16384)
                (equal (adt-tp-flat (fn-pck-fit (adt-tp-pages w)))
                       (append w (adt-tp-zeros (- 16384 (len w)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-fit adt-tp-len-pages)
                           (adt-tp-pages adt-tp-flat adt-tp-flat-of-pages pcko-pad-arith))
           :use ((:instance adt-tp-flat-of-pages)
                 (:instance pck-append-zeros (a (adt-tp-pad (len w)))
                            (b (* 2048 (- 8 (adt-tp-npages (len w))))))
                 (:instance pck-flat-zero-pages (n (- 8 (adt-tp-npages (len w)))))
                 (:instance pck-flat-append (p (adt-tp-pages w))
                            (q (fn-pck-zero-pages (- 8 (adt-tp-npages (len w))))))
                 (:instance pcko-pad-arith (n (len w)))))))

(defthm pcko-root-flat
  (implies (fn-pck-root-fitsp configs recs)
           (let ((rw0 (pcko-rw0 (fn-pck-root-tree configs recs))))
             (and (<= (len rw0) 16384)
                  (equal (adt-tp-flat (fn-pck-root-pages-of configs recs))
                         (append rw0 (adt-tp-zeros (- 16384 (len rw0))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-root-pages-of fn-pck-root-pages-of-tree
                            fn-pck-root-fitsp fn-pck-root-fitsp-tree
                            fn-pck-row-pages-of adt-tp-pages-of adt-tp-seq-words pcko-rw0 fn-pck-enc-row)
                           (adt-tp-pages adt-tp-flat adt-tp-flat-of-pages pcko-flat-fit))
           :use ((:instance pcko-flat-fit (w (adt-tp-rw *fn-pck-row-schema*
                                                        (fn-pck-enc-row (fn-pck-root-tree configs recs)))))))))

(defun pcko-tw (recs) (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs)))
(defthm pcko-tw-true-listp (true-listp (pcko-tw recs)))

(defthm pcko-flat-pages
  (implies (fn-pck-root-fitsp configs recs)
           (let* ((rw0 (pcko-rw0 (fn-pck-root-tree configs recs)))
                  (tw (pcko-tw recs)))
             (equal (adt-tp-flat (fn-pck-pages configs recs))
                    (append rw0 (adt-tp-zeros (- 16384 (len rw0)))
                            tw (adt-tp-zeros (adt-tp-pad (len tw)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-pages fn-pck-row-pages-of adt-tp-pages-of pcko-tw)
                           (adt-tp-pages adt-tp-flat adt-tp-flat-of-pages pcko-root-flat fn-pck-root-pages-of))
           :use ((:instance pcko-root-flat)
                 (:instance pck-flat-append (p (fn-pck-root-pages-of configs recs))
                            (q (adt-tp-pages (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs)))))
                 (:instance adt-tp-flat-of-pages (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs))))))))

(defthm pcko-len-pages
  (implies (fn-pck-root-fitsp configs recs)
           (equal (len (fn-pck-pages configs recs))
                  (+ 8 (adt-tp-npages (len (pcko-tw recs))))))
  :hints (("Goal" :in-theory (e/d (fn-pck-pages fn-pck-row-pages-of adt-tp-pages-of pcko-tw adt-tp-len-pages)
                                  (adt-tp-pages)))))

(defthm pcko-nthcdr-16384
  (implies (and (true-listp rw0) (<= (len rw0) 16384))
           (equal (nthcdr 16384 (append rw0 (adt-tp-zeros (- 16384 (len rw0))) rest)) rest))
  :hints (("Goal" :use ((:instance pck-nthcdr-root (r (append rw0 (adt-tp-zeros (- 16384 (len rw0))))) (c rest)))
           :in-theory (disable pck-nthcdr-root))))

(defthm pcko-len-w-gen
  (implies (and (true-listp rw0) (<= (len rw0) 16384) (true-listp tw))
           (equal (len (append rw0 (adt-tp-zeros (- 16384 (len rw0))) tw (adt-tp-zeros (adt-tp-pad (len tw)))))
                  (+ 16384 (* 2048 (adt-tp-npages (len tw))))))
  :hints (("Goal" :use ((:instance pcko-pad-arith (n (len tw)))))))

(defthm pcko-len-w
  (implies (fn-pck-root-fitsp configs recs)
           (equal (len (adt-tp-flat (fn-pck-pages configs recs)))
                  (* 2048 (len (fn-pck-pages configs recs)))))
  :hints (("Goal" :in-theory (disable pcko-flat-pages pcko-len-w-gen pcko-len-pages pcko-root-flat
                                      pcko-rw0 pcko-tw adt-tp-rw fn-pck-enc-row fn-pck-pages)
           :use ((:instance pcko-flat-pages) (:instance pcko-len-pages)
                 (:instance pcko-root-flat)
                 (:instance pcko-len-w-gen (rw0 (pcko-rw0 (fn-pck-root-tree configs recs)))
                            (tw (pcko-tw recs)))))))

(defthm pcko-w-tape
  (implies (fn-pck-root-fitsp configs recs)
           (equal (nthcdr 16384 (adt-tp-flat (fn-pck-pages configs recs)))
                  (append (pcko-tw recs) (adt-tp-zeros (adt-tp-pad (len (pcko-tw recs)))))))
  :hints (("Goal" :in-theory (e/d () (pcko-flat-pages pcko-nthcdr-16384 fn-pck-pages pcko-rw0 pcko-tw))
           :use ((:instance pcko-flat-pages)
                 (:instance pcko-root-flat)
                 (:instance pcko-nthcdr-16384 (rw0 (pcko-rw0 (fn-pck-root-tree configs recs)))
                            (rest (append (pcko-tw recs) (adt-tp-zeros (adt-tp-pad (len (pcko-tw recs)))))))))))

(defthm pcko-w-tape-well
  (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs))
           (and (pcko-wellp (nthcdr 16384 (adt-tp-flat (fn-pck-pages configs recs))))
                (equal (pcko-trees (nthcdr 16384 (adt-tp-flat (fn-pck-pages configs recs)))) recs)))
  :hints (("Goal" :in-theory (e/d (fn-pck-recordsp pcko-tw) (pcko-w-tape pcko-wellp-of-seq-words fn-pck-pages))
           :use ((:instance pcko-w-tape)
                 (:instance pcko-wellp-of-seq-words
                            (tail (adt-tp-zeros (adt-tp-pad (len (pcko-tw recs)))))
                            (recs recs))
                 (:instance adt-tp-car-zeros (n (adt-tp-pad (len (pcko-tw recs)))))))))

(defthm pcko-rw0-is
  (equal (pcko-rw0 x)
         (cons 1 (cons (len (fn-scc-program x)) (adt-tp-pack (fn-scc-program x)))))
  :hints (("Goal" :in-theory (enable pcko-rw0) :use pckx-row-of-program)))

(defthm pcko-w-root
  (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs))
           (let ((w (adt-tp-flat (fn-pck-pages configs recs)))
                 (x (fn-pck-root-tree configs recs)))
             (and (equal (nth 0 w) 1)
                  (equal (nth 1 w) (len (fn-scc-program x)))
                  (<= (+ 2 (adt-tp-npk (nth 1 w))) 16384)
                  (pcko-ok-treep (fn-scc-decode-tree (adt-tp-unpack (nth 1 w) (nthcdr 2 w))))
                  (equal (pcko-root w) x))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-recordsp pcko-root) (fn-pck-pages pcko-root-flat pcko-rw0
                                                       pcko-tw adt-tp-unpack adt-tp-npk
                                                       adt-tp-rw fn-pck-enc-row fn-scc-decode-tree
                                                       pcko-rw0-is))
           :use ((:instance pcko-root-flat)
                 (:instance pcko-rw0-is (x (fn-pck-root-tree configs recs)))
                 (:instance pckx-row-of-program (x (fn-pck-root-tree configs recs)))
                 (:instance pck-program-octetsp (x (fn-pck-root-tree configs recs)))
                 (:instance adt-tp-unpack-of-pack (o (fn-scc-program (fn-pck-root-tree configs recs)))
                            (r (append (adt-tp-zeros (- 16384 (len (pcko-rw0 (fn-pck-root-tree configs recs)))))
                                       (pcko-tw recs)
                                       (adt-tp-zeros (adt-tp-pad (len (pcko-tw recs)))))))
                 (:instance pcko-decode-of-program (x (fn-pck-root-tree configs recs)))
                 (:instance adt-tp-len-pack (o (fn-scc-program (fn-pck-root-tree configs recs))))))))

; -----------------------------------------------------------------------------
; The rows the intern fold leaves read back as the records it was given.  The
; seal survival lemmas are store-intern's local ones, restated.

(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-seal-list-is-append fn-arena-p-is-payload-listp
                           fn-arena-get-is-nth fn-arena-payload-len-is-len-nth)))

(defthm pcko-row-wire-of-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
           (equal (fn-row-wire-of row (fn-arena-seal-list xs fn-arena))
                  (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-wire-of fn-rows-handles-inp fn-held-wire-of
                                     fn-row-handle-inp fn-row-bytes))))

(defthm pcko-rows-handles-survive-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (fn-rows-handles-inp rows (fn-arena-seal-list xs fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (enable fn-rows-handles-inp))))

(defthm pcko-rows-wire-of-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (equal (fn-rows-wire-of rows (fn-arena-seal-list xs fn-arena))
                  (fn-rows-wire-of rows fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (enable fn-rows-handles-inp fn-rows-wire-of fn-row-wire-of))))

(defthm pcko-intern-event-wire-p
  (implies (not (eq (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad))
           (fn-wire-event-p w))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-wire-event-p)
                                  (fn-cat-intern-list fn-replay-composite-record)))))

(defthm pcko-rows-survive-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (and (fn-rows-handles-inp rows (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                (equal (fn-rows-wire-of rows (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                       (fn-rows-wire-of rows fn-arena))))
  :hints (("Goal" :use ((:instance fn-intern-event-arena)
                        (:instance pcko-rows-handles-survive-seal
                                   (xs (fn-record-payload w)))
                        (:instance pcko-rows-wire-of-survives-seal
                                   (xs (fn-record-payload w)))
                        (:instance pcko-rows-handles-survive-seal
                                   (xs (fn-record-payload (fn-replay-composite-record w))))
                        (:instance pcko-rows-wire-of-survives-seal
                                   (xs (fn-record-payload (fn-replay-composite-record w)))))
           :in-theory (disable fn-intern-event-arena pcko-rows-handles-survive-seal
                               pcko-rows-wire-of-survives-seal fn-intern-event))))

(defthm pcko-arena-p-of-intern-event
  (implies (and (fn-arena-p fn-arena)
                (not (eq (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :use ((:instance pcko-intern-event-wire-p)
                        (:instance fn-intern-events-arena-p (ws (list w))))
           :in-theory (e/d (fn-intern-events fn-wire-event-listp)
                           (pcko-intern-event-wire-p fn-intern-events-arena-p
                            fn-intern-event fn-wire-event-p fn-record-p)))))

(defthm pcko-handles-of-cons
  (implies (syntaxp (not (equal rs ''nil)))
           (equal (fn-rows-handles-inp (cons r rs) fn-arena)
                  (and (fn-rows-handles-inp (list r) fn-arena) (fn-rows-handles-inp rs fn-arena))))
  :hints (("Goal" :in-theory (enable fn-rows-handles-inp))))

(defthm pcko-intern-event-one
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-rows-handles-inp rows fn-arena)
                (not (eq (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (let ((row (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                 (ar1 (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
             (and (fn-arena-p ar1)
                  (fn-rows-handles-inp (cons row rows) ar1)
                  (equal (fn-rows-wire-of (cons row rows) ar1)
                         (cons w (fn-rows-wire-of rows fn-arena))))))
  :hints (("Goal" :in-theory (e/d (fn-rows-wire-of)
                                  (fn-intern-event pcko-rows-survive-intern-event
                                   fn-intern-event-handle-in fn-intern-event-materializes
                                   fn-rows-handles-inp fn-row-wire-of))
           :use ((:instance pcko-rows-survive-intern-event)
                 (:instance fn-intern-event-handle-in)
                 (:instance fn-intern-event-materializes)
                 (:instance pcko-arena-p-of-intern-event)
                 (:instance pcko-handles-of-cons (r (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                            (rs rows) (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))))))

(defthm pcko-statep-generation
  (implies (fn-ssr-statep acc) (natp (fn-ssr-at 2 acc)))
  :hints (("Goal" :in-theory (enable fn-ssr-statep))))

(defthm pcko-publish-rows
  (equal (fn-ssr-at 0 (fn-ssr-publish acc row wire identity))
         (cons row (fn-ssr-at 0 acc)))
  :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at))))

(defthm pcko-intern-materializes
  (implies (and (fn-arena-p fn-arena) (fn-ssr-statep acc)
                (fn-rows-handles-inp (fn-ssr-at 0 acc) fn-arena)
                (not (eq (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident nil fn-arena)) :bad)))
           (let ((acc2 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident nil fn-arena)))
                 (ar2 (mv-nth 1 (fn-ssr-intern-step acc ws nil nil :resident nil fn-arena))))
             (and (fn-arena-p ar2)
                  (fn-rows-handles-inp (fn-ssr-at 0 acc2) ar2)
                  (equal (fn-rows-wire-of (fn-ssr-at 0 acc2) ar2)
                         (revappend ws (fn-rows-wire-of (fn-ssr-at 0 acc) fn-arena))))))
  :hints (("Goal" :induct (fn-ssr-intern-step acc ws nil nil :resident nil fn-arena)
           :in-theory (e/d (fn-ssr-intern-step)
                           (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                            fn-replay-identity-step fn-ssr-publish fn-ssr-at fn-stxk-context-kind
                            pcko-intern-cons fn-rows-handles-inp fn-rows-wire-of pcko-handles-of-cons mv-nth)))))
