; fn: the history's FNADTSN2 image with its regions placed anywhere (lane
; arena-store-3, 2026-09-28).  Prefix fn-hp-.
;
; The canonical image (`fn-hp-iw') places the regions in order after the
; header.  FNADTSN2 lets a region lie anywhere the header says
; (`adt-placement-ok'), so a region that outgrows its pages moves to new
; pages at the image's end and nothing else moves.  The PLACED image
; (`fn-hp-piw' H SALT STARTS NP) is NP pages of zeros with the header page
; (naming STARTS and NP) and each region's padded words at its start
; written in; pages no region holds are zero in the model and unread by
; every reader.
(in-package "ACL2")
(include-book "history-pages-write-keys")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite pgs-x-nfix-when-natp))))

(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; A. Blocks apart: the word at K after a list of replacements.

(defun fn-hp-bj (b) (declare (xargs :guard (consp b))) (nfix (car b)))
(defun fn-hp-bw (b) (declare (xargs :guard (consp b))) (true-list-fix (cdr b)))

(defun fn-hp-in-block (k b)
  ; word K lies in block B
  (declare (xargs :guard (and (natp k) (consp b))))
  (and (<= (fn-hp-bj b) (nfix k)) (< (nfix k) (+ (fn-hp-bj b) (len (fn-hp-bw b))))))

(defun fn-hp-block-at (k blocks)
  ; the first block holding word K, or nil
  (declare (xargs :guard (and (natp k) (alistp blocks))))
  (if (atom blocks) nil
    (if (fn-hp-in-block k (car blocks)) (car blocks) (fn-hp-block-at k (cdr blocks)))))

(defun fn-hp-pair-apart (b c)
  ; blocks B and C share no word (an empty block shares none)
  (declare (xargs :guard (and (consp b) (consp c))))
  (or (atom (fn-hp-bw b)) (atom (fn-hp-bw c))
      (<= (+ (fn-hp-bj b) (len (fn-hp-bw b))) (fn-hp-bj c))
      (<= (+ (fn-hp-bj c) (len (fn-hp-bw c))) (fn-hp-bj b))))

(defun fn-hp-block-apart (b blocks)
  ; B shares no word with any block of BLOCKS
  (declare (xargs :guard (and (consp b) (alistp blocks))))
  (if (atom blocks) t
    (and (fn-hp-pair-apart b (car blocks)) (fn-hp-block-apart b (cdr blocks)))))

(defun fn-hp-blocks-apart (blocks)
  (declare (xargs :guard (alistp blocks)))
  (if (atom blocks) t
    (and (fn-hp-block-apart (car blocks) (cdr blocks)) (fn-hp-blocks-apart (cdr blocks)))))

(defthm fn-hp-pair-apart-not-in
  (implies (and (fn-hp-pair-apart b c) (fn-hp-in-block k b))
           (not (fn-hp-in-block k c)))
  :rule-classes nil)

(defthm fn-hp-block-at-apart
  (implies (and (fn-hp-block-apart b blocks) (fn-hp-in-block k b))
           (not (fn-hp-block-at k blocks)))
  :hints (("Goal" :induct (fn-hp-block-at k blocks) :in-theory (disable fn-hp-in-block fn-hp-pair-apart))
          ("Subgoal *1/2" :use ((:instance fn-hp-pair-apart-not-in (c (car blocks)))))))

(defthm fn-hp-block-apart-member
  (implies (and (fn-hp-block-apart c rest) (member-equal b rest))
           (fn-hp-pair-apart c b))
  :hints (("Goal" :in-theory (disable fn-hp-pair-apart))))

(defthm fn-hp-pair-apart-sym
  (implies (fn-hp-pair-apart b c) (fn-hp-pair-apart c b)))

(defthm fn-hp-block-at-member
  (implies (and (fn-hp-blocks-apart blocks) (member-equal b blocks) (fn-hp-in-block k b))
           (equal (fn-hp-block-at k blocks) b))
  :hints (("Goal" :induct (fn-hp-block-at k blocks) :in-theory (disable fn-hp-in-block fn-hp-pair-apart))
          ("Subgoal *1/2" :use ((:instance fn-hp-pair-apart-not-in (b b) (c (car blocks)))
                                (:instance fn-hp-block-apart-member (c (car blocks)) (rest (cdr blocks)))
                                (:instance fn-hp-pair-apart-sym (b (car blocks)) (c b))))))

(defthm fn-hp-nth-rep-block
  (implies (natp k)
           (equal (nth k (fn-hp-rep w (nfix (car b)) (true-list-fix (cdr b))))
                  (if (fn-hp-in-block k b) (nth (- k (fn-hp-bj b)) (fn-hp-bw b)) (nth k w)))))

(defthm fn-hp-not-in-empty-block
  (implies (atom (fn-hp-bw b)) (not (fn-hp-in-block k b))))

(defthm fn-hp-nth-wreps-outside
  (implies (and (natp k) (not (fn-hp-block-at k blocks)))
           (equal (nth k (fn-hp-wreps w blocks)) (nth k w)))
  :hints (("Goal" :induct (fn-hp-wreps w blocks) :expand ((fn-hp-block-at k blocks))
           :in-theory (disable fn-hp-rep fn-hp-nth-rep-block fn-hp-block-at-member fn-hp-blocks-apart nth))))

(defthm fn-hp-nth-wreps
  (implies (and (natp k) (fn-hp-blocks-apart blocks))
           (equal (nth k (fn-hp-wreps w blocks))
                  (if (fn-hp-block-at k blocks)
                      (nth (- k (fn-hp-bj (fn-hp-block-at k blocks))) (fn-hp-bw (fn-hp-block-at k blocks)))
                    (nth k w))))
  :hints (("Goal" :induct (fn-hp-wreps w blocks) :expand ((fn-hp-block-at k blocks))
           :in-theory (disable fn-hp-rep fn-hp-nth-rep-block fn-hp-block-at-member fn-hp-pair-apart nth))))

(defun fn-hp-blocks-within (blocks n)
  ; every block inside N words
  (declare (xargs :guard (and (alistp blocks) (natp n))))
  (if (atom blocks) t
    (and (<= (+ (fn-hp-bj (car blocks)) (len (fn-hp-bw (car blocks)))) (nfix n))
         (fn-hp-blocks-within (cdr blocks) n))))

(defthm fn-hp-len-wreps
  (implies (fn-hp-blocks-within blocks (len w))
           (equal (len (fn-hp-wreps w blocks)) (len w)))
  :hints (("Goal" :induct (fn-hp-wreps w blocks))))

(defthm fn-hp-true-listp-wreps
  (implies (true-listp w) (true-listp (fn-hp-wreps w blocks))))

; Extensionality: two true lists of one length that agree word by word.
(defthm fn-hp-equal-by-agree
  (implies (and (true-listp x) (true-listp y) (equal (len x) (len y)) (fn-hp-agree 0 (len x) x y))
           (equal x y))
  :hints (("Goal" :use ((:instance fn-hp-agree-is-take (a 0) (n (len x))))
           :in-theory (disable fn-hp-agree-is-take fn-hp-agree)))
  :rule-classes nil)

(defun fn-hp-agree2 (a b n x y)
  ; words A.. of X are words B.. of Y, N of them
  (declare (xargs :guard (and (natp a) (natp b) (natp n) (true-listp x) (true-listp y)) :measure (nfix n)))
  (if (zp n) t
    (and (equal (nth a x) (nth b y)) (fn-hp-agree2 (+ 1 (nfix a)) (+ 1 (nfix b)) (1- n) x y))))

(local
 (defthm fn-hp-take-nthcdr-open-2
   (implies (and (natp a) (posp n))
            (equal (take n (nthcdr a x)) (cons (nth a x) (take (1- n) (nthcdr (+ 1 a) x)))))
   :hints (("Goal" :in-theory (enable take nthcdr nth)))))

(defthm fn-hp-agree2-take
  (implies (and (natp a) (natp b) (fn-hp-agree2 a b n x y))
           (equal (take n (nthcdr a x)) (take n (nthcdr b y))))
  :hints (("Goal" :induct (fn-hp-agree2 a b n x y) :in-theory (disable nth nthcdr take))
          ("Subgoal *1/1" :in-theory (enable take))))

(local (in-theory (disable fn-hp-take-nthcdr-open-2)))

; -----------------------------------------------------------------------------
; B. The placed image.

(defun fn-hp-hdr2 (n lens starts np)
  ; the header page's words: magic, version, the schema digest, N, R, the
  ; region table, NPAGES, zeros
  (declare (xargs :guard (and (true-listp lens) (true-listp starts))))
  (append (list *fn-hp-magic-word* *adt-version*) *fn-hp-schema-words* (list n 5)
          (fn-hp-meta-words starts lens) (list np) (adt-zeros 2029)))

(defun fn-hp-rblocks (regs starts)
  ; each region's padded words at its start
  (declare (xargs :verify-guards nil))
  (if (or (atom regs) (atom starts)) nil
    (cons (cons (* 2048 (nfix (car starts))) (fn-hp-wpad (car regs)))
          (fn-hp-rblocks (cdr regs) (cdr starts)))))

(defun fn-hp-piw (h salt starts np)
  ; THE placed image's words: NP pages; the header page, each region at its
  ; start, zeros elsewhere
  (declare (xargs :verify-guards nil))
  (fn-hp-wreps (adt-zeros (* 2048 (nfix np)))
               (cons (cons 0 (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
                     (fn-hp-rblocks (fn-hp-regs h salt) starts))))

(defthm fn-hp-len-hdr2
  (implies (equal (len starts) 5) (equal (len (fn-hp-hdr2 n lens starts np)) 2048)))

(defthm fn-hp-true-listp-hdr2 (true-listp (fn-hp-hdr2 n lens starts np)))

; The canonical placement is the canonical image.
(local
 (defthm fn-hp-zeros-plus
   (implies (and (natp a) (natp b)) (equal (adt-zeros (+ a b)) (append (adt-zeros a) (adt-zeros b))))
   :hints (("Goal" :induct (adt-zeros a)))))

(local
 (defthm fn-hp-rep-into-zeros
   (implies (and (true-listp p) (true-listp x) (natp m) (<= (len x) m))
            (equal (fn-hp-rep (append p (adt-zeros m)) (len p) x)
                   (append p x (adt-zeros (- m (len x))))))
   :hints (("Goal" :in-theory (enable fn-hp-rep)
            :use ((:instance fn-hp-take-past-prefix (j 0) (z (adt-zeros m)))
                  (:instance fn-hp-nthcdr-past-prefix (j (len x)) (z (adt-zeros m))))))))

(local
 (defun fn-hp-rb-ind (regs base p)
   (declare (xargs :verify-guards nil))
   (if (atom regs) (list base p)
     (fn-hp-rb-ind (cdr regs) (+ (nfix base) (adt-cap (len (car regs)))) (append p (fn-hp-wpad (car regs)))))))

(defthm fn-hp-rblocks-contiguous
  (implies (and (true-listp p) (natp base) (equal (len p) (* 2048 base)))
           (equal (fn-hp-wreps (append p (adt-zeros (* 2048 (fn-hp-caps-sum regs))))
                               (fn-hp-rblocks regs (adt-starts regs base)))
                  (append p (fn-hp-wbody regs))))
  :hints (("Goal" :induct (fn-hp-rb-ind regs base p) :in-theory (disable adt-cap fn-hp-wpad))
          ("Subgoal *1/2" :use ((:instance fn-hp-rep-into-zeros (x (fn-hp-wpad (car regs)))
                                           (m (* 2048 (fn-hp-caps-sum regs))))
                                (:instance fn-hp-zeros-plus (a (* 2048 (adt-cap (len (car regs)))))
                                           (b (* 2048 (fn-hp-caps-sum (cdr regs)))))))))

(local
 (defthm fn-hp-pack8-hdr-const
   (equal (fn-hp-pack8 2 (adt-hdr-const)) (list *fn-hp-magic-word* *adt-version*))
   :hints (("Goal" :in-theory (enable (:e adt-hdr-const))))))

(local
 (defun fn-hp-uz-ind (w m) (if (zp w) (list w m) (fn-hp-uz-ind (1- w) (1- m)))))

(local
 (defthm fn-hp-unle-zeros
   (equal (adt-unle w (adt-zeros m)) 0)
   :hints (("Goal" :induct (fn-hp-uz-ind w m) :in-theory (enable adt-unle adt-zeros)))))

(local
 (defthm fn-hp-pack8-zeros
   (implies (natp k) (equal (fn-hp-pack8 k (adt-zeros (* 8 k))) (adt-zeros k)))
   :hints (("Goal" :induct (adt-zeros k) :in-theory (disable adt-unle))
           ("Subgoal *1/2" :expand ((fn-hp-pack8 k (adt-zeros (* 8 k))))
            :use ((:instance fn-hp-nthcdr-of-zeros (m 8) (z (* 8 k))))))))

(local
 (defthm fn-hp-len-hdr-const (equal (len (adt-hdr-const)) 16)))

(local
 (defthm fn-hp-schema-words-is
   (equal (fn-hp-pack8 4 (adt-schema-digest *fn-hp-schema*)) *fn-hp-schema-words*)))

(defthm fn-hp-header-words-canonical
  (implies (and (equal (len regs) 5) (unsigned-byte-p 64 n)
                (fn-hp-u64-listp (adt-starts regs 1)) (fn-hp-u64-listp (adt-lens regs))
                (unsigned-byte-p 64 (adt-end regs 1)))
           (equal (fn-hp-pack8 2048 (adt-header *fn-hp-schema* n regs))
                  (fn-hp-hdr2 n (adt-lens regs) (adt-starts regs 1) (adt-end regs 1))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-pack8-append (k1 2) (k2 2046) (x (adt-hdr-const))
                            (y (append (adt-schema-digest *fn-hp-schema*) (adt-le 8 n) (adt-le 8 5)
                                       (adt-meta (adt-starts regs 1) (adt-lens regs)) (adt-le 8 (adt-end regs 1))
                                       (adt-zeros 16232))))
                 (:instance fn-hp-pack8-append (k1 4) (k2 2042) (x (adt-schema-digest *fn-hp-schema*))
                            (y (append (adt-le 8 n) (adt-le 8 5)
                                       (adt-meta (adt-starts regs 1) (adt-lens regs)) (adt-le 8 (adt-end regs 1))
                                       (adt-zeros 16232))))
                 (:instance fn-hp-pack8-append (k1 10) (k2 2030) (x (adt-meta (adt-starts regs 1) (adt-lens regs)))
                            (y (append (adt-le 8 (adt-end regs 1)) (adt-zeros 16232))))
                 (:instance fn-hp-pack8-meta (starts (adt-starts regs 1)) (lens (adt-lens regs)))
                 (:instance fn-hp-pack8-zeros (k 2029)))
           :in-theory (e/d (adt-header adt-header-content)
                           (fn-hp-pack8-append fn-hp-pack8-meta fn-hp-pack8-zeros fn-hp-pack8 adt-le adt-meta adt-starts
                            adt-lens adt-end adt-starts-is-starts-l adt-end-is-end-l adt-zeros fn-hp-end-is-caps-sum
                            (:e adt-zeros) (:e adt-le) (:e adt-schema-digest) (:e fn-hp-pack8) (:e adt-hdr-const))))))

(local
 (defthm fn-hp-u64-listp-of-all-below
   (implies (and (nat-listp xs) (adt-all-below xs 18446744073709551616)) (fn-hp-u64-listp xs))))

(local
 (defthm fn-hp-nat-listp-starts-l-x
   (implies (natp s) (nat-listp (adt-starts-l lens s)))))

(defthm fn-hp-okp-u64-facts
  (implies (fn-hp-okp h salt)
           (and (unsigned-byte-p 64 (len h))
                (fn-hp-u64-listp (adt-starts (fn-hp-regs h salt) 1))
                (fn-hp-u64-listp (adt-lens (fn-hp-regs h salt)))
                (unsigned-byte-p 64 (adt-end (fn-hp-regs h salt) 1))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-ser-okp-bounds (s *fn-hp-schema*) (a (fn-hp-rows h salt)))
                 (:instance fn-hp-ser-okp)
                 (:instance adt-end-l-lower (lens (adt-lens (fn-hp-regs h salt))) (start 1)))
           :in-theory (e/d (fn-hp-okp fn-hp-regs fn-hp-image)
                           (adt-ser-okp-bounds fn-hp-ser-okp adt-ser adt-regs fn-hp-rows adt-starts-l adt-end-l adt-lens
                            adt-ser-okp adt-end-l-lower)))))

; The canonical placement: the placed image at the canonical starts and page
; count IS the canonical image.
(defthm fn-hp-piw-canonical
  (implies (fn-hp-okp h salt)
           (equal (fn-hp-piw h salt (fn-hp-starts h salt) (fn-hp-npages h salt))
                  (fn-hp-iw h salt)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-okp-u64-facts)
                 (:instance fn-hp-starts-is-adt-starts)
                 (:instance fn-hp-npages-is-caps-sum)
                 (:instance fn-hp-iw-split)
                 (:instance fn-hp-header-words-canonical (n (len h)) (regs (fn-hp-regs h salt)))
                 (:instance fn-hp-end-is-caps-sum (regs (fn-hp-regs h salt)) (s 1))
                 (:instance fn-hp-rep-into-zeros (p nil)
                            (x (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt)))
                            (m (* 2048 (fn-hp-npages h salt))))
                 (:instance fn-hp-zeros-plus (a 2048) (b (* 2048 (fn-hp-caps-sum (fn-hp-regs h salt)))))
                 (:instance fn-hp-rblocks-contiguous (base 1) (regs (fn-hp-regs h salt))
                            (p (fn-hp-hdr2 (len h) (fn-hp-lens h salt) (fn-hp-starts h salt) (fn-hp-npages h salt)))))
           :in-theory (e/d (fn-hp-piw fn-hp-lens)
                           (fn-hp-okp-u64-facts fn-hp-iw-split fn-hp-header-words-canonical fn-hp-end-is-caps-sum
                            fn-hp-rep-into-zeros fn-hp-zeros-plus fn-hp-rblocks-contiguous fn-hp-hdr2 fn-hp-rblocks
                            fn-hp-iw fn-hp-regs fn-hp-starts fn-hp-npages fn-hp-okp adt-starts adt-lens adt-end
                            adt-header fn-hp-wbody fn-hp-pack8 adt-zeros fn-hp-caps-sum adt-starts-is-starts-l
                            adt-end-is-end-l fn-hp-npages-is-end-l fn-hp-wreps (:e adt-zeros)))
           :expand ((fn-hp-wreps (adt-zeros (* 2048 (fn-hp-npages h salt)))
                                 (cons (cons 0 (fn-hp-hdr2 (len h) (adt-lens (fn-hp-regs h salt))
                                                           (fn-hp-starts h salt) (fn-hp-npages h salt)))
                                       (fn-hp-rblocks (fn-hp-regs h salt) (fn-hp-starts h salt))))))))

; -----------------------------------------------------------------------------
; C. A placement keeps the blocks apart and inside the image.

(local
 (defthm fn-hp-consp-iff-len
   (iff (consp x) (< 0 (len x)))))

(local
 (defthm fn-hp-wpad-empty-iff
   (iff (consp (fn-hp-wpad r)) (not (zp (adt-cap (len r)))))
   :hints (("Goal" :use ((:instance fn-hp-len-wpad) (:instance fn-hp-consp-iff-len (x (fn-hp-wpad r))))
            :in-theory (disable fn-hp-len-wpad adt-cap fn-hp-consp-iff-len)))))

(local (in-theory (disable fn-hp-consp-iff-len)))

(defthm fn-hp-rblocks-apart-of-adt-apart
  (implies (and (adt-apart s c starts (adt-lens regs)) (natp s) (equal c (adt-cap (len r))))
           (fn-hp-block-apart (cons (* 2048 s) (fn-hp-wpad r)) (fn-hp-rblocks regs starts)))
  :hints (("Goal" :induct (fn-hp-rblocks regs starts) :in-theory (disable adt-cap fn-hp-wpad))))

(defthm fn-hp-rblocks-apart
  (implies (adt-placement-ok starts (adt-lens regs) np)
           (fn-hp-blocks-apart (fn-hp-rblocks regs starts)))
  :hints (("Goal" :induct (fn-hp-rblocks regs starts) :in-theory (disable adt-cap fn-hp-wpad))))

(defthm fn-hp-hdr-apart-rblocks
  (implies (and (adt-placement-ok starts (adt-lens regs) np) (equal (len hdr) 2048))
           (fn-hp-block-apart (cons 0 hdr) (fn-hp-rblocks regs starts)))
  :hints (("Goal" :induct (fn-hp-rblocks regs starts) :in-theory (disable adt-cap fn-hp-wpad))))

(defthm fn-hp-rblocks-within
  (implies (adt-placement-ok starts (adt-lens regs) np)
           (fn-hp-blocks-within (fn-hp-rblocks regs starts) (* 2048 np)))
  :hints (("Goal" :induct (fn-hp-rblocks regs starts) :in-theory (disable adt-cap fn-hp-wpad))))

(local
 (defun fn-hp-nr-ind (r regs starts)
   (if (or (zp r) (atom regs)) (list regs starts) (fn-hp-nr-ind (1- r) (cdr regs) (cdr starts)))))

(defthm fn-hp-nth-rblocks
  (implies (and (natp r) (< r (len regs)) (< r (len starts)))
           (equal (nth r (fn-hp-rblocks regs starts))
                  (cons (* 2048 (nfix (nth r starts))) (fn-hp-wpad (nth r regs)))))
  :hints (("Goal" :induct (fn-hp-nr-ind r regs starts) :in-theory (e/d (nth) (fn-hp-wpad)))))

(defthm fn-hp-member-nth
  (implies (and (natp r) (< r (len l))) (member-equal (nth r l) l))
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-hp-len-rblocks
  (implies (equal (len starts) (len regs)) (equal (len (fn-hp-rblocks regs starts)) (len regs))))

(defthm fn-hp-placement-natp-start
  (implies (and (adt-placement-ok starts lens np) (natp r) (< r (len starts)) (< r (len lens)))
           (and (natp (nth r starts)) (<= 1 (nth r starts))
                (<= (+ (nth r starts) (adt-cap (nfix (nth r lens)))) (nfix np))))
  :hints (("Goal" :induct (fn-hp-nr-ind r starts lens) :in-theory (e/d (nth) (adt-cap))))
  :rule-classes nil)

; The relocation lemma: word I of region R is word I of its padded words,
; wherever the placement puts it.
(defthm fn-hp-piw-region-word
  (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5)
                (natp r) (< r 5) (natp i) (< i (* 2048 (adt-cap (len (nth r (fn-hp-regs h salt)))))))
           (equal (nth (+ (* 2048 (nth r starts)) i) (fn-hp-piw h salt starts np))
                  (nth i (fn-hp-wpad (nth r (fn-hp-regs h salt))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-placement-natp-start (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-nth-wreps (k (+ (* 2048 (nth r starts)) i)) (w (adt-zeros (* 2048 (nfix np))))
                            (blocks (cons (cons 0 (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
                                          (fn-hp-rblocks (fn-hp-regs h salt) starts))))
                 (:instance fn-hp-block-at-member (k (+ (* 2048 (nth r starts)) i))
                            (blocks (cons (cons 0 (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
                                          (fn-hp-rblocks (fn-hp-regs h salt) starts)))
                            (b (nth r (fn-hp-rblocks (fn-hp-regs h salt) starts))))
                 (:instance fn-hp-member-nth (l (fn-hp-rblocks (fn-hp-regs h salt) starts)))
                 (:instance fn-hp-rblocks-apart (regs (fn-hp-regs h salt)))
                 (:instance fn-hp-hdr-apart-rblocks (regs (fn-hp-regs h salt))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))))
           :in-theory (e/d (fn-hp-piw fn-hp-lens)
                           (fn-hp-nth-wreps fn-hp-block-at-member fn-hp-member-nth
                            fn-hp-rblocks-apart fn-hp-hdr-apart-rblocks fn-hp-wreps fn-hp-rblocks fn-hp-hdr2
                            fn-hp-regs adt-placement-ok adt-cap fn-hp-block-at)))))

(defthm fn-hp-piw-word-is-iw-word
  (implies (and (fn-hp-okp h salt) (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5)
                (natp r) (< r 5) (natp i) (< i (* 2048 (adt-cap (len (nth r (fn-hp-regs h salt)))))))
           (equal (nth (+ (* 2048 (nth r starts)) i) (fn-hp-piw h salt starts np))
                  (nth (+ (* 2048 (nth r (fn-hp-starts h salt))) i) (fn-hp-iw h salt))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-piw-region-word)
                 (:instance fn-hp-piw-region-word (starts (fn-hp-starts h salt)) (np (fn-hp-npages h salt)))
                 (:instance fn-hp-piw-canonical)
                 (:instance fn-hp-placement-ok-of-image)
                 (:instance fn-hp-len-starts))
           :in-theory (disable fn-hp-piw-region-word fn-hp-piw-canonical fn-hp-placement-ok-of-image fn-hp-len-starts
                               fn-hp-piw fn-hp-iw fn-hp-starts fn-hp-npages fn-hp-lens fn-hp-regs fn-hp-okp
                               adt-placement-ok adt-cap fn-hp-wpad))))

(local
 (defthm fn-hp-natp-nth-starts-x
   (implies (and (natp r) (< r 5)) (natp (nth r (fn-hp-starts h salt))))
   :hints (("Goal" :use ((:instance fn-hp-starts-okp-of-starts) (:instance fn-hp-nfix-nth-starts (starts (fn-hp-starts h salt))))
            :in-theory (disable fn-hp-starts-okp-of-starts fn-hp-nfix-nth-starts fn-hp-starts)))
   :rule-classes nil))

(local
 (defun fn-hp-pool-ind (o k)
   (if (zp k) (list o k) (fn-hp-pool-ind (+ 1 o) (1- k)))))

(defthm fn-hp-piw-agree-iw
  (implies (and (fn-hp-okp h salt) (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5)
                (natp r) (< r 5) (natp o) (natp k) (<= (+ o k) (* 2048 (adt-cap (len (nth r (fn-hp-regs h salt)))))))
           (fn-hp-agree2 (+ (* 2048 (nth r starts)) o) (+ (* 2048 (nth r (fn-hp-starts h salt))) o) k
                         (fn-hp-piw h salt starts np) (fn-hp-iw h salt)))
  :hints (("Goal" :induct (fn-hp-pool-ind o k)
           :in-theory (disable fn-hp-piw fn-hp-iw fn-hp-starts fn-hp-npages fn-hp-lens fn-hp-regs fn-hp-okp
                               adt-placement-ok adt-cap fn-hp-wpad nth))
          ("Subgoal *1/2" :use ((:instance fn-hp-piw-word-is-iw-word (i o))
                                (:instance fn-hp-placement-natp-start (lens (fn-hp-lens h salt)))
                                (:instance fn-hp-natp-nth-starts-x))
           :expand ((fn-hp-agree2 (+ o (* 2048 (nth r starts))) (+ o (* 2048 (nth r (fn-hp-starts h salt)))) k
                                  (fn-hp-piw h salt starts np) (fn-hp-iw h salt))))))

; -----------------------------------------------------------------------------
; D. The reads over a placed image: the row read and the open's header.

(local
 (defthm fn-hp-cap-covers-words
   (implies (natp u) (<= (floor u 8) (* 2048 (adt-cap u))))
   :hints (("Goal" :use ((:instance adt-cap-covers))
            :in-theory (disable adt-cap-covers adt-cap)))
   :rule-classes :linear))

(defthm fn-hp-piw-cell
  (implies (and (fn-hp-okp h salt) (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5)
                (natp r) (< r 4) (natp i) (< i (len h)))
           (equal (nth (+ (* 2048 (nth r starts)) i) (fn-hp-piw h salt starts np))
                  (nth r (fn-hp-cells-of (nth i h) salt (fn-hp-pes-len (take i h))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-piw-word-is-iw-word)
                 (:instance fn-hp-iw-cell)
                 (:instance fn-hp-lens-col-sizes)
                 (:instance adt-cap-covers (u (len (nth r (fn-hp-regs h salt)))))
                 (:instance adt-nth-lens (regs (fn-hp-regs h salt))))
           :in-theory (e/d (fn-hp-lens) (fn-hp-piw-word-is-iw-word fn-hp-iw-cell fn-hp-lens-col-sizes adt-cap-covers
                                         adt-nth-lens fn-hp-piw fn-hp-iw fn-hp-starts fn-hp-regs fn-hp-okp
                                         fn-hp-cells-of adt-cap adt-placement-ok adt-lens)))))

(defthm fn-hp-piw-pool
  (implies (and (fn-hp-okp h salt) (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5)
                (natp i) (< i (len h)))
           (equal (take (floor (len (fn-hp-pe (nth i h))) 8)
                        (nthcdr (+ (* 2048 (nth 4 starts)) (floor (fn-hp-pes-len (take i h)) 8))
                                (fn-hp-piw h salt starts np)))
                  (take (floor (len (fn-hp-pe (nth i h))) 8)
                        (nthcdr (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take i h)) 8))
                                (fn-hp-iw h salt)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-piw-agree-iw (r 4) (o (floor (fn-hp-pes-len (take i h)) 8))
                            (k (floor (len (fn-hp-pe (nth i h))) 8)))
                 (:instance fn-hp-agree2-take (a (+ (* 2048 (nth 4 starts)) (floor (fn-hp-pes-len (take i h)) 8)))
                            (b (+ (* 2048 (nth 4 (fn-hp-starts h salt))) (floor (fn-hp-pes-len (take i h)) 8)))
                            (n (floor (len (fn-hp-pe (nth i h))) 8))
                            (x (fn-hp-piw h salt starts np)) (y (fn-hp-iw h salt)))
                 (:instance fn-hp-pes-len-take-bound)
                 (:instance fn-hp-lens-4)
                 (:instance adt-nth-lens (regs (fn-hp-regs h salt)) (r 4))
                 (:instance adt-cap-covers (u (len (nth 4 (fn-hp-regs h salt)))))
                 (:instance fn-hp-floor-8-exact (x (fn-hp-pes-len (take i h))))
                 (:instance fn-hp-floor-8-exact (x (len (fn-hp-pe (nth i h)))))
                 (:instance fn-hp-pes-len-mod-8 (h (take i h)))
                 (:instance fn-hp-pe-mod-8 (ev (nth i h)))
                 (:instance fn-hp-placement-natp-start (r 4) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-natp-nth-starts-x (r 4)))
           :in-theory (e/d (fn-hp-lens)
                           (fn-hp-piw-agree-iw fn-hp-agree2-take fn-hp-pes-len-take-bound fn-hp-lens-4 adt-nth-lens
                            adt-cap-covers fn-hp-floor-8-exact fn-hp-pes-len-mod-8 fn-hp-pe-mod-8
                            fn-hp-piw fn-hp-iw fn-hp-starts fn-hp-regs fn-hp-okp adt-cap adt-placement-ok adt-lens
                            fn-hp-pe fn-hp-pes-len floor mod take nthcdr)))))

(defthm fn-hp-x-cell-of-placed
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h)) (natp r) (< r 4)
                (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (equal (mv-nth 0 (fn-hp-x-cell r seq starts pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-cell r seq starts pgs-mem))
                  (nth r (fn-hp-cells-of (nth seq h) salt (fn-hp-pes-len (take seq h))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-cell-from-ready (iw (fn-hp-piw h salt starts np)))
                 (:instance fn-hp-nfix-nth-starts)
                 (:instance fn-hp-piw-cell (i seq)))
           :in-theory (disable fn-hp-x-cell-from-ready fn-hp-nfix-nth-starts fn-hp-piw-cell fn-hp-x-cell
                               fn-hp-piw fn-hp-okp fn-hp-vhold fn-hp-cells-of adt-placement-ok fn-hp-lens))))

(defthm fn-hp-x-cells-of-placed
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h))
                (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) lens starts pgs-mem)) :ok))
           (and (equal (mv-nth 1 (fn-hp-x-cell 0 seq starts pgs-mem)) (fn-hp-mkey (nth seq h) salt))
                (equal (mv-nth 1 (fn-hp-x-cell 1 seq starts pgs-mem)) (len (fn-scc-encode (nth seq h))))
                (equal (mv-nth 1 (fn-hp-x-cell 2 seq starts pgs-mem)) (fn-hp-pes-len (take seq h)))
                (equal (mv-nth 1 (fn-hp-x-cell 3 seq starts pgs-mem)) (len (fn-hp-pe (nth seq h))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-at-ok-cells (n (len h)))
                 (:instance fn-hp-x-cell-of-placed (r 0)) (:instance fn-hp-x-cell-of-placed (r 1))
                 (:instance fn-hp-x-cell-of-placed (r 2)) (:instance fn-hp-x-cell-of-placed (r 3))
                 (:instance fn-hp-cells-of-is (ev (nth seq h)) (pos (fn-hp-pes-len (take seq h)))))
           :in-theory (union-theories '(car-cons cdr-cons nth-0-cons nth-add1 natp zp (:e zp) (:e natp) (:e <) (:e nth)
                                         (:e len) nth len (:e car) (:e cdr) (:t len) fn-hp-pes-len-natp nfix (:e nfix))
                                      (theory 'minimal-theory)))))

; KEYSTONE (the row read over any placement): whenever the read the host
; calls answers (VERDICT :ok), its answer is the history's event at SEQ --
; over ANY page store state whose verified pages hold the PLACED image's
; words, the regions wherever the header's STARTS put them.
(defthm fn-hp-x-at-is-nth-placed
  (implies (and (fn-hp-okp h salt) (natp seq) (< seq (len h))
                (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (equal (mv-nth 0 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-at seq salt (len h) (fn-hp-lens h salt) starts pgs-mem))
                  (list :ok (nth seq h))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-cells-of-placed (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-x-at-ok-pool (n (len h)) (lens (fn-hp-lens h salt))
                            (off (fn-hp-pes-len (take seq h))) (plen (len (fn-hp-pe (nth seq h)))))
                 (:instance fn-hp-x-words-from-pool-ready (iw (fn-hp-piw h salt starts np))
                            (lo (+ (* 2048 (nth 4 starts)) (floor (fn-hp-pes-len (take seq h)) 8)))
                            (k (floor (len (fn-hp-pe (nth seq h))) 8)))
                 (:instance fn-hp-piw-pool (i seq))
                 (:instance fn-hp-nfix-nth-starts (r 4))
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
                 (:instance fn-hp-len-enc-le-pe (ev (nth seq h)))
                 (:instance fn-hp-starts-okp-true-listp (s starts)))
           :in-theory (union-theories '(fn-hp-pool-lo nfix natp posp fn-hp-pes-len-natp (:t len) (:e <) (:e natp)
                                        (:t floor) fn-hp-okp-events fn-hp-floor-8-natp fn-hp-floor-8-nonneg
                                        fn-hp-starts-okp)
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-hp-list5-p
   (implies (and (true-listp x) (equal (len x) 5))
            (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) x))
   :hints (("Goal" :in-theory (e/d (nth) (len true-listp))
            :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x)) (len (cddddr x)) (len (cdr (cddddr x)))
                     (true-listp x) (true-listp (cdr x)) (true-listp (cddr x)) (true-listp (cdddr x))
                     (true-listp (cddddr x)) (true-listp (cdr (cddddr x))))))))

(local
 (defthm fn-hp-meta-words-5
   (implies (and (true-listp starts) (equal (len starts) 5) (true-listp lens) (equal (len lens) 5))
            (equal (fn-hp-meta-words starts lens)
                   (list (nth 0 starts) (nth 0 lens) (nth 1 starts) (nth 1 lens) (nth 2 starts) (nth 2 lens)
                         (nth 3 starts) (nth 3 lens) (nth 4 starts) (nth 4 lens))))
   :hints (("Goal" :in-theory (enable nth)
            :expand ((fn-hp-meta-words starts lens) (fn-hp-meta-words (cdr starts) (cdr lens))
                     (fn-hp-meta-words (cddr starts) (cddr lens)) (fn-hp-meta-words (cdddr starts) (cdddr lens))
                     (fn-hp-meta-words (cddddr starts) (cddddr lens))
                     (fn-hp-meta-words (cdr (cddddr starts)) (cdr (cddddr lens))))))))

(defthm fn-hp-w-header-of-hdr2
  (implies (and (natp n) (nat-listp lens) (equal (len lens) 5) (true-listp starts) (equal (len starts) 5) (natp np)
                (adt-placement-ok starts lens np)
                (equal (nth 0 lens) (* 8 n)) (equal (nth 1 lens) (* 8 n))
                (equal (nth 2 lens) (* 8 n)) (equal (nth 3 lens) (* 8 n)))
           (equal (fn-hp-w-header (fn-hp-hdr2 n lens starts np) np) (list :ok n lens starts)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-list5-p (x lens)) (:instance fn-hp-list5-p (x starts)))
           :in-theory (e/d (fn-hp-hdr2 fn-hp-w-header) (fn-hp-list5-p adt-placement-ok (:e adt-zeros) adt-zeros)))))

(defthm fn-hp-piw-header-word
  (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5) (natp k) (< k 2048))
           (equal (nth k (fn-hp-piw h salt starts np))
                  (nth k (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-nth-wreps (w (adt-zeros (* 2048 (nfix np))))
                            (blocks (cons (cons 0 (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
                                          (fn-hp-rblocks (fn-hp-regs h salt) starts))))
                 (:instance fn-hp-rblocks-apart (regs (fn-hp-regs h salt)))
                 (:instance fn-hp-hdr-apart-rblocks (regs (fn-hp-regs h salt))
                            (hdr (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))))
           :in-theory (e/d (fn-hp-piw fn-hp-lens)
                           (fn-hp-nth-wreps fn-hp-rblocks-apart fn-hp-hdr-apart-rblocks fn-hp-wreps fn-hp-rblocks
                            fn-hp-hdr2 fn-hp-regs adt-placement-ok fn-hp-block-apart)))))

(local
 (defthm fn-hp-piw-header-agree
   (implies (and (adt-placement-ok starts (fn-hp-lens h salt) np) (equal (len starts) 5) (natp a) (<= (+ a n) 2048))
            (fn-hp-agree a n (fn-hp-piw h salt starts np) (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
   :hints (("Goal" :induct (fn-hp-agree a n (fn-hp-piw h salt starts np) (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np))
            :in-theory (disable fn-hp-piw fn-hp-hdr2 fn-hp-lens adt-placement-ok)))))

(local
 (defun fn-hp-tt-ind-p (n m w)
   (if (or (zp n) (zp m)) (list n m w) (fn-hp-tt-ind-p (1- n) (1- m) (cdr w)))))

(local
 (defthm fn-hp-take-take-p
   (implies (and (natp n) (natp m) (<= n m)) (equal (take n (take m w)) (take n w)))
   :hints (("Goal" :induct (fn-hp-tt-ind-p n m w) :in-theory (enable take)))))

(local
 (defthm fn-hp-take-19-of-take-2048-p
   (equal (take 19 (take 2048 w)) (take 19 w))
   :hints (("Goal" :use ((:instance fn-hp-take-take-p (n 19) (m 2048))) :in-theory (disable fn-hp-take-take-p)))))

(defthm fn-hp-placement-np-pos-p
  (implies (and (adt-placement-ok starts lens np) (consp starts) (consp lens))
           (and (natp np) (<= 1 np)))
  :hints (("Goal" :expand ((adt-placement-ok starts lens np)) :in-theory (disable adt-cap)))
  :rule-classes nil)

; KEYSTONE (the open's header over any placement): once page 0 is ready,
; the header check answers the history's N, lengths and the header's
; starts, over any state whose verified pages hold the placed image.
(defthm fn-hp-x-header-is-placed
  (implies (and (fn-hp-okp h salt) (fn-hp-starts-okp starts) (adt-placement-ok starts (fn-hp-lens h salt) np)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (equal (mv-nth 0 (fn-hp-x-header np pgs-mem)) :ok))
           (equal (mv-nth 1 (fn-hp-x-header np pgs-mem))
                  (list :ok (len h) (fn-hp-lens h salt) starts)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-vhold-page (p 0) (q 0) (np (pgs-v-length pgs-mem)) (iw (fn-hp-piw h salt starts np)))
                 (:instance fn-hp-x-ready-ok (p 0))
                 (:instance fn-hp-piw-header-agree (a 0) (n 19))
                 (:instance fn-hp-agree-is-take (a 0) (n 19) (x (fn-hp-piw h salt starts np))
                            (y (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)))
                 (:instance fn-hp-w-header-take-19 (w (nth *pgs-wi* pgs-mem)) (npages np))
                 (:instance fn-hp-w-header-take-19 (w (fn-hp-hdr2 (len h) (fn-hp-lens h salt) starts np)) (npages np))
                 (:instance fn-hp-take-19-of-take-2048-p (w (nth *pgs-wi* pgs-mem)))
                 (:instance fn-hp-take-19-of-take-2048-p (w (fn-hp-piw h salt starts np)))
                 (:instance fn-hp-w-header-of-hdr2 (n (len h)) (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-placement-np-pos-p (lens (fn-hp-lens h salt)))
                 (:instance fn-hp-lens-col-sizes (r 0)) (:instance fn-hp-lens-col-sizes (r 1))
                 (:instance fn-hp-lens-col-sizes (r 2)) (:instance fn-hp-lens-col-sizes (r 3)))
           :in-theory (e/d (fn-hp-x-header fn-hp-x-words-is-take)
                           (fn-hp-vhold-page fn-hp-x-ready-ok fn-hp-piw-header-agree fn-hp-agree-is-take
                            fn-hp-w-header-take-19 fn-hp-take-19-of-take-2048-p fn-hp-w-header-of-hdr2
                            fn-hp-lens-col-sizes fn-hp-vhold fn-hp-piw fn-hp-hdr2 fn-hp-okp fn-hp-lens
                            fn-hp-x-ready fn-hp-w-header adt-placement-ok take fn-hp-agree fn-hp-x-words)))))
