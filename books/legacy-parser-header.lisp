; Proof decomposition for the full header projection simulation.
(in-package "ACL2")
(include-book "legacy-parser-cursor")

(defun fn-lpc-name-scan (candidate bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (fn-lpc-name-scan (fn-lpc-name-byte candidate (car bytes)) (cdr bytes))
    candidate))

(defthm fn-lpc-name-scan-matches-lower-name
  (equal (equal (fn-lpc-name-scan candidate bytes) nil)
         (equal (fn-article-ascii-downcase bytes) candidate))
  :hints (("Goal" :induct (fn-lpc-name-scan candidate bytes)
           :in-theory (enable fn-lpc-name-scan fn-lpc-name-byte
                               fn-article-ascii-downcase))))

(defun fn-lpc-names-scan (candidates bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (fn-lpc-names-scan (fn-lpc-name-step candidates (car bytes)) (cdr bytes))
    candidates))

(defthm fn-lpc-name-step-column
  (implies (and (natp k) (< k 5))
           (equal (fn-lpc-at k (fn-lpc-name-step candidates byte))
                  (fn-lpc-name-byte (fn-lpc-at k candidates) byte)))
  :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3) (equal k 4))
           :in-theory (e/d (fn-lpc-name-step fn-lpc-at)
                           (fn-lpc-name-byte)))))

(defthm fn-lpc-names-scan-column
  (implies (and (natp k) (< k 5))
           (equal (fn-lpc-at k (fn-lpc-names-scan candidates bytes))
                  (fn-lpc-name-scan (fn-lpc-at k candidates) bytes)))
  :hints (("Goal" :induct (fn-lpc-names-scan candidates bytes)
           :in-theory (e/d (fn-lpc-names-scan fn-lpc-name-scan)
                           (fn-lpc-at fn-lpc-name-byte fn-lpc-name-step)))))

(defthm fn-lpc-selected-name-exact
  (implies (and (natp k) (< k 5))
           (equal (equal (fn-lpc-at k (fn-lpc-names-scan *fn-lpc-names* bytes)) nil)
                  (equal (fn-article-ascii-downcase bytes)
                         (fn-lpc-at k *fn-lpc-names*))))
  :hints (("Goal"
           :use ((:instance fn-lpc-name-scan-matches-lower-name
                            (candidate (fn-lpc-at k *fn-lpc-names*))))
           :in-theory (disable fn-lpc-at fn-lpc-names-scan fn-lpc-name-scan
                               fn-lpc-name-scan-matches-lower-name
                               fn-article-ascii-downcase))))

(defthm fn-lpc-at-put
  (implies (and (natp i) (natp j))
           (equal (fn-lpc-at i (fn-lpc-put j v s))
                  (if (equal i j) v (fn-lpc-at i s))))
  :hints (("Goal" :in-theory (enable fn-lpc-at fn-lpc-put))))

; Logical representation invariant only. The executable tick does not run
; this recognizer; it carries the source identity and fixed scalar bounds.
(defun fn-lpc-span-bound-p (span h pin bound)
  (declare (xargs :guard t))
  (or (not span)
      (and (true-listp span) (equal (len span) 4)
           (equal (fn-lpc-at 0 span) h) (equal (fn-lpc-at 3 span) pin)
           (natp (fn-lpc-at 1 span)) (natp (fn-lpc-at 2 span))
           (<= (+ (fn-lpc-at 1 span) (fn-lpc-at 2 span)) (nfix bound)))))

(defun fn-lpc-spans-bound-p (spans h pin bound)
  (declare (xargs :guard t))
  (if (consp spans)
      (and (fn-lpc-span-bound-p (car spans) h pin bound)
           (fn-lpc-spans-bound-p (cdr spans) h pin bound))
    (null spans)))

(defthm fn-lpc-span-bound-monotone
  (implies (and (natp a) (natp b) (<= a b)
                (fn-lpc-span-bound-p span h pin a))
           (fn-lpc-span-bound-p span h pin b))
  :hints (("Goal" :in-theory (enable fn-lpc-span-bound-p))))

(defthm fn-lpc-spans-bound-monotone
  (implies (and (natp a) (natp b) (<= a b)
                (fn-lpc-spans-bound-p spans h pin a))
           (fn-lpc-spans-bound-p spans h pin b))
  :hints (("Goal" :induct (fn-lpc-spans-bound-p spans h pin a)
           :in-theory (e/d (fn-lpc-spans-bound-p) (fn-lpc-span-bound-p)))))

(defthm fn-lpc-span-bounded
  (implies (and (natp start) (natp end) (natp bound)
                (<= start bound) (<= end bound))
           (fn-lpc-span-bound-p (fn-lpc-span h start end pin) h pin bound))
  :hints (("Goal" :in-theory (enable fn-lpc-span fn-lpc-span-bound-p fn-lpc-at))))

(defthm fn-lpc-put-preserves-span-bounds
  (implies (and (natp k) (fn-lpc-spans-bound-p spans h pin bound)
                (fn-lpc-span-bound-p span h pin bound))
           (fn-lpc-spans-bound-p (fn-lpc-put k span spans) h pin bound))
  :hints (("Goal" :induct (fn-lpc-put k span spans)
           :in-theory (enable fn-lpc-put fn-lpc-spans-bound-p fn-lpc-span-bound-p))))

(defun fn-lpc-header-bounds-p (s h pin pos)
  (declare (xargs :guard t))
  (and (natp pos) (natp (fn-lpc-at 4 s)) (natp (fn-lpc-at 5 s))
       (<= (fn-lpc-at 4 s) pos) (<= (fn-lpc-at 5 s) pos)
       (fn-lpc-spans-bound-p (fn-lpc-at 8 s) h pin pos)))

(defthm fn-lpc-close-fields-preserves-bounds
  (implies (fn-lpc-header-bounds-p s h pin pos)
           (fn-lpc-spans-bound-p (fn-lpc-close-fields s h pin) h pin pos))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-close-fields fn-lpc-header-bounds-p)
                (fn-lpc-at fn-lpc-span fn-lpc-spans-bound-p fn-lpc-span-bound-p)))))

(defthm fn-lpc-header-byte-names-preserves-bounds
  (implies (fn-lpc-header-bounds-p s h pin pos)
           (fn-lpc-header-bounds-p
            (fn-lpc-header-byte-names s byte pos h pin names) h pin (+ 1 pos)))
  :hints (("Goal"
           :use ((:instance fn-lpc-spans-bound-monotone
                            (spans (fn-lpc-at 8 s)) (a pos) (b (+ 1 pos)))
                 (:instance fn-lpc-spans-bound-monotone
                            (spans (fn-lpc-close-fields s h pin))
                            (a pos) (b (+ 1 pos))))
           :in-theory
           (e/d (fn-lpc-header-bounds-p fn-lpc-header-byte-names fn-lpc-value-byte
                 fn-lpc-header-bad fn-lpc-at)
                (fn-lpc-put fn-lpc-close-fields fn-lpc-spans-bound-p
                 fn-lpc-span-bound-p fn-lpc-name-step fn-lpc-name-key)))))

(defthm fn-lpc-header-byte-preserves-bounds
  (implies (fn-lpc-header-bounds-p s h pin pos)
           (fn-lpc-header-bounds-p
            (fn-lpc-header-byte s byte pos h pin) h pin (+ 1 pos)))
  :hints (("Goal"
           :use ((:instance fn-lpc-spans-bound-monotone
                            (spans (fn-lpc-at 8 s)) (a pos) (b (+ 1 pos)))
                 (:instance fn-lpc-spans-bound-monotone
                            (spans (fn-lpc-close-fields s h pin))
                            (a pos) (b (+ 1 pos))))
           :in-theory
           (e/d (fn-lpc-header-bounds-p fn-lpc-header-byte fn-lpc-value-byte
                 fn-lpc-header-bad fn-lpc-at)
                (fn-lpc-put fn-lpc-close-fields fn-lpc-spans-bound-p
                 fn-lpc-span-bound-p fn-lpc-name-step fn-lpc-name-key)))))

(defun fn-lpc-cursor-bounds-p (s)
  (declare (xargs :guard t))
  (fn-lpc-header-bounds-p (fn-lpc-at 4 s) (fn-lpc-at 0 s)
                         (fn-lpc-at 2 s) (fn-lpc-at 3 s)))

(defthm fn-lpc-begin-establishes-bounds
  (fn-lpc-cursor-bounds-p (fn-lpc-begin h n pin))
  :hints (("Goal" :in-theory
           (enable fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p fn-lpc-begin
                   fn-lpc-header-begin fn-lpc-header-bad fn-lpc-at
                   fn-lpc-spans-bound-p fn-lpc-span-bound-p))))

(defthm fn-lpc-header-bounds-natural-position
  (implies (fn-lpc-header-bounds-p s h pin pos) (natp pos))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-lpc-header-bounds-p))))

(defthm fn-lpc-byte-names-preserves-bounds
  (implies (fn-lpc-cursor-bounds-p s)
           (fn-lpc-cursor-bounds-p (fn-lpc-byte-names s byte names)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-cursor-bounds-p fn-lpc-byte-names fn-lpc-at)
                (fn-lpc-header-byte-names fn-lpc-header-bounds-p fn-lpc-body-byte
                 fn-lpc-split-byte)))))

(defthm fn-lpc-byte-preserves-bounds
  (implies (fn-lpc-cursor-bounds-p s)
           (fn-lpc-cursor-bounds-p (fn-lpc-byte s byte)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-byte) (fn-lpc-byte-names fn-lpc-cursor-bounds-p)))))

(defthm fn-lpc-tick-preserves-bounds
  (implies (fn-lpc-cursor-bounds-p s)
           (fn-lpc-cursor-bounds-p (mv-nth 0 (fn-lpc-tick s fuel fn-arena))))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick)
                           (fn-lpc-byte fn-lpc-cursor-bounds-p fn-lpc-at fn-lpc-verdict)))))

(defthm fn-lpc-spans-bound-at
  (implies (and (natp k) (fn-lpc-spans-bound-p spans h pin pos))
           (fn-lpc-span-bound-p (fn-lpc-at k spans) h pin pos))
  :hints (("Goal" :induct (fn-lpc-at k spans)
           :in-theory (enable fn-lpc-at fn-lpc-spans-bound-p fn-lpc-span-bound-p))))

(local (defthm fn-lpc-empty-span-bounded
  (fn-lpc-span-bound-p nil h pin pos)
  :hints (("Goal" :in-theory (enable fn-lpc-span-bound-p)))))

(defthm fn-lpc-field-retains-pinned-source
  (implies (and (natp k) (fn-lpc-cursor-bounds-p s))
           (fn-lpc-span-bound-p (fn-lpc-field s k) (fn-lpc-at 0 s)
                                (fn-lpc-at 2 s) (fn-lpc-at 3 s)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-field fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p)
                (fn-lpc-at fn-lpc-verdict fn-lpc-span-bound-p fn-lpc-spans-bound-p)))))

(defthm fn-lpc-field-read-is-ready
  (implies (and (fn-lpc-ready-p s fn-arena) (fn-lpc-cursor-bounds-p s)
                (natp k) (natp offset) (fn-lpc-field s k)
                (< offset (fn-lpc-at 2 (fn-lpc-field s k))))
           (fn-lpc-span-ready-p (fn-lpc-field s k) offset fn-arena))
  :hints (("Goal" :use fn-lpc-field-retains-pinned-source
           :in-theory
           (e/d (fn-lpc-ready-p fn-lpc-span-ready-p fn-lpc-span-bound-p)
                (fn-lpc-field fn-lpc-at fn-lpc-cursor-bounds-p
                 fn-lpc-field-retains-pinned-source)))))
