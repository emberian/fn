; Logical observation of the cursor. None of these materializers belongs
; on the served path; the formatter reads each span under its own quantum.
(in-package "ACL2")
(include-book "legacy-parser-cursor")
(include-book "catalog-record")

(defun fn-lpc-feed (bytes s)
  (declare (xargs :guard t))
  (if (consp bytes) (fn-lpc-feed (cdr bytes) (fn-lpc-byte s (car bytes))) s))

(defun fn-lpc-span-value (span arena)
  (declare (xargs :guard t :verify-guards nil))
  (if span
      (fn-nov-scrub
       (take (nfix (fn-lpc-at 2 span))
             (nthcdr (nfix (fn-lpc-at 1 span))
                     (nth (nfix (fn-lpc-at 0 span)) arena)))) nil))

(defun fn-lpc-nov-value (s arena)
  (declare (xargs :guard t :verify-guards nil))
  (fn-hnov-make
   (fn-lpc-tombstonep s) (eq (fn-lpc-verdict s) :valid)
   (fn-record-octets-string (fn-lpc-span-value (fn-lpc-field s 0) arena))
   (fn-record-octets-string (fn-lpc-span-value (fn-lpc-field s 1) arena))
   (fn-record-octets-string (fn-lpc-span-value (fn-lpc-field s 2) arena))
   (fn-record-octets-string (fn-lpc-span-value (fn-lpc-field s 3) arena))
   (fn-record-octets-string (fn-lpc-span-value (fn-lpc-field s 4) arena))))

; Full refinement obligation, deliberately a predicate rather than a
; theorem until the line/field simulation is admitted. Its reference is
; the actual catalog implementation, including invalid parses.
(defun fn-lpc-agreesp (bytes pin)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s (fn-lpc-feed bytes (fn-lpc-begin 0 (len bytes) pin))))
    (and (equal (fn-lpc-nov-value s (list bytes)) (fn-hnov-of bytes))
         (equal (fn-lpc-body-lines s) (fn-hf-body-lines-of bytes)))))

; Body-count residual used to connect the one-byte machine to the existing
; two-byte CRLF recursion. This is proof vocabulary, never served work.
(defun fn-lpc-body-residual (bytes s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((phase (fn-lpc-at 0 s)) (count (nfix (fn-lpc-at 1 s))))
    (cond ((eq phase :bad) nil)
          ((eq phase :cr)
           (if (and (consp bytes) (equal (car bytes) 10))
               (let ((n (fn-hf-crlf-count (cdr bytes) nil)))
                 (and n (+ 1 count n))) nil))
          (t (let ((n (fn-hf-crlf-count bytes (eq phase :inline))))
               (and n (+ count n)))))))

(defun fn-lpc-body-phasep (s)
  (declare (xargs :guard t))
  (member-eq (fn-lpc-at 0 s) '(:line :inline :cr :bad)))

(defthm fn-lpc-body-byte-preserves-phase
  (implies (fn-lpc-body-phasep s)
           (fn-lpc-body-phasep (fn-lpc-body-byte s byte)))
  :hints (("Goal" :in-theory (enable fn-lpc-body-byte fn-lpc-body-phasep fn-lpc-at))))

(defthm fn-lpc-body-byte-refines-crlf-count
  (implies (fn-lpc-body-phasep s)
           (equal (fn-lpc-body-residual (cons byte rest) s)
                  (fn-lpc-body-residual rest (fn-lpc-body-byte s byte))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-body-phasep fn-lpc-body-byte fn-lpc-body-residual
                 fn-lpc-at fn-hf-crlf-count)
                (fn-hf-crlf-count-onto)))))

(defun fn-lpc-body-fold (bytes s)
  (declare (xargs :guard t))
  (if (consp bytes) (fn-lpc-body-fold (cdr bytes) (fn-lpc-body-byte s (car bytes))) s))

(local (defthm fn-lpc-body-residual-atom
  (implies (not (consp bytes))
           (equal (fn-lpc-body-residual bytes s)
                  (if (member-eq (fn-lpc-at 0 s) '(:bad :cr :inline)) nil
                    (nfix (fn-lpc-at 1 s)))))
  :hints (("Goal" :in-theory (enable fn-lpc-body-residual fn-hf-crlf-count)))))

(defthm fn-lpc-body-fold-refines-crlf-count
  (implies (fn-lpc-body-phasep s)
           (equal (fn-lpc-body-residual nil (fn-lpc-body-fold bytes s))
                  (fn-lpc-body-residual bytes s)))
  :hints (("Goal" :induct (fn-lpc-body-fold bytes s)
           :in-theory (e/d (fn-lpc-body-fold)
                           (fn-lpc-body-byte fn-lpc-body-residual fn-lpc-body-phasep)))))

(defthm fn-lpc-body-fold-from-begin-is-crlf-count
  (equal (fn-lpc-body-residual nil (fn-lpc-body-fold bytes '(:line 0)))
         (fn-hf-crlf-count bytes nil))
  :hints (("Goal" :use ((:instance fn-lpc-body-fold-refines-crlf-count
                                   (s '(:line 0))))
           :in-theory (e/d (fn-lpc-body-residual fn-lpc-body-phasep fn-lpc-at)
                           (fn-lpc-body-fold fn-hf-crlf-count)))))

; Concrete arena tick -> list scan of the exact consumed source prefix.
; Unlike a theorem about a second parser, this bridges the actual arena
; accessor used in fn-lpc-tick to the transition used by the full reference.
(defun fn-lpc-list-tick (bytes fuel s)
  (declare (xargs :guard (natp fuel)))
  (if (or (zp fuel) (not (consp bytes))) s
    (fn-lpc-list-tick (cdr bytes) (1- fuel) (fn-lpc-byte s (car bytes)))))

(local (defthm fn-lpc-car-nthcdr
  (equal (car (nthcdr i xs)) (nth i xs))))
(local (defthm fn-lpc-cdr-nthcdr
  (implies (natp i)
           (equal (cdr (nthcdr i xs)) (nthcdr (+ 1 i) xs)))))
(local (defthm fn-lpc-nthcdr-nil (equal (nthcdr i nil) nil)))
(local (defthm fn-lpc-consp-nthcdr
  (implies (natp i)
           (iff (consp (nthcdr i xs)) (< i (len xs))))))

(defthm fn-lpc-tick-is-source-list-tick
  (implies (fn-lpc-ready-p s fn-arena)
           (equal (mv-nth 0 (fn-lpc-tick s fuel fn-arena))
                  (fn-lpc-list-tick
                   (nthcdr (fn-lpc-at 3 s) (nth (fn-lpc-at 0 s) fn-arena))
                   fuel s)))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick fn-lpc-list-tick fn-lpc-ready-p)
                           (fn-lpc-byte fn-lpc-at fn-lpc-verdict nthcdr nth)))))

(defun fn-lpc-search-count (bytes)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp bytes)
      (if (and (equal (car bytes) 13) (equal (cadr bytes) 10)
               (equal (caddr bytes) 13) (equal (cadddr bytes) 10))
          (nfix (fn-hf-crlf-count (cddddr bytes) nil))
        (fn-lpc-search-count (cdr bytes))) 0))

(defthm fn-lpc-search-count-is-index-count
  (implies (natp i)
           (equal (if (fn-hf-split-index bytes i)
                      (nfix (fn-hf-crlf-count
                             (nthcdr (- (fn-hf-split-index bytes i) i) bytes) nil)) 0)
                  (fn-lpc-search-count bytes)))
  :hints (("Goal" :induct (fn-hf-split-index bytes i)
           :in-theory (e/d (fn-hf-split-index fn-lpc-search-count nthcdr)
                           (fn-hf-crlf-count fn-lpc-cdr-nthcdr)))))

(defthm fn-lpc-search-count-is-body-lines-of
  (equal (fn-lpc-search-count bytes) (fn-hf-body-lines-of bytes))
  :hints (("Goal" :use ((:instance fn-lpc-search-count-is-index-count (i 0)))
           :in-theory (e/d (fn-hf-body-lines-of)
                           (fn-lpc-search-count fn-hf-split-index fn-hf-crlf-count)))))

(defun fn-lpc-matched-prefix (matched)
  (declare (xargs :guard t))
  (cond ((equal matched 1) '(13)) ((equal matched 2) '(13 10))
        ((equal matched 3) '(13 10 13)) (t nil)))

(defun fn-lpc-facts-residual (bytes s)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-lpc-at 5 s) 4)
      (nfix (fn-lpc-body-residual bytes (fn-lpc-at 6 s)))
    (fn-lpc-search-count (append (fn-lpc-matched-prefix (fn-lpc-at 5 s)) bytes))))

(defun fn-lpc-facts-statep (s)
  (declare (xargs :guard t))
  (and (member-equal (fn-lpc-at 5 s) '(0 1 2 3 4))
       (if (equal (fn-lpc-at 5 s) 4) (fn-lpc-body-phasep (fn-lpc-at 6 s))
         (equal (fn-lpc-at 6 s) '(:line 0)))))

(local (defthm fn-lpc-byte-facts-unfolds
  (and (equal (fn-lpc-at 5 (fn-lpc-byte s byte))
              (fn-lpc-split-byte (fn-lpc-at 5 s) byte))
       (equal (fn-lpc-at 6 (fn-lpc-byte s byte))
              (if (equal (fn-lpc-at 5 s) 4)
                  (fn-lpc-body-byte (fn-lpc-at 6 s) byte) (fn-lpc-at 6 s))))
  :hints (("Goal" :in-theory
    (union-theories '(fn-lpc-byte fn-lpc-at fn-ag-car fn-ag-cdr car-cons cdr-cons)
                    (union-theories (theory 'minimal-theory)
                                    (executable-counterpart-theory :here)))))))

(defthm fn-lpc-byte-preserves-facts-state
  (implies (fn-lpc-facts-statep s)
           (fn-lpc-facts-statep (fn-lpc-byte s byte)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-facts-statep fn-lpc-split-byte)
                (fn-lpc-byte fn-lpc-at fn-lpc-header-byte fn-lpc-body-byte fn-lpc-body-phasep)))))

(local (defthm fn-lpc-body-residual-start
  (equal (fn-lpc-body-residual bytes '(:line 0)) (fn-hf-crlf-count bytes nil))
  :hints (("Goal" :in-theory (enable fn-lpc-body-residual fn-lpc-at)))))

(defthm fn-lpc-byte-refines-body-facts
  (implies (fn-lpc-facts-statep s)
           (equal (fn-lpc-facts-residual (cons byte rest) s)
                  (fn-lpc-facts-residual rest (fn-lpc-byte s byte))))
  :hints (("Goal" :expand ((:free (a b) (fn-lpc-search-count (cons a b))))
           :in-theory
           (e/d (fn-lpc-facts-statep fn-lpc-facts-residual fn-lpc-matched-prefix
                 fn-lpc-split-byte)
                (fn-lpc-byte fn-lpc-at fn-lpc-search-count-is-body-lines-of
                 fn-lpc-header-byte fn-lpc-body-byte fn-lpc-body-phasep
                 fn-lpc-search-count fn-lpc-body-residual)))))

(defthm fn-lpc-feed-preserves-facts-state
  (implies (fn-lpc-facts-statep s)
           (fn-lpc-facts-statep (fn-lpc-feed bytes s)))
  :hints (("Goal" :induct (fn-lpc-feed bytes s)
           :in-theory (e/d (fn-lpc-feed) (fn-lpc-byte fn-lpc-facts-statep)))))

(defthm fn-lpc-feed-refines-body-facts
  (implies (and (true-listp bytes) (fn-lpc-facts-statep s))
           (equal (fn-lpc-facts-residual nil (fn-lpc-feed bytes s))
                  (fn-lpc-facts-residual bytes s)))
  :hints (("Goal" :induct (fn-lpc-feed bytes s)
           :in-theory (e/d (fn-lpc-feed)
                           (fn-lpc-byte fn-lpc-facts-statep fn-lpc-facts-residual)))))

(local (defthm fn-lpc-facts-residual-finish
  (implies (fn-lpc-facts-statep s)
           (equal (fn-lpc-facts-residual nil s) (fn-lpc-body-lines s)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-facts-statep fn-lpc-facts-residual fn-lpc-matched-prefix
                 fn-lpc-body-lines fn-lpc-body-phasep fn-lpc-search-count
                 fn-lpc-body-residual fn-lpc-at fn-hf-crlf-count)
                (fn-lpc-search-count-is-body-lines-of))))))

(defthm fn-lpc-feed-body-lines-is-body-lines-of
  (implies (true-listp bytes)
           (equal (fn-lpc-body-lines
                   (fn-lpc-feed bytes (fn-lpc-begin h n pin)))
                  (fn-hf-body-lines-of bytes)))
  :hints (("Goal" :use ((:instance fn-lpc-feed-refines-body-facts
                                   (s (fn-lpc-begin h n pin))))
           :in-theory (e/d (fn-lpc-begin fn-lpc-facts-statep fn-lpc-facts-residual
                             fn-lpc-at fn-lpc-matched-prefix)
                           (fn-lpc-feed fn-lpc-header-begin fn-lpc-header-bad
                            fn-lpc-body-lines fn-lpc-search-count)))))

(local (defthm fn-lpc-list-tick-full
  (implies (<= (len bytes) (nfix fuel))
           (equal (fn-lpc-list-tick bytes fuel s) (fn-lpc-feed bytes s)))
  :hints (("Goal" :induct (fn-lpc-list-tick bytes fuel s)
           :in-theory (e/d (fn-lpc-list-tick fn-lpc-feed)
                           (fn-lpc-byte))))))

(local (defthm fn-lpc-begin-source-unfolds
  (and (equal (fn-lpc-at 0 (fn-lpc-begin h n pin)) h)
       (equal (fn-lpc-at 1 (fn-lpc-begin h n pin)) n)
       (equal (fn-lpc-at 3 (fn-lpc-begin h n pin)) 0))
  :hints (("Goal" :in-theory
    (union-theories '(fn-lpc-begin fn-lpc-at fn-ag-car fn-ag-cdr car-cons cdr-cons)
                    (union-theories (theory 'minimal-theory)
                                    (executable-counterpart-theory :here)))))))

(defthm fn-lpc-tick-full-body-lines-is-body-lines-of
  (implies (and (fn-arena-p fn-arena) (natp h)
                (< h (fn-arena-count fn-arena)))
           (equal
            (fn-lpc-body-lines
             (mv-nth 0
              (fn-lpc-tick (fn-lpc-begin h (fn-arena-payload-len h fn-arena) pin)
                           (fn-arena-payload-len h fn-arena) fn-arena)))
            (fn-hf-body-lines-of (nth h fn-arena))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-ready-p fn-arn-payload-listp-nth
                 fn-cbor-octet-listp-implies-true-listp)
                (fn-lpc-begin fn-lpc-at fn-lpc-tick fn-lpc-feed fn-lpc-list-tick fn-lpc-body-lines
                 fn-lpc-header-begin fn-lpc-header-bad fn-hf-body-lines-of)))))

; The logical source theorem needs only the cursor's numeric bounds, not
; an arena-wide recognizer or a valid-handle premise. The stronger runtime
; guard remains the admission check for the concrete accessor.
(defthm fn-lpc-tick-is-source-list-tick-under-bounds
  (implies (and (natp (fn-lpc-at 3 s))
                (equal (fn-lpc-at 1 s) (len (nth (fn-lpc-at 0 s) fn-arena)))
                (<= (fn-lpc-at 3 s) (fn-lpc-at 1 s)))
           (equal (mv-nth 0 (fn-lpc-tick s fuel fn-arena))
                  (fn-lpc-list-tick
                   (nthcdr (fn-lpc-at 3 s) (nth (fn-lpc-at 0 s) fn-arena))
                   fuel s)))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick fn-lpc-list-tick)
                           (fn-lpc-byte fn-lpc-at fn-lpc-verdict nthcdr nth)))))

(local (defthm fn-lpc-facts-residual-atom
  (implies (and (not (consp bytes)) (fn-lpc-facts-statep s))
           (equal (fn-lpc-facts-residual bytes s) (fn-lpc-body-lines s)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-facts-statep fn-lpc-facts-residual fn-lpc-matched-prefix
                 fn-lpc-body-lines fn-lpc-body-phasep fn-lpc-search-count
                 fn-lpc-body-residual fn-lpc-at fn-hf-crlf-count)
                (fn-lpc-search-count-is-body-lines-of))))))

(defthm fn-lpc-feed-refines-body-facts-all-tails
  (implies (fn-lpc-facts-statep s)
           (equal (fn-lpc-facts-residual nil (fn-lpc-feed bytes s))
                  (fn-lpc-facts-residual bytes s)))
  :hints (("Goal" :induct (fn-lpc-feed bytes s)
           :in-theory (e/d (fn-lpc-feed)
                           (fn-lpc-byte fn-lpc-facts-statep fn-lpc-facts-residual)))))

(defthm fn-lpc-feed-body-lines-is-body-lines-of-all-tails
  (equal (fn-lpc-body-lines (fn-lpc-feed bytes (fn-lpc-begin h n pin)))
         (fn-hf-body-lines-of bytes))
  :hints (("Goal" :use ((:instance fn-lpc-feed-refines-body-facts-all-tails
                                   (s (fn-lpc-begin h n pin))))
           :in-theory (e/d (fn-lpc-begin fn-lpc-facts-statep fn-lpc-facts-residual
                             fn-lpc-at fn-lpc-matched-prefix)
                           (fn-lpc-feed-refines-body-facts-all-tails
                            fn-lpc-feed fn-lpc-header-begin fn-lpc-header-bad
                            fn-lpc-body-lines fn-lpc-search-count)))))

(defthm fn-lpc-tick-full-body-lines
  (equal
   (fn-lpc-body-lines
    (mv-nth 0
     (fn-lpc-tick (fn-lpc-begin h (fn-arena-payload-len h fn-arena) pin)
                  (fn-arena-payload-len h fn-arena) fn-arena)))
   (fn-hf-body-lines-of (nth h fn-arena)))
  :hints (("Goal" :in-theory
           (disable fn-lpc-begin fn-lpc-at fn-lpc-tick fn-lpc-feed fn-lpc-list-tick
                    fn-lpc-body-lines fn-lpc-header-begin fn-lpc-header-bad
                    fn-hf-body-lines-of))))
