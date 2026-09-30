; Actual arena tick and catalog record composition of the legacy byte cursor.
(in-package "ACL2")
(include-book "legacy-parser-columns")
(include-book "article-properties")

(defthm fn-lpv-feed-keeps-source-and-position
  (let ((out (fn-lpc-feed bytes s)))
    (and (equal (fn-lpc-at 0 out) (fn-lpc-at 0 s))
         (equal (fn-lpc-at 1 out) (fn-lpc-at 1 s))
         (equal (fn-lpc-at 2 out) (fn-lpc-at 2 s))
         (implies (natp (fn-lpc-at 3 s))
                  (equal (fn-lpc-at 3 out) (+ (fn-lpc-at 3 s) (len bytes))))))
  :hints (("Goal" :induct (fn-lpc-feed bytes s)
           :in-theory (e/d (fn-lpc-feed) (fn-lpc-byte fn-lpc-at)))))

(defthm fn-lpv-feed-header-is-actual-header-run
  (implies (natp (fn-lpc-at 3 s))
           (equal (fn-lpc-at 4 (fn-lpc-feed bytes s))
                  (fn-nlv-run bytes (fn-lpc-at 4 s) (fn-lpc-at 3 s)
                              (fn-lpc-at 0 s) (fn-lpc-at 2 s))))
  :hints (("Goal" :induct (fn-lpc-feed bytes s)
           :in-theory (e/d (fn-lpc-feed fn-nlv-run fn-lpc-byte fn-lpc-at)
                           (fn-lpc-header-byte fn-lpc-body-byte fn-lpc-split-byte)))))

(defthm fn-lpv-full-list-tick-is-feed
  (implies (<= (len bytes) (nfix fuel))
           (equal (fn-lpc-list-tick bytes fuel s) (fn-lpc-feed bytes s)))
  :hints (("Goal" :induct (fn-lpc-list-tick bytes fuel s)
           :in-theory (e/d (fn-lpc-list-tick fn-lpc-feed) (fn-lpc-byte)))))

(defthm fn-lpv-full-arena-tick-is-feed
  (equal (mv-nth 0 (fn-lpc-tick (fn-lpc-begin h (fn-arena-payload-len h fn-arena) pin)
                                (fn-arena-payload-len h fn-arena) fn-arena))
         (fn-lpc-feed (nth h fn-arena) (fn-lpc-begin h (len (nth h fn-arena)) pin)))
  :hints (("Goal"
           :use ((:instance fn-lpc-tick-is-source-list-tick-under-bounds
                    (s (fn-lpc-begin h (fn-arena-payload-len h fn-arena) pin))
                    (fuel (fn-arena-payload-len h fn-arena))))
           :in-theory
           (e/d (fn-lpc-begin fn-lpc-at fn-arena-payload-len)
                (fn-lpc-feed fn-lpc-list-tick fn-lpc-tick fn-lpc-header-begin fn-lpc-header-bad
                 fn-lpc-tick-is-source-list-tick-under-bounds)))))

(defthm fn-lpv-feed-preserves-bounds
  (implies (fn-lpc-cursor-bounds-p s)
           (fn-lpc-cursor-bounds-p (fn-lpc-feed bytes s)))
  :hints (("Goal" :induct (fn-lpc-feed bytes s)
           :in-theory (e/d (fn-lpc-feed) (fn-lpc-byte fn-lpc-cursor-bounds-p)))))

(local (defthm fn-lpv-preflight-from-length
  (implies (<= (len bytes) (nfix bound)) (fn-cbor-at-mostp bytes bound))
  :hints (("Goal" :induct (fn-cbor-at-mostp bytes bound)
           :in-theory (enable fn-cbor-at-mostp)))))

(defthm fn-lpv-complete-feed-verdict-is-actual-parser
  (implies (fn-cbor-octet-listp bytes)
           (equal (eq (fn-lpc-verdict (fn-lpc-feed bytes (fn-lpc-begin h (len bytes) pin))) :valid)
                  (fn-article-result-okp (fn-article-parse bytes))))
  :hints (("Goal" :cases ((fn-cbor-at-mostp bytes *fn-article-max-octets*))
           :use ((:instance fn-lpv-feed-header-is-actual-header-run
                    (s (fn-lpc-begin h (len bytes) pin)))
                 (:instance fn-lpv-feed-keeps-source-and-position
                    (s (fn-lpc-begin h (len bytes) pin)))
                 (:instance fn-nlpc-actual-byte-machine-accepts-iff-article-parser
                    (octets bytes) (pos 0)))
           :in-theory
           (e/d (fn-lpc-verdict fn-lpc-begin fn-lpc-at fn-lpc-header-bad fn-lpc-header-begin
                 fn-article-parse fn-article-parse-under fn-article-result-okp fn-article-error)
                (fn-lpc-feed fn-nlv-run fn-lpc-header-byte fn-article-parse-lines
                 fn-nlv-run-phase-is-control-run-phase fn-cbor-at-mostp
                 fn-lpv-feed-header-is-actual-header-run fn-lpv-feed-keeps-source-and-position
                 fn-nlpc-actual-byte-machine-accepts-iff-article-parser)))))

(local (defthm fn-lpv-byte-tombstone-flag
  (iff (fn-lpc-at 7 (fn-lpc-byte s byte))
       (and (fn-lpc-at 7 s)
            (or (<= 8 (nfix (fn-lpc-at 3 s)))
                (equal byte (fn-lpc-at (nfix (fn-lpc-at 3 s)) *fn-rcl-magic*)))))
  :hints (("Goal" :in-theory (union-theories
    '(fn-lpc-byte fn-lpc-at fn-ag-car fn-ag-cdr car-cons cdr-cons iff)
    (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))))))

(local (defthm fn-lpv-magic-tail-empty
  (implies (and (natp pos) (<= 8 pos))
           (equal (nthcdr pos *fn-rcl-magic*) nil))
  :hints (("Goal" :in-theory (enable nthcdr)))))

(local (defthm fn-lpv-prefix-nil
  (equal (fn-rcl-prefixp nil bytes) t)
  :hints (("Goal" :in-theory (enable fn-rcl-prefixp)))))

(local (defthm fn-lpv-magic-prefix-step-complete
  (implies (and (natp pos) (consp bytes))
           (equal (fn-rcl-prefixp (nthcdr pos *fn-rcl-magic*) bytes)
                  (or (<= 8 pos)
                      (and (equal (car bytes) (fn-lpc-at pos *fn-rcl-magic*))
                           (fn-rcl-prefixp (nthcdr (+ 1 pos) *fn-rcl-magic*) (cdr bytes))))))
  :hints (("Goal" :cases ((equal pos 0) (equal pos 1) (equal pos 2) (equal pos 3)
                         (equal pos 4) (equal pos 5) (equal pos 6) (equal pos 7))
           :in-theory (enable nthcdr fn-rcl-prefixp fn-lpc-at)))))

(local (defthm fn-lpv-prefix-atom
  (implies (not (consp bytes))
           (equal (fn-rcl-prefixp prefix bytes) (not (consp prefix))))
  :hints (("Goal" :in-theory (enable fn-rcl-prefixp)))))

(defthm fn-lpv-feed-tombstone-prefix
  (implies (and (natp (fn-lpc-at 3 s))
                (<= 8 (+ (fn-lpc-at 3 s) (len bytes))))
           (iff (fn-lpc-at 7 (fn-lpc-feed bytes s))
                (and (fn-lpc-at 7 s)
                     (fn-rcl-prefixp (nthcdr (fn-lpc-at 3 s) *fn-rcl-magic*) bytes))))
  :hints (("Goal" :induct (fn-lpc-feed bytes s)
           :in-theory (e/d (fn-lpc-feed nfix)
                           (fn-lpc-byte fn-lpc-at fn-rcl-prefixp nthcdr)))))

(local (defthm fn-lpv-at-leastp-is-length
  (equal (fn-rcl-at-leastp n bytes) (<= (nfix n) (len bytes)))
  :hints (("Goal" :induct (fn-rcl-at-leastp n bytes)
           :in-theory (enable fn-rcl-at-leastp)))))

(defthm fn-lpv-complete-feed-tombstone-is-actual
  (equal (fn-lpc-tombstonep (fn-lpc-feed bytes (fn-lpc-begin h (len bytes) pin)))
         (fn-rcl-tombstonep bytes))
  :hints (("Goal"
           :use ((:instance fn-lpv-feed-tombstone-prefix
                    (s (fn-lpc-begin h (len bytes) pin)))
                 (:instance fn-lpv-feed-keeps-source-and-position
                    (s (fn-lpc-begin h (len bytes) pin))))
           :in-theory
           (e/d (fn-lpc-tombstonep fn-rcl-tombstonep fn-lpc-begin fn-lpc-at)
                (fn-lpc-feed fn-lpc-header-begin fn-lpc-header-bad fn-rcl-at-leastp
                 fn-lpv-feed-tombstone-prefix fn-lpv-feed-keeps-source-and-position)))))

(defthm fn-lpv-complete-feed-has-bounded-spans
  (let ((out (fn-lpc-feed bytes (fn-lpc-begin h (len bytes) pin))))
    (fn-lpc-spans-bound-p (fn-lpc-at 8 (fn-lpc-at 4 out)) h pin (len bytes)))
  :hints (("Goal"
           :use ((:instance fn-lpv-feed-preserves-bounds
                    (s (fn-lpc-begin h (len bytes) pin)))
                 (:instance fn-lpv-feed-keeps-source-and-position
                    (s (fn-lpc-begin h (len bytes) pin))))
           :in-theory
           (e/d (fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p fn-lpc-begin fn-lpc-at)
                (fn-lpc-feed fn-lpc-header-begin fn-lpc-header-bad fn-lpc-spans-bound-p
                 fn-lpv-feed-preserves-bounds fn-lpv-feed-keeps-source-and-position)))))

(local (defthm fn-lpv-nil-span-value-by-definition
  (equal (fn-lpc-span-value nil arena) nil)
  :hints (("Goal" :in-theory (enable fn-lpc-span-value)))))
(local (defthm fn-lpv-nil-span-column
  (equal (fn-lpv-span-column nil source) nil)
  :hints (("Goal" :in-theory (enable fn-lpv-span-column)))))

(local (defthm fn-lpv-nth-nfix
  (equal (nth (nfix h) arena) (nth h arena))
  :hints (("Goal" :cases ((natp h)) :in-theory (enable nth nfix)))))

(local (defthm fn-lpv-catalog-cancel-start
  (implies (and (acl2-numberp a) (acl2-numberp b)) (equal (+ a (- a) b) b))
  :hints (("Goal" :in-theory (enable associativity-of-+ inverse-of-+)))))

(defthm fn-lpv-catalog-span-column-is-arena-abstraction
  (implies (fn-lpc-span-bound-p span h pin bound)
           (equal (fn-lpv-span-column span (nth h arena))
                  (and span (list (fn-lpc-span-value span arena)))))
  :hints (("Goal" :use ((:instance fn-lpv-nth-nfix (h (fn-lpc-at 0 span))))
           :in-theory
           (e/d (fn-lpv-span-column fn-lpc-span-bound-p fn-lpc-span-value fn-lpv-slice)
                (fn-lpc-at fn-nov-scrub nth nthcdr take fn-lpv-nth-nfix)))))

(defthm fn-lpv-span-values-are-arena-values
  (implies (fn-lpc-spans-bound-p spans h pin bound)
           (equal (fn-lpv-span-values spans (nth h arena))
                  (list (fn-lpc-span-value (fn-lpc-at 0 spans) arena)
                        (fn-lpc-span-value (fn-lpc-at 1 spans) arena)
                        (fn-lpc-span-value (fn-lpc-at 2 spans) arena)
                        (fn-lpc-span-value (fn-lpc-at 3 spans) arena)
                        (fn-lpc-span-value (fn-lpc-at 4 spans) arena))))
  :hints (("Goal"
           :use ((:instance fn-lpc-spans-bound-at (k 0) (pos bound))
                 (:instance fn-lpc-spans-bound-at (k 1) (pos bound))
                 (:instance fn-lpc-spans-bound-at (k 2) (pos bound))
                 (:instance fn-lpc-spans-bound-at (k 3) (pos bound))
                 (:instance fn-lpc-spans-bound-at (k 4) (pos bound))
                 (:instance fn-lpv-catalog-span-column-is-arena-abstraction (span (fn-lpc-at 0 spans)))
                 (:instance fn-lpv-catalog-span-column-is-arena-abstraction (span (fn-lpc-at 1 spans)))
                 (:instance fn-lpv-catalog-span-column-is-arena-abstraction (span (fn-lpc-at 2 spans)))
                 (:instance fn-lpv-catalog-span-column-is-arena-abstraction (span (fn-lpc-at 3 spans)))
                 (:instance fn-lpv-catalog-span-column-is-arena-abstraction (span (fn-lpc-at 4 spans))))
           :in-theory
           (e/d (fn-lpv-span-values)
                (fn-lpv-span-column fn-lpc-span-value fn-lpc-at fn-lpc-spans-bound-p nth
                 fn-lpc-span-bound-p fn-lpc-spans-bound-at fn-lpv-catalog-span-column-is-arena-abstraction)))))

(defthm fn-lpv-complete-feed-values-are-actual-content
  (implies (fn-article-result-okp (fn-article-parse bytes))
           (let ((out (fn-lpc-feed bytes (fn-lpc-begin h (len bytes) pin)))
                 (view (fn-article-result-article (fn-article-parse bytes))))
             (equal (fn-lpv-span-values (fn-lpc-at 8 (fn-lpc-at 4 out)) bytes)
                    (list (fn-nov-header-content view *fn-nov-subject-name*)
                          (fn-nov-header-content view *fn-nov-from-name*)
                          (fn-nov-header-content view *fn-nov-date-name*)
                          (fn-nov-header-content view *fn-nov-message-id-name*)
                          (fn-nov-header-content view *fn-nov-references-name*)))))
  :hints (("Goal"
           :use ((:instance fn-lpv-feed-header-is-actual-header-run
                    (s (fn-lpc-begin h (len bytes) pin)))
                 fn-lpv-complete-values-are-actual-overview-content)
           :in-theory
           (e/d (fn-lpc-begin fn-lpc-at)
                (fn-lpc-feed fn-nlv-run fn-lpc-header-begin fn-lpc-header-bad fn-lpv-span-values
                 fn-article-parse fn-article-result-okp fn-article-result-article fn-nov-header-content
                 fn-nlv-run-phase-is-control-run-phase fn-lpv-feed-header-is-actual-header-run
                 fn-lpv-complete-values-are-actual-overview-content)))))

(local (defthm fn-lpv-actual-parser-result-true-listp
  (true-listp (fn-article-parse bytes))
  :hints (("Goal" :in-theory (enable fn-article-parse fn-article-parse-under)))
  :rule-classes :type-prescription))

(defthm fn-lpv-actual-parser-catalog-verdict
  (equal (fn-hnov-parsed-okp (fn-article-parse bytes))
         (fn-article-result-okp (fn-article-parse bytes)))
  :hints (("Goal" :use ((:instance fn-article-successful-parse-syntax-p (octets bytes)))
           :in-theory (e/d (fn-hnov-parsed-okp)
                           (fn-article-parse fn-article-result-okp fn-article-syntax-p
                            fn-article-result-article)))))

(defthm fn-lpv-complete-feed-is-actual-catalog
  (implies (fn-cbor-octet-listp (nth h arena))
           (equal (fn-lpc-nov-value
                    (fn-lpc-feed (nth h arena) (fn-lpc-begin h (len (nth h arena)) pin)) arena)
                  (fn-hnov-of (nth h arena))))
  :hints (("Goal"
           :cases ((fn-article-result-okp (fn-article-parse (nth h arena))))
           :do-not-induct t
           :use ((:instance fn-lpv-actual-parser-catalog-verdict (bytes (nth h arena)))
                 (:instance fn-lpv-complete-feed-verdict-is-actual-parser (bytes (nth h arena)))
                 (:instance fn-lpv-complete-feed-tombstone-is-actual (bytes (nth h arena)))
                 (:instance fn-lpv-complete-feed-has-bounded-spans (bytes (nth h arena)))
                 (:instance fn-lpv-complete-feed-values-are-actual-content (bytes (nth h arena)))
                 (:instance fn-lpv-span-values-are-arena-values
                   (spans (fn-lpc-at 8 (fn-lpc-at 4
                           (fn-lpc-feed (nth h arena) (fn-lpc-begin h (len (nth h arena)) pin)))))
                   (bound (len (nth h arena)))))
           :in-theory (union-theories
             '(fn-lpc-nov-value fn-lpc-field fn-hnov-of fn-hnov-of-parsed fn-hnov-field
               car-cons cdr-cons cons-equal fn-lpv-nil-span-value-by-definition)
             (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))))))

; Host-called concrete source tick; the only source-domain requirement is
; octets. Invalid grammar is included, and the actual codec ceiling is
; decided by begin and the reference parser rather than assumed here.
(defthm fn-lpc-tick-full-nov-is-actual-catalog
  (implies (fn-cbor-octet-listp (nth h fn-arena))
           (equal (fn-lpc-nov-value
                    (mv-nth 0 (fn-lpc-tick
                                (fn-lpc-begin h (fn-arena-payload-len h fn-arena) pin)
                                (fn-arena-payload-len h fn-arena) fn-arena)) fn-arena)
                  (fn-hnov-of (nth h fn-arena))))
  :hints (("Goal" :use (fn-lpv-full-arena-tick-is-feed
                        (:instance fn-lpv-complete-feed-is-actual-catalog (arena fn-arena)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (executable-counterpart-theory :here)))))

(defthm fn-lpc-agrees-with-actual-catalog
  (implies (fn-cbor-octet-listp bytes) (fn-lpc-agreesp bytes pin))
  :hints (("Goal"
           :use ((:instance fn-lpv-complete-feed-is-actual-catalog (h 0) (arena (list bytes)))
                 (:instance fn-lpc-feed-body-lines-is-body-lines-of-all-tails
                    (h 0) (n (len bytes))))
           :in-theory (union-theories '(fn-lpc-agreesp nth car-cons cdr-cons)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here))))))
