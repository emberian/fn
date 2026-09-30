; Normalization and source-slice algebra for byte cursor -> line projection.
; These are proof functions; the served candidate keeps immutable spans.
(in-package "ACL2")
(include-book "legacy-parser-header")
(include-book "nov-line-projection")

(defthm fn-lpv-scrub-append-framed
  (implies (fn-article-body-crlfp a)
           (equal (fn-nov-scrub (append a b))
                  (append (fn-nov-scrub a) (fn-nov-scrub b))))
  :hints (("Goal" :induct (fn-article-body-crlfp a)
           :in-theory (enable fn-article-body-crlfp fn-nov-scrub
                               fn-ag-car fn-ag-cdr))))

(defthm fn-lpv-header-bytes-are-framed
  (implies (fn-article-header-bytes-p a) (fn-article-body-crlfp a))
  :hints (("Goal" :induct (fn-article-header-bytes-p a)
           :in-theory (enable fn-article-header-bytes-p fn-article-header-bytep
                               fn-article-wspp fn-article-vcharp fn-article-body-crlfp))))

(defthm fn-lpv-content-append
  (equal (fn-nov-value-content (append a b))
         (if (consp a) (append (fn-nov-value-content a) b)
           (fn-nov-value-content b)))
  :hints (("Goal" :in-theory (enable fn-nov-value-content fn-ag-car fn-ag-cdr))))

(defthm fn-lpv-content-header-bytes
  (implies (fn-article-header-bytes-p a)
           (fn-article-header-bytes-p (fn-nov-value-content a)))
  :hints (("Goal" :in-theory (enable fn-nov-value-content fn-article-header-bytes-p))))

(defthm fn-lpv-unfolded-append-normalization
  (implies (fn-article-header-bytes-p a)
           (equal (fn-nov-scrub (fn-nov-value-content (append a b)))
                  (if (consp a)
                      (append (fn-nov-scrub (fn-nov-value-content a))
                              (fn-nov-scrub b))
                    (fn-nov-scrub (fn-nov-value-content b)))))
  :hints (("Goal" :in-theory
           (disable fn-nov-scrub fn-nov-value-content fn-article-header-bytes-p))))

(defthm fn-lpv-value-content-keeps-visibility
  (equal (fn-article-has-vcharp (fn-nov-value-content a))
         (fn-article-has-vcharp a))
  :hints (("Goal" :in-theory (enable fn-nov-value-content fn-article-has-vcharp
                                      fn-article-vcharp))))

(defthm fn-lpv-scrub-keeps-visibility
  (equal (fn-article-has-vcharp (fn-nov-scrub a))
         (fn-article-has-vcharp a))
  :hints (("Goal" :induct (fn-nov-scrub a)
           :in-theory (enable fn-nov-scrub fn-nov-scrub-byte fn-article-has-vcharp
                               fn-article-vcharp fn-ag-car fn-ag-cdr))))

; A physically complete CRLF is removed, including at a source-span join.
(defthm fn-lpv-scrub-fold-join
  (implies (fn-article-body-crlfp raw)
           (equal (fn-nov-scrub (append raw (cons 13 (cons 10 line))))
                  (append (fn-nov-scrub raw) (fn-nov-scrub line))))
  :hints (("Goal" :expand ((fn-nov-scrub (cons 13 (cons 10 line))))
           :in-theory (disable fn-nov-scrub fn-article-body-crlfp))))

; A slice is proof-only vocabulary for the bytes owned by one immutable
; reference. Bounds, rather than a fresh source recognizer, justify reads.
(defun fn-lpv-slice (source start end)
  (declare (xargs :guard t :verify-guards nil))
  (take (nfix (- (nfix end) (nfix start)))
        (nthcdr (nfix start) source)))

(defthm fn-lpv-take-append-prefix
  (implies (and (natp n) (<= n (len a)))
           (equal (take n (append a b)) (take n a)))
  :hints (("Goal" :induct (take n a) :in-theory (enable take))))

(defthm fn-lpv-take-through-append
  (implies (natp n)
           (equal (take (+ (len a) n) (append a b))
                  (append a (take n b))))
  :hints (("Goal" :induct (len a) :in-theory (enable take))))

(defthm fn-lpv-nthcdr-append-prefix
  (implies (and (natp n) (<= n (len a)))
           (equal (nthcdr n (append a b))
                  (append (nthcdr n a) b)))
  :hints (("Goal" :induct (nthcdr n a) :in-theory (enable nthcdr))))

(defthm fn-lpv-len-nthcdr
  (equal (len (nthcdr n a)) (nfix (- (len a) (nfix n))))
  :hints (("Goal" :induct (nthcdr n a) :in-theory (enable nthcdr))))

(defthm fn-lpv-take-len
  (implies (true-listp a) (equal (take (len a) a) a))
  :hints (("Goal" :induct (len a) :in-theory (enable take))))

(defthm fn-lpv-true-listp-nthcdr
  (implies (true-listp a) (true-listp (nthcdr n a)))
  :hints (("Goal" :induct (nthcdr n a) :in-theory (enable nthcdr))))

(defthm fn-lpv-slice-within-prefix
  (implies (and (natp start) (natp end) (<= start end) (<= end (len a)))
           (equal (fn-lpv-slice (append a b) start end)
                  (fn-lpv-slice a start end)))
  :hints (("Goal" :in-theory (enable fn-lpv-slice))))

(defthm fn-lpv-slice-extended-prefix
  (implies (and (true-listp a) (true-listp b) (natp start) (<= start (len a)))
           (equal (fn-lpv-slice (append a b) start (+ (len a) (len b)))
                  (append (fn-lpv-slice a start (len a)) b)))
  :hints (("Goal" :in-theory (enable fn-lpv-slice))))

(defthm fn-lpv-header-byte-singleton-framed
  (implies (fn-article-header-bytep byte)
           (fn-article-body-crlfp (list byte)))
  :hints (("Goal" :in-theory
           (enable fn-article-header-bytep fn-article-wspp fn-article-vcharp
                   fn-article-body-crlfp))))

(defthm fn-lpv-framed-append
  (implies (and (fn-article-body-crlfp a) (fn-article-body-crlfp b))
           (fn-article-body-crlfp (append a b)))
  :hints (("Goal" :induct (fn-article-body-crlfp a)
           :in-theory (enable fn-article-body-crlfp))))

(defthm fn-lpv-slice-at-end
  (implies (and (true-listp a) (true-listp b))
           (equal (fn-lpv-slice (append a b) (len a) (+ (len a) (len b))) b))
  :hints (("Goal" :in-theory (enable fn-lpv-slice))))

; This relation is logical only. VALUE is the existing parser's unfolded
; value; SOURCE is the already-consumed raw prefix. An unseen empty value
; does not yet own a span. A seen value's framing is retained in the source
; and removed exactly by fn-nov-scrub, never by the executable byte tick.
(defun fn-lpv-value-state-p (s source value)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp source) (fn-article-header-bytes-p value)
       (equal (fn-lpc-at 9 s) (consp value))
       (equal (fn-lpc-at 3 s) (fn-article-has-vcharp value))
       (or (not (consp value))
           (and (natp (fn-lpc-at 4 s)) (<= (fn-lpc-at 4 s) (len source))
                (fn-article-body-crlfp
                 (fn-lpv-slice source (fn-lpc-at 4 s) (len source)))
                (equal (fn-nov-scrub
                        (fn-lpv-slice source (fn-lpc-at 4 s) (len source)))
                       (fn-nov-scrub (fn-nov-value-content value)))))))

(defthm fn-lpv-value-byte-start
  (implies (fn-article-header-bytep byte)
           (equal (fn-lpc-at 4 (fn-lpc-value-byte s byte pos))
                  (if (fn-lpc-at 9 s) (fn-lpc-at 4 s)
                    (if (equal byte 32) (+ 1 pos) pos))))
  :hints (("Goal" :in-theory (enable fn-lpc-value-byte fn-lpc-at))))

(defthm fn-lpv-has-vchar-append
  (equal (fn-article-has-vcharp (append a b))
         (or (fn-article-has-vcharp a) (fn-article-has-vcharp b)))
  :hints (("Goal" :induct (fn-article-has-vcharp a)
           :in-theory (enable fn-article-has-vcharp))))

(defthm fn-lpv-header-bytes-append
  (implies (and (fn-article-header-bytes-p a) (fn-article-header-bytes-p b))
           (fn-article-header-bytes-p (append a b)))
  :hints (("Goal" :induct (fn-article-header-bytes-p a)
           :in-theory (enable fn-article-header-bytes-p))))

(defthm fn-lpv-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-lpv-true-listp-append
  (implies (true-listp b) (true-listp (append a b))))

(defthm fn-lpv-consp-append
  (equal (consp (append a b)) (or (consp a) (consp b))))

(defthm fn-lpv-slice-empty
  (equal (fn-lpv-slice source at at) nil)
  :hints (("Goal" :in-theory (enable fn-lpv-slice))))

(defthm fn-lpv-value-byte-visible
  (implies (fn-article-header-bytep byte)
           (equal (fn-lpc-at 3 (fn-lpc-value-byte s byte pos))
                  (or (fn-lpc-at 3 s) (fn-article-vcharp byte))))
  :hints (("Goal" :in-theory (enable fn-lpc-value-byte fn-lpc-at))))

(defthm fn-lpv-value-byte-seen
  (implies (fn-article-header-bytep byte)
           (equal (fn-lpc-at 9 (fn-lpc-value-byte s byte pos)) t))
  :hints (("Goal" :in-theory (enable fn-lpc-value-byte fn-lpc-at))))

(defthm fn-lpv-header-singleton
  (equal (fn-article-header-bytes-p (list byte)) (fn-article-header-bytep byte))
  :hints (("Goal" :in-theory (enable fn-article-header-bytes-p))))

(defthm fn-lpv-visible-singleton
  (equal (fn-article-has-vcharp (list byte)) (fn-article-vcharp byte))
  :hints (("Goal" :in-theory (enable fn-article-has-vcharp))))

(defthm fn-lpv-content-singleton
  (equal (fn-nov-value-content (list byte)) (if (equal byte 32) nil (list byte)))
  :hints (("Goal" :in-theory (enable fn-nov-value-content))))

(defthm fn-lpv-len-cons
  (equal (len (cons a b)) (+ 1 (len b))))

(defthm fn-lpv-slice-one-more-byte
  (implies (and (true-listp source) (natp start) (<= start (len source)))
           (equal (fn-lpv-slice (append source (list byte)) start (+ 1 (len source)))
                  (append (fn-lpv-slice source start (len source)) (list byte))))
  :hints (("Goal"
           :use ((:instance fn-lpv-slice-extended-prefix (a source) (b (list byte))))
           :in-theory (disable fn-lpv-slice fn-lpv-slice-extended-prefix))))

(defthm fn-lpv-append-nil-left
  (equal (append nil a) a))

(defthm fn-lpv-value-byte-refines-unfolded-append
  (implies (and (fn-lpv-value-state-p s source value)
                (fn-article-header-bytep byte))
           (fn-lpv-value-state-p
            (fn-lpc-value-byte s byte (len source))
            (append source (list byte)) (append value (list byte))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-value-state-p)
                (fn-lpc-value-byte fn-lpc-at fn-lpv-slice fn-nov-scrub
                 fn-nov-value-content fn-article-header-bytep fn-article-header-bytes-p
                 fn-article-has-vcharp fn-article-vcharp fn-article-body-crlfp
                 binary-append len fn-lpv-content-append)))))

(defthm fn-lpv-slice-add-framing
  (implies (and (true-listp source) (natp start) (<= start (len source)))
           (equal (fn-lpv-slice (append source '(13 10)) start (+ 2 (len source)))
                  (append (fn-lpv-slice source start (len source)) '(13 10))))
  :hints (("Goal"
           :use ((:instance fn-lpv-slice-extended-prefix (a source) (b '(13 10))))
           :in-theory (disable fn-lpv-slice fn-lpv-slice-extended-prefix))))

(defthm fn-lpv-value-state-skips-fold-framing
  (implies (fn-lpv-value-state-p s source value)
           (fn-lpv-value-state-p s (append source '(13 10)) value))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-value-state-p)
                (fn-lpc-at fn-lpv-slice fn-nov-scrub fn-nov-value-content
                 fn-article-header-bytes-p fn-article-has-vcharp
                 fn-article-body-crlfp binary-append len)))))

(defthm fn-lpv-value-state-unrelated-slot
  (implies (and (natp k) (not (equal k 3)) (not (equal k 4))
                (not (equal k 9)))
           (equal (fn-lpv-value-state-p (fn-lpc-put k x s) source value)
                  (fn-lpv-value-state-p s source value)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-value-state-p) (fn-lpc-put fn-lpc-at fn-lpv-slice
                 fn-article-header-bytes-p fn-article-body-crlfp
                 fn-article-has-vcharp fn-nov-scrub fn-nov-value-content)))))

; The real header transition takes exactly the value-byte step on its
; reachable value phase. Grammar acceptance and counters stay with the
; separate control simulation; this theorem covers the retained source.
(defthm fn-lpv-header-value-is-value-byte
  (implies (and (equal (fn-lpc-at 0 s) :value)
                (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
                (fn-article-header-bytep byte))
           (equal (fn-lpc-header-byte s byte pos h pin)
                  (fn-lpc-value-byte s byte pos)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-article-header-bytep
                 fn-article-wspp fn-article-vcharp)
                (fn-lpc-value-byte fn-lpc-at fn-lpc-put fn-lpc-header-bad)))))

(defthm fn-lpv-actual-header-value-refines-unfolded-append
  (implies (and (fn-lpv-value-state-p s source value)
                (equal (fn-lpc-at 0 s) :value)
                (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
                (fn-article-header-bytep byte))
           (fn-lpv-value-state-p
            (fn-lpc-header-byte s byte (len source) h pin)
            (append source (list byte)) (append value (list byte))))
  :hints (("Goal"
           :use ((:instance fn-lpv-header-value-is-value-byte (pos (len source)))
                 fn-lpv-value-byte-refines-unfolded-append)
           :in-theory
           (disable fn-lpv-value-state-p fn-lpc-header-byte fn-lpc-value-byte
                    fn-lpc-at fn-article-header-bytep binary-append len nfix
                    fn-lpv-header-value-is-value-byte
                    fn-lpv-value-byte-refines-unfolded-append))))

(defthm fn-lpv-name-key-matches-name
  (implies (and (natp k) (< k 5))
           (equal (equal (fn-lpc-name-key
                          (fn-lpc-names-scan *fn-lpc-names* bytes)) k)
                  (equal (fn-article-ascii-downcase bytes)
                         (fn-lpc-at k *fn-lpc-names*))))
  :hints (("Goal"
           :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3) (equal k 4))
           :use ((:instance fn-lpc-selected-name-exact (k 0))
                 (:instance fn-lpc-selected-name-exact (k 1))
                 (:instance fn-lpc-selected-name-exact (k 2))
                 (:instance fn-lpc-selected-name-exact (k 3))
                 (:instance fn-lpc-selected-name-exact (k 4)))
           :in-theory
           (e/d (fn-lpc-name-key)
                (fn-lpc-at fn-lpc-names-scan fn-article-ascii-downcase
                 fn-lpc-selected-name-exact)))))

(defthm fn-lpv-close-fields-column
  (implies (natp k)
           (equal (fn-lpc-at k (fn-lpc-close-fields s h pin))
                  (if (and (natp (fn-lpc-at 6 s)) (< (fn-lpc-at 6 s) 5)
                           (equal k (fn-lpc-at 6 s))
                           (not (fn-lpc-at k (fn-lpc-at 8 s))))
                      (fn-lpc-span h (nfix (fn-lpc-at 4 s))
                                   (nfix (fn-lpc-at 5 s)) pin)
                    (fn-lpc-at k (fn-lpc-at 8 s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-close-fields) (fn-lpc-put fn-lpc-at fn-lpc-span)))))

; Optional normalized hits preserve absence separately from an empty
; first value. This is the same distinction made by fn-novlp-add-field.
(defun fn-lpv-column (column)
  (declare (xargs :guard t :verify-guards nil))
  (and column (list (fn-nov-scrub (fn-nov-value-content (car column))))))

(defun fn-lpv-columns (columns)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp columns)
      (cons (fn-lpv-column (car columns)) (fn-lpv-columns (cdr columns))) nil))

(defun fn-lpv-add-normal-field (columns field names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (cons (or (car columns)
                (and field (fn-article-field-name-equalp field (car names))
                     (list (fn-nov-scrub
                            (fn-nov-value-content
                             (fn-article-field-unfolded-value field))))))
            (fn-lpv-add-normal-field (cdr columns) field (cdr names))) nil))

(defthm fn-lpv-normalization-commutes-with-first-field
  (equal (fn-lpv-columns (fn-novlp-add-field columns field names))
         (fn-lpv-add-normal-field (fn-lpv-columns columns) field names))
  :hints (("Goal" :induct (fn-novlp-add-field columns field names)
           :in-theory
           (e/d (fn-lpv-columns fn-lpv-column fn-novlp-add-field fn-lpv-add-normal-field)
                (fn-nov-scrub fn-nov-value-content fn-article-field-name-equalp
                 fn-article-field-unfolded-value)))))

(defthm fn-lpv-normal-columns-retain-empty-first-value
  (implies (car columns)
           (equal (car (fn-lpv-columns (fn-novlp-add-field columns field names)))
                  (if (consp names) (fn-lpv-column (car columns)) nil)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-columns fn-lpv-column fn-novlp-add-field fn-lpv-add-normal-field)
                (fn-nov-scrub fn-nov-value-content fn-article-field-name-equalp
                 fn-article-field-unfolded-value)))))

(defthm fn-lpv-value-state-empty
  (implies (and (true-listp source) (not (fn-lpc-at 9 s)) (not (fn-lpc-at 3 s)))
           (fn-lpv-value-state-p s source nil))
  :hints (("Goal" :in-theory (e/d (fn-lpv-value-state-p) (fn-lpc-at)))))

(defthm fn-lpv-header-first-is-value-byte
  (implies (and (equal (fn-lpc-at 0 s) :first)
                (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
                (fn-article-wspp byte))
           (equal (fn-lpc-header-byte s byte pos h pin)
                  (fn-lpc-value-byte s byte pos)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-article-wspp)
                (fn-lpc-value-byte fn-lpc-at fn-lpc-put fn-lpc-header-bad)))))

(defthm fn-lpv-header-fold-is-value-byte
  (implies (and (equal (fn-lpc-at 0 s) :start) (fn-lpc-at 2 s)
                (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
                (fn-article-wspp byte))
           (equal (fn-lpc-header-byte s byte pos h pin)
                  (fn-lpc-value-byte (fn-lpc-put 10 :fold-empty s) byte pos)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-article-wspp)
                (fn-lpc-value-byte fn-lpc-at fn-lpc-put fn-lpc-header-bad)))))

(defthm fn-lpv-actual-header-fold-refines-unfolded-append
  (implies (and (fn-lpv-value-state-p s source value)
                (equal (fn-lpc-at 0 s) :start) (fn-lpc-at 2 s)
                (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
                (fn-article-wspp byte))
           (fn-lpv-value-state-p
            (fn-lpc-header-byte s byte (len source) h pin)
            (append source (list byte)) (append value (list byte))))
  :hints (("Goal"
           :use ((:instance fn-lpv-header-fold-is-value-byte (pos (len source)))
                 (:instance fn-lpv-value-byte-refines-unfolded-append
                            (s (fn-lpc-put 10 :fold-empty s))))
           :in-theory
           (e/d (fn-article-wspp fn-article-header-bytep)
                (fn-lpv-value-state-p fn-lpc-header-byte fn-lpc-value-byte
                 fn-lpc-put fn-lpc-at binary-append len nfix
                 fn-lpv-header-fold-is-value-byte
                 fn-lpv-value-byte-refines-unfolded-append)))))

(defthm fn-lpv-header-line-end
  (implies (and (member-eq (fn-lpc-at 0 s) '(:first :value))
                (not (equal (fn-lpc-at 10 s) :fold-empty)))
           (equal (fn-lpc-header-byte (fn-lpc-header-byte s 13 pos h pin)
                                      10 (+ 1 pos) h pin)
                  (fn-lpc-put 1 0 (fn-lpc-put 0 :start (fn-lpc-put 5 pos s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-lpc-at fn-lpc-put)
                (fn-lpc-header-bad fn-lpc-value-byte fn-lpc-close-fields
                 fn-lpc-name-step fn-lpc-name-key)))))

(defthm fn-lpv-framing-byte-preserves-value-record
  (implies (or (equal byte 13) (equal byte 10))
           (equal (fn-lpv-value-state-p (fn-lpc-header-byte s byte pos h pin) source value)
                  (fn-lpv-value-state-p s source value)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-lpc-header-bad)
                (fn-lpc-at fn-lpc-put fn-lpv-value-state-p fn-lpc-close-fields
                 fn-lpc-value-byte fn-lpc-name-key fn-lpc-name-step)))))

(defthm fn-lpv-actual-line-end-keeps-unfolded-value
  (implies (fn-lpv-value-state-p s source value)
           (fn-lpv-value-state-p
            (fn-lpc-header-byte (fn-lpc-header-byte s 13 (len source) h pin)
                                10 (+ 1 (len source)) h pin)
            (append source '(13 10)) value))
  :hints (("Goal" :in-theory
           (disable fn-lpv-value-state-p fn-lpc-header-byte fn-lpc-value-byte
                    fn-lpc-put fn-lpc-at binary-append len))))

(defthm fn-lpv-completed-line-span-is-unfolded-value
  (implies (and (fn-lpv-value-state-p s source value) (consp value)
                (member-eq (fn-lpc-at 0 s) '(:first :value))
                (not (equal (fn-lpc-at 10 s) :fold-empty)))
           (let ((out (fn-lpc-header-byte
                       (fn-lpc-header-byte s 13 (len source) h pin)
                       10 (+ 1 (len source)) h pin)))
             (equal (fn-nov-scrub
                     (fn-lpv-slice (append source '(13 10))
                                   (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                    (fn-nov-scrub (fn-nov-value-content value)))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-value-state-p)
                (fn-lpc-header-byte fn-lpc-put fn-lpc-at fn-lpv-slice
                 fn-nov-scrub fn-nov-value-content fn-article-header-bytes-p
                 fn-article-body-crlfp fn-article-has-vcharp binary-append len)))))
