; First-hit selected-column refinement of immutable source spans.
(in-package "ACL2")
(include-book "legacy-parser-value-run")
(include-book "legacy-parser-reference")
(include-book "legacy-parser-composition")

(defun fn-lpv-span-column (span source)
  (declare (xargs :guard t :verify-guards nil))
  (and span
       (list (fn-nov-scrub
              (fn-lpv-slice source (fn-lpc-at 1 span)
                            (+ (nfix (fn-lpc-at 1 span)) (nfix (fn-lpc-at 2 span))))))))

(defthm fn-lpv-span-column-presence
  (iff (fn-lpv-span-column span source) span)
  :hints (("Goal" :in-theory (enable fn-lpv-span-column))))

(defthm fn-lpv-column-presence
  (iff (fn-lpv-column column) column)
  :hints (("Goal" :in-theory (enable fn-lpv-column))))

(local (defthm fn-lpv-cancel-start
  (implies (and (acl2-numberp a) (acl2-numberp b)) (equal (+ a (- a) b) b))
  :hints (("Goal" :in-theory (enable associativity-of-+ inverse-of-+)))))

(defthm fn-lpv-span-column-is-arena-abstraction
  (implies (and (fn-lpc-span-bound-p span h pin bound) (natp h))
           (equal (fn-lpv-span-column span (nth h arena))
                  (and span (list (fn-lpc-span-value span arena)))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-span-column fn-lpc-span-bound-p fn-lpc-span-value fn-lpv-slice)
                (fn-lpc-at fn-nov-scrub nth nthcdr take)))))

(defthm fn-lpv-span-column-stable-under-extension
  (implies (fn-lpc-span-bound-p span h pin (len source))
           (equal (fn-lpv-span-column span (append source rest))
                  (fn-lpv-span-column span source)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-span-column fn-lpc-span-bound-p)
                (fn-lpc-at fn-lpv-slice fn-nov-scrub binary-append len)))))

(defun fn-lpv-columns-equiv (spans columns source)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-lpv-span-column (fn-lpc-at 0 spans) source)
              (fn-lpv-column (fn-lpc-at 0 columns)))
       (equal (fn-lpv-span-column (fn-lpc-at 1 spans) source)
              (fn-lpv-column (fn-lpc-at 1 columns)))
       (equal (fn-lpv-span-column (fn-lpc-at 2 spans) source)
              (fn-lpv-column (fn-lpc-at 2 columns)))
       (equal (fn-lpv-span-column (fn-lpc-at 3 spans) source)
              (fn-lpv-column (fn-lpc-at 3 columns)))
       (equal (fn-lpv-span-column (fn-lpc-at 4 spans) source)
              (fn-lpv-column (fn-lpc-at 4 columns)))))

(defthm fn-lpv-columns-equiv-at
  (implies (and (fn-lpv-columns-equiv spans columns source) (natp k) (< k 5))
           (equal (fn-lpv-span-column (fn-lpc-at k spans) source)
                  (fn-lpv-column (fn-lpc-at k columns))))
  :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3) (equal k 4))
           :in-theory
           (e/d (fn-lpv-columns-equiv)
                (fn-lpv-span-column fn-lpv-column fn-lpc-at)))))

(defthm fn-lpv-columns-equiv-stable-under-extension
  (implies (and (fn-lpv-columns-equiv spans columns source)
                (fn-lpc-spans-bound-p spans h pin (len source)))
           (fn-lpv-columns-equiv spans columns (append source rest)))
  :hints (("Goal"
           :use ((:instance fn-lpc-spans-bound-at (k 0) (pos (len source)))
                 (:instance fn-lpc-spans-bound-at (k 1) (pos (len source)))
                 (:instance fn-lpc-spans-bound-at (k 2) (pos (len source)))
                 (:instance fn-lpc-spans-bound-at (k 3) (pos (len source)))
                 (:instance fn-lpc-spans-bound-at (k 4) (pos (len source))))
           :in-theory
           (e/d (fn-lpv-columns-equiv)
                (fn-lpv-span-column fn-lpv-column fn-lpc-at fn-lpc-spans-bound-p
                 fn-lpc-span-bound-p fn-lpc-spans-bound-at binary-append len)))))

(defthm fn-lpv-span-column-of-span
  (implies (and (natp start) (natp end))
           (equal (fn-lpv-span-column (fn-lpc-span h start end pin) source)
                  (list (fn-nov-scrub (fn-lpv-slice source start end)))))
  :hints (("Goal" :expand ((:free (x) (take 0 x))) :in-theory
           (e/d (fn-lpv-span-column fn-lpc-span fn-lpv-slice fn-lpc-at)
                (fn-nov-scrub nthcdr take)))))

(defun fn-lpv-selectedp (key field)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (equal key 0) (and field (fn-article-field-name-equalp field *fn-nov-subject-name*)))
       (equal (equal key 1) (and field (fn-article-field-name-equalp field *fn-nov-from-name*)))
       (equal (equal key 2) (and field (fn-article-field-name-equalp field *fn-nov-date-name*)))
       (equal (equal key 3) (and field (fn-article-field-name-equalp field *fn-nov-message-id-name*)))
       (equal (equal key 4) (and field (fn-article-field-name-equalp field *fn-nov-references-name*)))))

(defthm fn-lpv-selectedp-at
  (implies (and (fn-lpv-selectedp key field) (natp k) (< k 5))
           (equal (equal key k)
                  (and field (fn-article-field-name-equalp field (fn-lpc-at k *fn-novlp-names*)))))
  :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3) (equal k 4))
           :in-theory (e/d (fn-lpv-selectedp) (fn-lpc-at fn-article-field-name-equalp)))))

(defthm fn-lpv-line-projection-add-field-column
  (implies (and (natp k) (< k 5))
           (equal (fn-lpc-at k (fn-novlp-add-field columns field *fn-novlp-names*))
                  (or (fn-lpc-at k columns)
                      (and field
                           (fn-article-field-name-equalp field (fn-lpc-at k *fn-novlp-names*))
                           (list (fn-article-field-unfolded-value field))))))
  :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3) (equal k 4))
           :in-theory
           (e/d (fn-lpc-at fn-novlp-add-field)
                (fn-article-field-name-equalp fn-article-field-unfolded-value)))))

(local (defthm fn-lpv-span-column-nil-by-definition
  (equal (fn-lpv-span-column nil source) nil)
  :hints (("Goal" :in-theory (enable fn-lpv-span-column)))))

(defthm fn-lpv-close-field-refines-column-at
  (implies
   (and (natp k) (< k 5)
        (fn-lpv-columns-equiv (fn-lpc-at 8 s) columns source)
        (fn-lpv-selectedp (fn-lpc-at 6 s) field)
        (or (not field)
            (equal (fn-nov-scrub
                    (fn-lpv-slice source (nfix (fn-lpc-at 4 s)) (nfix (fn-lpc-at 5 s))))
                   (fn-nov-scrub
                    (fn-nov-value-content (fn-article-field-unfolded-value field))))))
   (equal
    (fn-lpv-span-column (fn-lpc-at k (fn-lpc-close-fields s h pin)) source)
    (fn-lpv-column (fn-lpc-at k (fn-novlp-add-field columns field *fn-novlp-names*)))))
  :hints (("Goal"
           :use ((:instance fn-lpv-selectedp-at (key (fn-lpc-at 6 s)))
                 (:instance fn-lpv-columns-equiv-at (spans (fn-lpc-at 8 s))))
           :in-theory
           (e/d (fn-lpv-column)
                (fn-lpc-at fn-lpc-close-fields fn-lpc-span fn-lpv-span-column
                 fn-lpv-columns-equiv fn-lpv-selectedp fn-novlp-add-field
                 fn-article-field-unfolded-value fn-article-field-name-equalp
                 fn-lpv-slice fn-nov-scrub fn-nov-value-content
                 fn-lpv-selectedp-at fn-lpv-columns-equiv-at)))))

(defthm fn-lpv-close-field-refines-columns
  (implies
   (and (fn-lpv-columns-equiv (fn-lpc-at 8 s) columns source)
        (fn-lpv-selectedp (fn-lpc-at 6 s) field)
        (or (not field)
            (equal (fn-nov-scrub
                    (fn-lpv-slice source (nfix (fn-lpc-at 4 s)) (nfix (fn-lpc-at 5 s))))
                   (fn-nov-scrub
                    (fn-nov-value-content (fn-article-field-unfolded-value field))))))
   (fn-lpv-columns-equiv (fn-lpc-close-fields s h pin)
                         (fn-novlp-add-field columns field *fn-novlp-names*) source))
  :hints (("Goal"
           :use ((:instance fn-lpv-close-field-refines-column-at (k 0))
                 (:instance fn-lpv-close-field-refines-column-at (k 1))
                 (:instance fn-lpv-close-field-refines-column-at (k 2))
                 (:instance fn-lpv-close-field-refines-column-at (k 3))
                 (:instance fn-lpv-close-field-refines-column-at (k 4)))
           :in-theory
           (e/d (fn-lpv-columns-equiv)
                (fn-lpc-at fn-lpc-close-fields fn-lpv-selectedp fn-novlp-add-field
                 fn-lpv-span-column fn-lpv-column fn-lpv-slice fn-nov-scrub
                 fn-nov-value-content fn-article-field-unfolded-value
                 fn-lpv-close-field-refines-column-at fn-lpv-close-fields-column
                 fn-lpv-line-projection-add-field-column)))))

(defthm fn-lpv-run-preserves-header-bounds
  (implies (fn-lpc-header-bounds-p s h pin pos)
           (fn-lpc-header-bounds-p (fn-nlv-run bytes s pos h pin)
                                   h pin (+ pos (len bytes))))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :in-theory
           (e/d (fn-nlv-run)
                (fn-lpc-header-byte fn-lpc-header-bounds-p fn-lpc-at
                 fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-lpv-header-byte-preserves-natural-line-length
  (implies (natp (fn-lpc-at 1 s))
           (natp (fn-lpc-at 1 (fn-lpc-header-byte s byte pos h pin))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-lpc-header-bad fn-lpc-value-byte fn-lpc-at)
                (fn-lpc-put fn-lpc-name-key fn-lpc-name-step fn-lpc-close-fields)))))

(defthm fn-lpv-run-preserves-natural-line-length
  (implies (natp (fn-lpc-at 1 s))
           (natp (fn-lpc-at 1 (fn-nlv-run bytes s pos h pin))))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :in-theory (e/d (fn-nlv-run)
                           (fn-lpc-header-byte fn-lpc-at fn-nlv-run-phase-is-control-run-phase)))))

(defun fn-lpv-header-equiv (s source current columns h pin)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-lpc-header-bounds-p s h pin (len source))
       (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
       (equal (fn-lpc-at 2 s) (and current t))
       (fn-lpv-value-state-p s source (fn-article-field-unfolded-value current))
       (fn-lpv-selectedp (fn-lpc-at 6 s) current)
       (fn-lpv-columns-equiv (fn-lpc-at 8 s) columns source)
       (or (not (consp (fn-article-field-unfolded-value current)))
           (equal (fn-nov-scrub
                   (fn-lpv-slice source (nfix (fn-lpc-at 4 s)) (nfix (fn-lpc-at 5 s))))
                  (fn-nov-scrub
                   (fn-nov-value-content (fn-article-field-unfolded-value current)))))))

(defthm fn-lpv-header-begin-equiv
  (fn-lpv-header-equiv (fn-lpc-header-begin) nil nil
                       (fn-novlp-columns nil *fn-novlp-names*) h pin)
  :hints (("Goal" :in-theory
           (enable fn-lpv-header-equiv fn-lpc-header-begin fn-lpc-header-bounds-p
                   fn-lpc-spans-bound-p fn-lpc-span-bound-p fn-lpc-at
                   fn-lpv-value-state-p fn-lpv-selectedp fn-lpv-columns-equiv
                   fn-lpv-span-column fn-lpv-column fn-novlp-columns fn-novlp-first))))

(defthm fn-lpv-header-equiv-close-columns
  (implies (and (fn-lpv-header-equiv s source current columns h pin)
                (fn-article-field-closedp current))
           (fn-lpv-columns-equiv (fn-lpc-close-fields s h pin)
                                 (fn-novlp-add-field columns current *fn-novlp-names*) source))
  :hints (("Goal"
           :use ((:instance fn-lpv-close-field-refines-columns (field current)))
           :in-theory
           (e/d (fn-lpv-header-equiv fn-article-field-closedp fn-article-has-vcharp)
                (fn-lpc-close-fields fn-lpv-columns-equiv fn-lpv-selectedp
                 fn-lpv-value-state-p fn-lpc-header-bounds-p fn-lpc-at
                 fn-lpv-slice fn-nov-scrub fn-nov-value-content
                 fn-article-field-unfolded-value fn-novlp-add-field
                 fn-lpv-close-field-refines-columns)))))

(defthm fn-lpv-valid-fold-line-control
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (fn-lpc-at 2 s) (fn-article-fold-linep line)
                (<= (len line) *fn-article-max-line-octets*))
           (equal (fn-nlv-control (fn-nlv-run (append line '(13 10)) s pos h pin))
                  '(:start 0 t t :fold-visible)))
  :hints (("Goal"
           :use ((:instance fn-nlv-fold-line-control
                            (visible (and (fn-lpc-at 3 s) t)) (old-mode (fn-lpc-at 10 s))))
           :in-theory
           (e/d (fn-nlv-control fn-article-fold-linep)
                (fn-lpc-at fn-nlv-run fn-nlv-control-run fn-article-header-bytes-p
                 fn-article-wspp fn-article-has-vcharp binary-append len
                 fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-lpv-valid-fold-line-start
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (fn-lpc-at 2 s) (fn-article-fold-linep line)
                (<= (len line) *fn-article-max-line-octets*))
           (and (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s pos h pin)) :start)
                (equal (fn-lpc-at 1 (fn-nlv-run (append line '(13 10)) s pos h pin)) 0)))
  :hints (("Goal"
           :use (fn-lpv-valid-fold-line-control
                 (:instance fn-lpv-control-at-by-definition
                            (s (fn-nlv-run (append line '(13 10)) s pos h pin)))
                 (:instance fn-lpv-run-preserves-natural-line-length
                            (bytes (append line '(13 10)))))
           :in-theory
           (disable fn-lpc-at fn-nlv-run fn-nlv-control fn-nlv-control-run
                    fn-nlv-run-phase-is-control-run-phase fn-nlv-control-run-is-actual-header-run
                    fn-lpv-valid-fold-line-control fn-lpv-control-at-by-definition
                    fn-article-fold-linep binary-append len))))

(defthm fn-lpv-selectedp-add-fold
  (implies current
           (equal (fn-lpv-selectedp key (fn-article-add-fold current line))
                  (fn-lpv-selectedp key current)))
  :hints (("Goal" :in-theory
           (enable fn-lpv-selectedp fn-article-add-fold fn-article-make-field
                   fn-article-field-name-equalp fn-article-field-name))))

(local (defthm fn-lpv-add-fold-value-by-definition
  (equal (fn-article-field-unfolded-value (fn-article-add-fold current line))
         (append (fn-article-field-unfolded-value current) line))
  :hints (("Goal" :in-theory (enable fn-article-add-fold fn-article-field-unfolded-value fn-article-make-field)))))
(local (defthm fn-lpv-add-fold-present-by-definition
  (fn-article-add-fold current line)
  :hints (("Goal" :in-theory (enable fn-article-add-fold fn-article-make-field)))))

(defthm fn-lpv-header-equiv-fold-line
  (implies (and (fn-lpv-header-equiv s source current columns h pin)
                current (fn-article-fold-linep line)
                (<= (len line) *fn-article-max-line-octets*))
           (fn-lpv-header-equiv
            (fn-nlv-run (append line '(13 10)) s (len source) h pin)
            (append source (append line '(13 10)))
            (fn-article-add-fold current line) columns h pin))
  :hints (("Goal"
           :use ((:instance fn-lpv-columns-equiv-stable-under-extension
                            (spans (fn-lpc-at 8 s)) (rest (append line '(13 10))))
                 (:instance fn-lpv-run-preserves-header-bounds (bytes (append line '(13 10)))
                            (pos (len source)))
                 (:instance fn-lpv-valid-fold-line-start (pos (len source)))
                 (:instance fn-lpv-run-fold-line-refines-unfolded-append
                            (bytes line) (value (fn-article-field-unfolded-value current)))
                 (:instance fn-lpv-fold-line-span-is-unfolded-value
                            (bytes line) (value (fn-article-field-unfolded-value current)))
                 (:instance fn-lpv-fold-line-fixed-column (bytes line) (pos (len source)) (k 2))
                 (:instance fn-lpv-fold-line-fixed-column (bytes line) (pos (len source)) (k 6))
                 (:instance fn-lpv-fold-line-fixed-column (bytes line) (pos (len source)) (k 8)))
           :in-theory
           (e/d (fn-lpv-header-equiv fn-article-fold-linep fn-lpc-header-bounds-p)
                (fn-lpc-at fn-nlv-run fn-lpc-header-byte fn-lpv-columns-equiv
                 fn-lpv-selectedp fn-lpv-value-state-p fn-lpc-spans-bound-p
                 fn-lpv-slice fn-nov-scrub fn-nov-value-content
                 fn-article-header-bytes-p fn-article-wspp fn-article-has-vcharp
                 fn-article-field-raw-lines fn-article-field-name binary-append len
                 fn-nlv-run-phase-is-control-run-phase
                 fn-lpv-columns-equiv-stable-under-extension fn-nlv-run-append
                 fn-lpv-content-append fn-lpv-unfolded-append-normalization
                 fn-article-add-fold fn-article-field-unfolded-value
                 fn-lpv-run-preserves-header-bounds fn-lpv-valid-fold-line-start
                 fn-lpv-run-fold-line-refines-unfolded-append
                 fn-lpv-fold-line-span-is-unfolded-value fn-lpv-fold-line-fixed-column)))))

(defthm fn-lpv-selectedp-new-field
  (fn-lpv-selectedp
   (fn-lpc-name-key (fn-lpc-names-scan *fn-lpc-names* name))
   (fn-article-make-field raw-lines (fn-article-ascii-downcase name) value))
  :hints (("Goal"
           :use ((:instance fn-lpv-name-key-matches-name (bytes name) (k 0))
                 (:instance fn-lpv-name-key-matches-name (bytes name) (k 1))
                 (:instance fn-lpv-name-key-matches-name (bytes name) (k 2))
                 (:instance fn-lpv-name-key-matches-name (bytes name) (k 3))
                 (:instance fn-lpv-name-key-matches-name (bytes name) (k 4)))
           :in-theory
           (e/d (fn-lpv-selectedp fn-article-make-field fn-article-field-name
                 fn-article-field-name-equalp)
                (fn-lpc-name-key fn-lpc-names-scan fn-article-ascii-downcase
                 fn-lpv-name-key-matches-name fn-lpc-at)))))

(defthm fn-lpv-header-equiv-old-closed
  (implies (and (fn-lpv-header-equiv s source current columns h pin)
                (fn-article-field-closedp current))
           (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-header-equiv fn-lpv-value-state-p fn-article-field-closedp)
                (fn-lpc-at fn-lpv-selectedp fn-lpv-columns-equiv fn-lpc-header-bounds-p
                 fn-lpv-slice fn-nov-scrub fn-nov-value-content fn-article-has-vcharp
                 fn-article-field-unfolded-value fn-article-header-bytes-p)))))

(defthm fn-lpv-valid-new-field-line-control
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name) (fn-article-header-bytes-p value)
                (or (not (consp value)) (fn-article-wspp (car value)))
                (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*))
           (equal (fn-nlv-control
                   (fn-nlv-run (append name (cons 58 (append value '(13 10)))) s pos h pin))
                  (list :start 0 t (and (fn-article-has-vcharp value) t) :plain)))
  :hints (("Goal"
           :use ((:instance fn-nlv-new-field-line-control
                            (current (and (fn-lpc-at 2 s) t))
                            (visible (and (fn-lpc-at 3 s) t)) (old-mode (fn-lpc-at 10 s))))
           :in-theory
           (e/d (fn-nlv-control)
                (fn-lpc-at fn-nlv-run fn-nlv-control-run fn-article-header-bytes-p
                 fn-article-namep fn-article-wspp fn-article-has-vcharp binary-append len
                 fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-lpv-valid-new-field-line-start
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name) (fn-article-header-bytes-p value)
                (or (not (consp value)) (fn-article-wspp (car value)))
                (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*))
           (let ((out (fn-nlv-run (append name (cons 58 (append value '(13 10)))) s pos h pin)))
             (and (equal (fn-lpc-at 0 out) :start) (equal (fn-lpc-at 1 out) 0))))
  :hints (("Goal"
           :use (fn-lpv-valid-new-field-line-control
                 (:instance fn-lpv-control-at-by-definition
                    (s (fn-nlv-run (append name (cons 58 (append value '(13 10)))) s pos h pin)))
                 (:instance fn-lpv-run-preserves-natural-line-length
                    (bytes (append name (cons 58 (append value '(13 10)))))))
           :in-theory
           (e/d (fn-lpc-at)
                (fn-nlv-run fn-nlv-control fn-nlv-control-run
                 fn-nlv-run-phase-is-control-run-phase fn-nlv-control-run-is-actual-header-run
                 fn-lpv-valid-new-field-line-control fn-lpv-control-at-by-definition
                 fn-article-namep fn-article-header-bytes-p fn-article-wspp
                 fn-article-has-vcharp binary-append len)))))

(local (defthm fn-lpv-col-append-associative
  (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fn-lpv-col-append-cons
  (equal (append (cons a b) c) (cons a (append b c)))))
(local (defthm fn-lpv-col-append-atom
  (implies (not (consp a)) (equal (append a b) b))))

(defthm fn-lpv-new-field-line-current-present
  (implies (and (natp pos)
                (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name) (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (len name) 1 (len bytes)) *fn-article-max-line-octets*))
           (equal (fn-lpc-at 2
                    (fn-nlv-run (append name (cons 58 (append bytes '(13 10)))) s pos h pin)) t))
  :hints (("Goal"
           :use ((:instance fn-lpv-first-line-fixed-column
                    (s (fn-nlv-run (append name '(58)) s pos h pin))
                    (pos (+ pos 1 (len name))) (k 2))
                 (:instance fn-nlv-run-append (a (append name '(58)))
                            (b (append bytes '(13 10)))))
           :in-theory
           (e/d (fn-lpc-at)
                (fn-nlv-run fn-lpc-header-byte fn-lpc-name-key fn-lpc-names-scan
                 fn-lpc-close-fields fn-article-header-bytes-p fn-article-namep
                 fn-article-wspp binary-append len fn-nlv-run-append
                 fn-lpv-first-line-fixed-column fn-lpv-initial-name-run-record
                 fn-nlv-run-phase-is-control-run-phase)))))

(local (defthm fn-lpv-make-field-value-by-definition
  (equal (fn-article-field-unfolded-value (fn-article-make-field raw name value)) value)
  :hints (("Goal" :in-theory (enable fn-article-make-field fn-article-field-unfolded-value)))))
(local (defthm fn-lpv-make-field-present-by-definition
  (fn-article-make-field raw name value)
  :hints (("Goal" :in-theory (enable fn-article-make-field)))))

(defthm fn-lpv-header-equiv-new-field-line
  (implies (and (fn-lpv-header-equiv s source current columns h pin)
                (fn-article-field-closedp current)
                (fn-article-namep name) (fn-article-header-bytes-p value)
                (or (not (consp value)) (fn-article-wspp (car value)))
                (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*))
           (let ((line (append name (cons 58 (append value '(13 10))))))
             (fn-lpv-header-equiv
              (fn-nlv-run line s (len source) h pin) (append source line)
              (fn-article-make-field (list (append name (cons 58 value)))
                                     (fn-article-ascii-downcase name) value)
              (fn-novlp-add-field columns current *fn-novlp-names*) h pin)))
  :hints (("Goal"
           :use (fn-lpv-header-equiv-old-closed
                 fn-lpv-header-equiv-close-columns
                 (:instance fn-lpc-close-fields-preserves-bounds (pos (len source)))
                 (:instance fn-lpv-columns-equiv-stable-under-extension
                    (spans (fn-lpc-close-fields s h pin))
                    (columns (fn-novlp-add-field columns current *fn-novlp-names*))
                    (rest (append name (cons 58 (append value '(13 10))))))
                 (:instance fn-lpv-run-preserves-header-bounds
                    (bytes (append name (cons 58 (append value '(13 10))))) (pos (len source)))
                 (:instance fn-lpv-valid-new-field-line-start (pos (len source)))
                 (:instance fn-lpv-new-field-line-value-run (bytes value))
                 (:instance fn-lpv-new-field-line-span-is-unfolded-value (bytes value))
                 (:instance fn-lpv-new-field-line-selected-name (bytes value) (pos (len source)))
                 (:instance fn-lpv-new-field-line-current-present (bytes value) (pos (len source))))
           :in-theory
           (e/d (fn-lpv-header-equiv fn-lpc-header-bounds-p)
                (fn-lpc-at fn-nlv-run fn-lpc-header-byte fn-lpv-columns-equiv
                 fn-lpv-selectedp fn-lpv-value-state-p fn-lpc-spans-bound-p
                 fn-lpv-slice fn-nov-scrub fn-nov-value-content fn-novlp-add-field
                 fn-article-namep fn-article-header-bytes-p fn-article-wspp fn-article-has-vcharp
                 fn-article-make-field fn-article-field-unfolded-value fn-article-field-closedp
                 fn-article-ascii-downcase fn-lpc-close-fields fn-lpc-name-key fn-lpc-names-scan
                 binary-append len fn-nlv-run-phase-is-control-run-phase fn-nlv-run-append
                 fn-lpv-content-append fn-lpv-unfolded-append-normalization
                 fn-lpv-header-equiv-old-closed fn-lpv-header-equiv-close-columns
                 fn-lpc-close-fields-preserves-bounds fn-lpv-columns-equiv-stable-under-extension
                 fn-lpv-run-preserves-header-bounds fn-lpv-valid-new-field-line-start
                 fn-lpv-new-field-line-value-run fn-lpv-new-field-line-span-is-unfolded-value
                 fn-lpv-new-field-line-selected-name fn-lpv-new-field-line-current-present)))))

(defthm fn-lpv-terminal-byte-keeps-columns
  (implies (member-equal (fn-lpc-at 0 s) '(:body :body-cr :bad))
           (and (member-equal (fn-lpc-at 0 (fn-lpc-header-byte s byte pos h pin))
                              '(:body :body-cr :bad))
                (equal (fn-lpc-at 8 (fn-lpc-header-byte s byte pos h pin)) (fn-lpc-at 8 s))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-lpc-header-bad)
                (fn-lpc-at fn-lpc-put fn-lpc-value-byte fn-lpc-close-fields)))))

(defthm fn-lpv-terminal-run-keeps-columns
  (implies (member-equal (fn-lpc-at 0 s) '(:body :body-cr :bad))
           (equal (fn-lpc-at 8 (fn-nlv-run bytes s pos h pin)) (fn-lpc-at 8 s)))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :in-theory (e/d (fn-nlv-run)
                           (fn-lpc-header-byte fn-lpc-at fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-lpv-separator-closes-columns
  (implies (and (equal (fn-lpc-at 0 s) :start)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)))
           (and (equal (fn-lpc-at 0 (fn-nlv-run '(13 10) s pos h pin)) :body)
                (equal (fn-lpc-at 8 (fn-nlv-run '(13 10) s pos h pin))
                       (fn-lpc-close-fields s h pin))))
  :hints (("Goal" :in-theory
           (e/d (fn-nlv-run fn-lpc-header-byte fn-lpc-at fn-lpc-close-fields)
                (fn-lpc-put fn-lpc-span fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-lpv-separator-body-closes-columns
  (implies (and (equal (fn-lpc-at 0 s) :start)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)))
           (equal (fn-lpc-at 8 (fn-nlv-run (cons 13 (cons 10 body)) s pos h pin))
                  (fn-lpc-close-fields s h pin)))
  :hints (("Goal"
           :use ((:instance fn-lpv-separator-closes-columns))
           :expand ((fn-nlv-run (cons 13 (cons 10 body)) s pos h pin)
                    (fn-nlv-run (cons 10 body) (fn-lpc-header-byte s 13 pos h pin)
                                (+ 1 pos) h pin)
                    (fn-nlv-run '(13 10) s pos h pin)
                    (fn-nlv-run '(10) (fn-lpc-header-byte s 13 pos h pin)
                                (+ 1 pos) h pin)
                    (:free (s pos) (fn-nlv-run nil s pos h pin)))
           :in-theory
           (disable fn-nlv-run fn-lpc-header-byte fn-lpc-at fn-lpc-close-fields fn-nlv-run-append
                    fn-lpv-separator-closes-columns fn-nlv-run-phase-is-control-run-phase))))

(defthm fn-lpv-header-equiv-separator-body
  (implies (and (fn-lpv-header-equiv s source current columns h pin)
                (fn-article-field-closedp current))
           (fn-lpv-columns-equiv
            (fn-lpc-at 8 (fn-nlv-run (cons 13 (cons 10 body)) s (len source) h pin))
            (fn-novlp-add-field columns current *fn-novlp-names*)
            (append source (cons 13 (cons 10 body)))))
  :hints (("Goal"
           :use (fn-lpv-header-equiv-old-closed fn-lpv-header-equiv-close-columns
                 (:instance fn-lpc-close-fields-preserves-bounds (pos (len source)))
                 (:instance fn-lpv-columns-equiv-stable-under-extension
                    (spans (fn-lpc-close-fields s h pin))
                    (columns (fn-novlp-add-field columns current *fn-novlp-names*))
                    (rest (cons 13 (cons 10 body)))))
           :in-theory
           (e/d (fn-lpv-header-equiv)
                (fn-lpc-at fn-nlv-run fn-lpc-close-fields fn-lpv-columns-equiv
                 fn-lpv-value-state-p fn-lpv-selectedp fn-lpc-header-bounds-p
                 fn-article-field-closedp fn-article-field-unfolded-value
                 fn-lpv-slice fn-nov-scrub fn-nov-value-content fn-novlp-add-field
                 fn-lpv-header-equiv-old-closed fn-lpv-header-equiv-close-columns
                 fn-lpc-close-fields-preserves-bounds fn-lpv-columns-equiv-stable-under-extension
                 fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-lpv-header-equiv-actual-new-field
  (implies (and (fn-lpv-header-equiv s source current columns h pin)
                (fn-article-field-closedp current)
                (true-listp line) (fn-article-line-okp (fn-article-new-field line))
                (<= (len line) *fn-article-max-line-octets*))
           (fn-lpv-header-equiv
            (fn-nlv-run (append line '(13 10)) s (len source) h pin)
            (append source (append line '(13 10)))
            (fn-article-line-value (fn-article-new-field line))
            (fn-novlp-add-field columns current *fn-novlp-names*) h pin))
  :hints (("Goal"
           :use ((:instance fn-nlpc-split-partition (prefix nil))
                 (:instance fn-lpv-header-equiv-new-field-line
                    (name (fn-article-line-value (fn-article-split-colon-aux line nil)))
                    (value (fn-article-line-rest (fn-article-split-colon-aux line nil)))))
           :in-theory
           (e/d (fn-article-new-field fn-article-line-okp fn-article-line-value
                 fn-article-line-rest fn-article-error)
                (fn-lpv-header-equiv-new-field-line fn-nlpc-split-partition
                 fn-lpv-header-equiv fn-nlv-run fn-nlv-run-append
                 fn-article-split-colon-aux fn-nlv-new-field-is-name-tail
                 fn-article-namep fn-article-header-bytes-p fn-article-wspp
                 fn-article-make-field fn-article-ascii-downcase fn-novlp-add-field
                 fn-article-field-closedp fn-nlv-run-phase-is-control-run-phase)))))

(defun fn-lpv-span-values (spans source)
  (declare (xargs :guard t :verify-guards nil))
  (list (car (fn-lpv-span-column (fn-lpc-at 0 spans) source))
        (car (fn-lpv-span-column (fn-lpc-at 1 spans) source))
        (car (fn-lpv-span-column (fn-lpc-at 2 spans) source))
        (car (fn-lpv-span-column (fn-lpc-at 3 spans) source))
        (car (fn-lpv-span-column (fn-lpc-at 4 spans) source))))

(defthm fn-lpv-equivalent-closed-columns-normalize
  (implies (fn-lpv-columns-equiv spans (fn-novlp-add-field columns current *fn-novlp-names*) source)
           (equal (fn-lpv-span-values spans source)
                  (fn-novlp-normalize (fn-novlp-add-field columns current *fn-novlp-names*))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpv-columns-equiv fn-lpv-span-values fn-novlp-normalize
                 fn-novlp-add-field fn-lpv-column fn-lpc-at)
                (fn-lpv-span-column fn-article-field-name-equalp fn-article-field-unfolded-value
                 fn-nov-scrub fn-nov-value-content)))))

(defthm fn-lpv-separator-body-normalized-values
  (implies (and (fn-lpv-header-equiv s source current columns h pin)
                (fn-article-field-closedp current))
           (equal (fn-lpv-span-values
                    (fn-lpc-at 8 (fn-nlv-run (cons 13 (cons 10 body)) s (len source) h pin))
                    (append source (cons 13 (cons 10 body))))
                  (fn-novlp-normalize (fn-novlp-add-field columns current *fn-novlp-names*))))
  :hints (("Goal"
           :use (fn-lpv-header-equiv-separator-body
                 (:instance fn-lpv-equivalent-closed-columns-normalize
                   (spans (fn-lpc-at 8 (fn-nlv-run (cons 13 (cons 10 body)) s (len source) h pin)))
                   (source (append source (cons 13 (cons 10 body))))))
           :in-theory (disable fn-lpv-header-equiv fn-lpc-at fn-nlv-run fn-lpv-span-values
                                fn-lpv-columns-equiv fn-novlp-normalize fn-novlp-add-field
                                fn-lpv-header-equiv-separator-body
                                fn-lpv-equivalent-closed-columns-normalize
                                fn-article-field-closedp fn-nlv-run-phase-is-control-run-phase))))

; Proof-only induction follows the actual parser's physical line split and
; carries the consumed source prefix and actual byte state. It emits no data.
(local
 (defun fn-lpv-header-ind (octets lines-left header-bytes nfields s source current columns h pin)
   (declare (xargs :measure (nfix lines-left) :verify-guards nil))
   (if (zp lines-left) (list header-bytes nfields s source current columns h pin)
     (let* ((next (fn-article-next-line octets))
            (line (fn-article-line-value next))
            (rest (fn-article-line-rest next)))
       (if (or (not (fn-article-line-okp next)) (not line))
           (list header-bytes nfields s source current columns h pin)
         (fn-lpv-header-ind
          rest (1- lines-left) (+ header-bytes (len line) 2)
          (if (fn-article-wspp (car line)) nfields
            (if current (+ 1 (nfix nfields)) nfields))
          (fn-nlv-run (append line '(13 10)) s (len source) h pin)
          (append source (append line '(13 10)))
          (if (fn-article-wspp (car line)) (fn-article-add-fold current line)
            (fn-article-line-value (fn-article-new-field line)))
          (if (fn-article-wspp (car line)) columns
            (fn-novlp-add-field columns current *fn-novlp-names*)) h pin))))))

(defthm fn-lpv-successful-header-values
  (implies (and (fn-lpv-header-equiv s source current columns h pin)
                (fn-article-result-okp
                 (fn-novlp-parse-lines octets limits lines-left header-bytes nfields
                                       columns current *fn-novlp-names*)))
           (equal (fn-lpv-span-values
                    (fn-lpc-at 8 (fn-nlv-run octets s (len source) h pin))
                    (append source octets))
                  (cadr (fn-novlp-parse-lines octets limits lines-left header-bytes nfields
                                             columns current *fn-novlp-names*))))
  :hints (("Goal"
           :expand ((fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*))
           :induct (fn-lpv-header-ind octets lines-left header-bytes nfields
                                      s source current columns h pin)
           :in-theory
           (e/d (fn-lpv-header-ind fn-article-result-okp fn-article-line-okp fn-article-error)
                (fn-novlp-parse-lines fn-lpv-header-equiv fn-lpv-span-values fn-nlv-run fn-lpc-at
                 fn-article-next-line fn-article-line-value
                 fn-article-line-rest fn-article-field-closedp fn-article-fold-linep
                 fn-article-body-crlfp fn-article-wspp fn-article-new-field fn-article-add-fold
                 fn-article-limit-octets fn-article-limit-fields fn-novlp-add-field
                 fn-novlp-normalize binary-append len fn-nlv-run-append
                 fn-nlv-run-phase-is-control-run-phase fn-nlv-new-field-is-name-tail fn-nlv-physicalp
                 fn-nlpc-next-line-partition fn-lpv-header-equiv-fold-line
                 fn-lpv-header-equiv-actual-new-field)))
          ("Subgoal *1/3" :expand ((:free (current) (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*)))
                            :use (fn-nlpc-next-line-partition
                                (:instance fn-lpv-header-equiv-fold-line (line (fn-article-line-value (fn-article-next-line octets))))
                                (:instance fn-lpv-header-equiv-actual-new-field (line (fn-article-line-value (fn-article-next-line octets))))
                                (:instance fn-nlv-run-append
                                  (a (append (fn-article-line-value (fn-article-next-line octets)) '(13 10)))
                                  (b (fn-article-line-rest (fn-article-next-line octets)))
                                  (pos (len source)))))
          ("Subgoal *1/2" :expand ((fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*))
                            :use (fn-nlpc-next-line-partition))))

(defthm fn-lpv-complete-successful-header-values
  (implies (fn-article-result-okp (fn-novlp-parse bytes))
           (equal (fn-lpv-span-values
                    (fn-lpc-at 8 (fn-nlv-run bytes (fn-lpc-header-begin) 0 h pin)) bytes)
                  (cadr (fn-novlp-parse bytes))))
  :hints (("Goal"
           :use (fn-lpv-header-begin-equiv
                 (:instance fn-lpv-successful-header-values
                    (octets bytes) (s (fn-lpc-header-begin)) (source nil) (current nil)
                    (columns (fn-novlp-columns nil *fn-novlp-names*))
                    (limits *fn-article-ceiling-limits*)
                    (lines-left (1+ (fn-article-limit-lines *fn-article-ceiling-limits*)))
                    (header-bytes 0) (nfields 0)))
           :in-theory
           (e/d (fn-novlp-parse fn-novlp-parse-under fn-article-result-okp fn-article-error)
                (fn-lpv-header-begin-equiv fn-lpv-successful-header-values fn-lpv-header-equiv fn-lpv-span-values
                 fn-lpc-at fn-nlv-run fn-lpc-header-begin fn-novlp-columns
                 fn-novlp-parse-lines fn-novlp-parse-is-parser-projection
                 fn-novlp-parse-under-is-parser-projection
                 fn-cbor-at-mostp fn-cbor-octet-listp)))))

(defthm fn-lpv-complete-values-are-actual-overview-content
  (implies (fn-article-result-okp (fn-article-parse bytes))
           (let ((view (fn-article-result-article (fn-article-parse bytes))))
             (equal (fn-lpv-span-values
                      (fn-lpc-at 8 (fn-nlv-run bytes (fn-lpc-header-begin) 0 h pin)) bytes)
                    (list (fn-nov-header-content view *fn-nov-subject-name*)
                          (fn-nov-header-content view *fn-nov-from-name*)
                          (fn-nov-header-content view *fn-nov-date-name*)
                          (fn-nov-header-content view *fn-nov-message-id-name*)
                          (fn-nov-header-content view *fn-nov-references-name*)))))
  :hints (("Goal"
           :use (fn-lpv-complete-successful-header-values
                 (:instance fn-novlp-parse-is-parser-projection (octets bytes)))
           :in-theory
           (e/d (fn-novlp-result fn-article-result-okp)
                (fn-lpv-span-values fn-lpc-at fn-nlv-run fn-lpc-header-begin
                 fn-article-parse fn-article-result-article fn-article-fields fn-nov-header-content
                 fn-novlp-normalize fn-novlp-columns fn-novlp-parse
                 fn-lpv-complete-successful-header-values fn-novlp-parse-is-parser-projection)))))
