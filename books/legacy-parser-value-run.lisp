; Actual header-byte runs preserve normalized source spans.
(in-package "ACL2")
(include-book "legacy-parser-values")
(include-book "legacy-parser-validity")

(defthm fn-lpv-value-byte-phase-and-length-by-definition
  (implies (fn-article-header-bytep byte)
           (and (equal (fn-lpc-at 0 (fn-lpc-value-byte s byte pos)) :value)
                (equal (fn-lpc-at 1 (fn-lpc-value-byte s byte pos))
                       (+ 1 (nfix (fn-lpc-at 1 s))))))
  :hints (("Goal" :in-theory (e/d (fn-lpc-value-byte fn-lpc-at) (fn-nlv-run-phase-is-control-run-phase)))))

(local (defthm fn-lpv-append-associative
  (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fn-lpv-append-atom
  (implies (not (consp a)) (equal (append a b) b))))
(local (defthm fn-lpv-append-cons
  (equal (append (cons a b) c) (cons a (append b c)))))
(local (defthm fn-lpv-append-nil-right
  (implies (true-listp a) (equal (append a nil) a))))

(local (defun fn-lpv-run-ind (bytes s source value h pin)
  (if (consp bytes)
      (fn-lpv-run-ind (cdr bytes)
                      (fn-lpc-header-byte s (car bytes) (len source) h pin)
                      (append source (list (car bytes)))
                      (append value (list (car bytes))) h pin)
    (list s source value h pin))))

(local (defthm fn-lpv-len-consp
  (implies (consp bytes) (equal (len bytes) (+ 1 (len (cdr bytes)))))))

(defthm fn-lpv-value-state-list-shape
  (implies (fn-lpv-value-state-p s source value)
           (and (true-listp source) (true-listp value)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-lpv-value-state-p) (fn-nlv-run-phase-is-control-run-phase)))))

(local (defthm fn-lpv-run-atom
  (implies (not (consp bytes)) (equal (fn-nlv-run bytes s pos h pin) s))
  :hints (("Goal" :in-theory (e/d (fn-nlv-run) (fn-nlv-run-phase-is-control-run-phase))))))

(defthm fn-lpv-run-value-refines-unfolded-append
  (implies (and (fn-lpv-value-state-p s source value)
                (equal (fn-lpc-at 0 s) :value)
                (natp (fn-lpc-at 1 s))
                (fn-article-header-bytes-p bytes)
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*))
           (fn-lpv-value-state-p
            (fn-nlv-run bytes s (len source) h pin)
            (append source bytes) (append value bytes)))
  :hints (("Goal" :induct (fn-lpv-run-ind bytes s source value h pin)
           :expand ((:free (s pos) (fn-nlv-run bytes s pos h pin)))
           :in-theory
           (e/d (fn-article-header-bytes-p nfix)
                (fn-nlv-run-phase-is-control-run-phase fn-lpv-value-state-p fn-lpc-header-byte fn-lpc-value-byte
                 fn-lpc-at fn-nlv-run binary-append len
                 fn-article-header-bytep)))))

(defthm fn-lpv-run-fold-refines-unfolded-append
  (implies (and (fn-lpv-value-state-p s source value)
                (equal (fn-lpc-at 0 s) :start)
                (equal (fn-lpc-at 1 s) 0) (fn-lpc-at 2 s)
                (fn-article-header-bytes-p bytes) (fn-article-wspp (car bytes))
                (<= (len bytes) *fn-article-max-line-octets*))
           (fn-lpv-value-state-p
            (fn-nlv-run bytes s (len source) h pin)
            (append source bytes) (append value bytes)))
  :hints (("Goal"
           :use ((:instance fn-lpv-run-value-refines-unfolded-append
                    (bytes (cdr bytes))
                    (s (fn-lpc-header-byte s (car bytes) (len source) h pin))
                    (source (append source (list (car bytes))))
                    (value (append value (list (car bytes))))))
           :expand ((fn-nlv-run bytes s (len source) h pin))
           :in-theory
           (e/d (fn-article-header-bytes-p fn-article-wspp nfix)
                (fn-nlv-run-phase-is-control-run-phase fn-lpv-value-state-p fn-lpc-header-byte fn-lpc-value-byte
                 fn-lpc-at fn-lpc-put fn-nlv-run binary-append len
                 fn-article-header-bytep fn-lpv-run-value-refines-unfolded-append)))))

(defthm fn-lpv-run-framing-keeps-value
  (implies (fn-lpv-value-state-p s source value)
           (fn-lpv-value-state-p
            (fn-nlv-run '(13 10) s (len source) h pin)
            (append source '(13 10)) value))
  :hints (("Goal" :expand ((:free (s pos) (fn-nlv-run '(13 10) s pos h pin))
                           (:free (s pos) (fn-nlv-run '(10) s pos h pin))
                           (:free (s pos) (fn-nlv-run nil s pos h pin)))
           :in-theory (disable fn-nlv-run-phase-is-control-run-phase fn-lpv-value-state-p fn-nlv-run fn-lpc-header-byte
                               binary-append len))))

(defthm fn-lpv-run-fold-line-refines-unfolded-append
  (implies (and (fn-lpv-value-state-p s source value)
                (equal (fn-lpc-at 0 s) :start)
                (equal (fn-lpc-at 1 s) 0) (fn-lpc-at 2 s)
                (fn-article-header-bytes-p bytes) (fn-article-wspp (car bytes))
                (<= (len bytes) *fn-article-max-line-octets*))
           (fn-lpv-value-state-p
            (fn-nlv-run (append bytes '(13 10)) s (len source) h pin)
            (append source (append bytes '(13 10))) (append value bytes)))
  :hints (("Goal"
           :use ((:instance fn-lpv-run-framing-keeps-value
                            (s (fn-nlv-run bytes s (len source) h pin))
                            (source (append source bytes))
                            (value (append value bytes))))
           :in-theory (disable fn-nlv-run-phase-is-control-run-phase fn-lpv-value-state-p fn-nlv-run fn-lpc-header-byte
                               fn-lpc-at binary-append len
                               fn-article-header-bytes-p fn-article-wspp
                               fn-lpv-run-framing-keeps-value))))

(defthm fn-lpv-header-name-step-by-definition
  (implies (and (equal (fn-lpc-at 0 s) :name)
                (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
                (fn-article-ftextp byte))
           (equal (fn-lpc-header-byte s byte pos h pin)
                  (fn-lpc-put 7 (fn-lpc-name-step (fn-lpc-at 7 s) byte)
                   (fn-lpc-put 1 (+ 1 (nfix (fn-lpc-at 1 s))) s))))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-article-ftextp)
                (fn-nlv-run-phase-is-control-run-phase fn-lpc-at fn-lpc-put fn-lpc-name-step fn-lpc-name-key
                 fn-lpc-close-fields fn-lpc-value-byte fn-lpc-header-bad)))))

(defthm fn-lpv-name-run-preserves-metadata
  (implies (and (equal (fn-lpc-at 0 s) :name)
                (natp (fn-lpc-at 1 s)) (fn-article-ftext-listp bytes)
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*)
                (natp k) (not (equal k 1)) (not (equal k 7)))
           (let ((out (fn-nlv-run bytes s pos h pin)))
             (and (equal (fn-lpc-at k out) (fn-lpc-at k s))
                  (equal (fn-lpc-at 1 out) (+ (fn-lpc-at 1 s) (len bytes)))
                  (equal (fn-lpc-at 7 out)
                         (fn-lpc-names-scan (fn-lpc-at 7 s) bytes)))))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :expand ((fn-nlv-run bytes s pos h pin))
           :in-theory
           (e/d (fn-article-ftext-listp fn-lpc-names-scan nfix (:induction fn-nlv-run))
                (fn-nlv-run-phase-is-control-run-phase (:definition fn-nlv-run) fn-lpc-header-byte fn-lpc-put fn-lpc-at
                 fn-lpc-name-step fn-article-ftextp len)))))

(local (defun fn-lpv-name-record-ind (bytes n candidates pos)
  (if (consp bytes)
      (fn-lpv-name-record-ind (cdr bytes) (+ 1 n)
                              (fn-lpc-name-step candidates (car bytes)) (+ 1 pos))
    (list n candidates pos))))

(defthm fn-lpv-name-run-record
  (implies (and (natp n) (fn-article-ftext-listp bytes)
                (<= (+ n (len bytes)) *fn-article-max-line-octets*))
           (equal
            (fn-nlv-run bytes (list :name n t nil 0 0 nil candidates fields nil :plain)
                        pos h pin)
            (list :name (+ n (len bytes)) t nil 0 0 nil
                  (fn-lpc-names-scan candidates bytes) fields nil :plain)))
  :hints (("Goal" :induct (fn-lpv-name-record-ind bytes n candidates pos)
           :expand ((:free (s) (fn-nlv-run bytes s pos h pin)))
           :in-theory
           (e/d (fn-article-ftext-listp fn-lpc-names-scan fn-lpc-at fn-lpc-put nfix)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-header-byte fn-lpc-name-step fn-article-ftextp len)))))

(defthm fn-lpv-initial-name-run-record
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name)
                (<= (len name) *fn-article-max-line-octets*))
           (equal
            (fn-nlv-run name s pos h pin)
            (list :name (len name) t nil 0 0 nil
                  (fn-lpc-names-scan *fn-lpc-names* name)
                  (fn-lpc-close-fields s h pin) nil :plain)))
  :hints (("Goal"
           :expand ((fn-nlv-run name s pos h pin)
                    (fn-lpc-names-scan *fn-lpc-names* name))
           :in-theory
           (e/d (fn-lpc-header-byte fn-article-namep fn-article-ftext-listp
                 fn-article-ftextp fn-article-wspp)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-at fn-lpc-put fn-lpc-name-step fn-lpc-name-key
                 fn-lpc-close-fields fn-lpc-names-scan len)))))

(defthm fn-lpv-run-first-refines-unfolded-append
  (implies (and (fn-lpv-value-state-p s source value)
                (equal (fn-lpc-at 0 s) :first) (natp (fn-lpc-at 1 s))
                (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*))
           (fn-lpv-value-state-p
            (fn-nlv-run bytes s (len source) h pin)
            (append source bytes) (append value bytes)))
  :hints (("Goal" :cases ((consp bytes))
           :use ((:instance fn-lpv-run-value-refines-unfolded-append
                    (bytes (cdr bytes))
                    (s (fn-lpc-header-byte s (car bytes) (len source) h pin))
                    (source (append source (list (car bytes))))
                    (value (append value (list (car bytes))))))
           :expand ((fn-nlv-run bytes s (len source) h pin))
           :in-theory
           (e/d (fn-article-header-bytes-p fn-article-wspp nfix)
                (fn-nlv-run-phase-is-control-run-phase fn-lpv-value-state-p fn-lpc-header-byte fn-lpc-value-byte
                 fn-lpc-at fn-lpc-put fn-nlv-run binary-append len
                 fn-article-header-bytep fn-lpv-run-value-refines-unfolded-append)))))

(defthm fn-lpv-name-colon-run-record
  (implies (and (natp pos)
                (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name)
                (< (len name) *fn-article-max-line-octets*))
           (equal
            (fn-nlv-run (append name '(58)) s pos h pin)
            (list :first (+ 1 (len name)) t nil 0 0
                  (fn-lpc-name-key (fn-lpc-names-scan *fn-lpc-names* name))
                  (fn-lpc-names-scan *fn-lpc-names* name)
                  (fn-lpc-close-fields s h pin) nil :plain)))
  :hints (("Goal"
           :expand ((:free (s pos) (fn-nlv-run '(58) s pos h pin)))
           :in-theory
           (e/d (fn-lpc-header-byte fn-lpc-at fn-lpc-put)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-name-key fn-lpc-name-step fn-lpc-names-scan
                 fn-lpc-close-fields fn-article-namep len)))))

(defthm fn-lpv-new-field-value-run
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name) (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (len name) 1 (len bytes)) *fn-article-max-line-octets*))
           (fn-lpv-value-state-p
            (fn-nlv-run (append name (cons 58 bytes)) s (len source) h pin)
            (append source (append name (cons 58 bytes))) bytes))
  :hints (("Goal"
           :use ((:instance fn-lpv-run-first-refines-unfolded-append
                    (s (fn-nlv-run (append name '(58)) s (len source) h pin))
                    (source (append source (append name '(58)))) (value nil))
                 (:instance fn-nlv-run-append (a (append name '(58))) (b bytes)
                            (pos (len source))))
           :in-theory
           (e/d (fn-lpc-at fn-lpv-value-state-p)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-header-byte fn-lpc-name-key fn-lpc-names-scan
                 fn-lpc-close-fields fn-lpv-slice fn-nov-scrub fn-nov-value-content
                 fn-article-header-bytes-p fn-article-namep fn-article-has-vcharp
                 fn-article-body-crlfp fn-article-wspp binary-append len
                 fn-nlv-run-append fn-lpv-run-first-refines-unfolded-append)))))

(defthm fn-lpv-new-field-line-value-run
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name) (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (len name) 1 (len bytes)) *fn-article-max-line-octets*))
           (fn-lpv-value-state-p
            (fn-nlv-run (append name (cons 58 (append bytes '(13 10))))
                        s (len source) h pin)
            (append source (append name (cons 58 (append bytes '(13 10))))) bytes))
  :hints (("Goal"
           :use ((:instance fn-lpv-run-framing-keeps-value
                    (s (fn-nlv-run (append name (cons 58 bytes)) s (len source) h pin))
                    (source (append source (append name (cons 58 bytes)))) (value bytes))
                 fn-lpv-new-field-value-run
                 (:instance fn-nlv-run-append (a (append name (cons 58 bytes)))
                            (b '(13 10)) (pos (len source))))
           :in-theory
           (disable fn-nlv-run-phase-is-control-run-phase fn-lpv-value-state-p fn-nlv-run fn-lpc-header-byte fn-lpc-at
                    fn-article-namep fn-article-header-bytes-p fn-article-wspp
                    binary-append len fn-lpv-run-framing-keeps-value
                    fn-nlv-run-append fn-lpv-new-field-value-run
                    fn-lpv-initial-name-run-record fn-lpv-name-colon-run-record
                    fn-lpc-names-scan fn-lpc-close-fields))))

(defthm fn-lpv-value-byte-fixed-column-by-definition
  (implies (and (member-equal k '(2 5 6 7 8)) (fn-article-header-bytep byte))
           (equal (fn-lpc-at k (fn-lpc-value-byte s byte pos)) (fn-lpc-at k s)))
  :hints (("Goal" :in-theory (e/d (fn-lpc-at fn-lpc-value-byte) (fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-lpv-value-run-fixed-column
  (implies (and (equal (fn-lpc-at 0 s) :value) (natp (fn-lpc-at 1 s))
                (fn-article-header-bytes-p bytes)
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*)
                (member-equal k '(2 5 6 7 8)))
           (equal (fn-lpc-at k (fn-nlv-run bytes s pos h pin)) (fn-lpc-at k s)))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :expand ((fn-nlv-run bytes s pos h pin))
           :in-theory
           (e/d (fn-article-header-bytes-p nfix (:induction fn-nlv-run))
                (fn-nlv-run-phase-is-control-run-phase (:definition fn-nlv-run) fn-lpc-header-byte fn-lpc-value-byte
                 fn-lpc-at fn-article-header-bytep len)))))

(defthm fn-lpv-first-run-fixed-column
  (implies (and (equal (fn-lpc-at 0 s) :first) (natp (fn-lpc-at 1 s))
                (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*)
                (member-equal k '(2 5 6 7 8)))
           (equal (fn-lpc-at k (fn-nlv-run bytes s pos h pin)) (fn-lpc-at k s)))
  :hints (("Goal" :cases ((consp bytes))
           :expand ((fn-nlv-run bytes s pos h pin))
           :in-theory
           (e/d (fn-article-header-bytes-p fn-article-wspp nfix)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-header-byte fn-lpc-value-byte fn-lpc-at
                 fn-article-header-bytep len)))))

(defthm fn-lpv-fold-run-fixed-column
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (fn-lpc-at 2 s) (fn-article-header-bytes-p bytes)
                (fn-article-wspp (car bytes))
                (<= (len bytes) *fn-article-max-line-octets*)
                (member-equal k '(2 5 6 7 8)))
           (equal (fn-lpc-at k (fn-nlv-run bytes s pos h pin)) (fn-lpc-at k s)))
  :hints (("Goal" :expand ((fn-nlv-run bytes s pos h pin))
           :in-theory
           (e/d (fn-article-header-bytes-p fn-article-wspp nfix)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-header-byte fn-lpc-value-byte fn-lpc-at fn-lpc-put
                 fn-article-header-bytep len)))))

(defthm fn-lpv-value-run-control
  (implies (and (equal (fn-lpc-at 0 s) :value) (natp (fn-lpc-at 1 s))
                (fn-article-header-bytes-p bytes)
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*))
           (equal (fn-nlv-control (fn-nlv-run bytes s pos h pin))
                  (fn-nlv-value-final bytes (fn-lpc-at 1 s)
                                      (and (fn-lpc-at 2 s) t)
                                      (and (fn-lpc-at 3 s) t) (fn-lpc-at 10 s))))
  :hints (("Goal"
           :use ((:instance fn-nlv-value-run-valid (n (fn-lpc-at 1 s))
                    (current (and (fn-lpc-at 2 s) t))
                    (visible (and (fn-lpc-at 3 s) t)) (mode (fn-lpc-at 10 s))))
           :in-theory
           (e/d (fn-nlv-control)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-nlv-control-run fn-nlv-value-final fn-lpc-at
                 fn-article-header-bytes-p len)))))

(defthm fn-lpv-first-run-control
  (implies (and (equal (fn-lpc-at 0 s) :first) (natp (fn-lpc-at 1 s))
                (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*))
           (equal (fn-nlv-control (fn-nlv-run bytes s pos h pin))
                  (if (consp bytes)
                      (fn-nlv-value-final bytes (fn-lpc-at 1 s)
                                          (and (fn-lpc-at 2 s) t)
                                          (and (fn-lpc-at 3 s) t) (fn-lpc-at 10 s))
                    (fn-nlv-control s))))
  :hints (("Goal" :expand ((:free (c) (fn-nlv-control-run nil c)))
           :use ((:instance fn-nlv-initial-value-control (n (fn-lpc-at 1 s))
                    (current (and (fn-lpc-at 2 s) t))
                    (visible (and (fn-lpc-at 3 s) t)) (mode (fn-lpc-at 10 s))))
           :in-theory
           (e/d (fn-nlv-control)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-nlv-control-run fn-nlv-value-final fn-lpc-at
                 fn-article-header-bytes-p fn-article-wspp len)))))

(defthm fn-lpv-control-at-by-definition
  (and (equal (fn-lpc-at 0 (fn-nlv-control s)) (fn-lpc-at 0 s))
       (equal (fn-lpc-at 1 (fn-nlv-control s)) (nfix (fn-lpc-at 1 s)))
       (equal (fn-lpc-at 3 (fn-nlv-control s)) (and (fn-lpc-at 3 s) t))
       (equal (fn-lpc-at 4 (fn-nlv-control s)) (fn-lpc-at 10 s)))
  :hints (("Goal" :in-theory (e/d (fn-nlv-control fn-lpc-at) (fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-lpv-first-run-end-phase
  (implies (and (equal (fn-lpc-at 0 s) :first) (natp (fn-lpc-at 1 s))
                (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*))
           (and (equal (fn-lpc-at 0 (fn-nlv-run bytes s pos h pin))
                       (if (consp bytes) :value :first))
                (equal (fn-lpc-at 10 (fn-nlv-run bytes s pos h pin))
                       (if (and (equal (fn-lpc-at 10 s) :fold-empty)
                                (fn-article-has-vcharp bytes))
                           :fold-visible (fn-lpc-at 10 s)))))
  :hints (("Goal"
           :use (fn-lpv-first-run-control
                 (:instance fn-lpv-control-at-by-definition (s (fn-nlv-run bytes s pos h pin))))
           :in-theory
           (e/d (fn-nlv-value-final fn-lpc-at)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-nlv-control fn-article-header-bytes-p
                 fn-article-has-vcharp fn-article-wspp len
                 fn-lpv-first-run-control fn-lpv-control-at-by-definition
                 fn-nlv-control-run-is-actual-header-run fn-nlv-control-run
                 fn-lpc-close-fields fn-lpc-names-scan fn-lpc-name-key)))))

(defthm fn-lpv-value-framing-fixed-column-by-definition
  (implies (and (member-eq (fn-lpc-at 0 s) '(:first :value))
                (member-equal k '(2 6 7 8)))
           (equal (fn-lpc-at k
                    (fn-lpc-header-byte (fn-lpc-header-byte s 13 pos h pin)
                                        10 (+ 1 pos) h pin))
                  (fn-lpc-at k s)))
  :hints (("Goal" :in-theory
           (e/d (fn-lpc-header-byte fn-lpc-header-bad)
                (fn-nlv-run-phase-is-control-run-phase fn-lpc-at fn-lpc-put fn-lpc-close-fields fn-lpc-value-byte
                 fn-lpc-name-step fn-lpc-name-key)))))

(defthm fn-lpv-first-line-fixed-column
  (implies (and (natp pos)
                (equal (fn-lpc-at 0 s) :first) (natp (fn-lpc-at 1 s))
                (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*)
                (member-equal k '(2 6 7 8)))
           (equal (fn-lpc-at k (fn-nlv-run (append bytes '(13 10)) s pos h pin))
                  (fn-lpc-at k s)))
  :hints (("Goal" :expand ((:free (s pos) (fn-nlv-run '(13 10) s pos h pin))
                           (:free (s pos) (fn-nlv-run '(10) s pos h pin)))
           :in-theory
           (disable fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-header-byte fn-lpc-value-byte fn-lpc-at
                    fn-lpc-put fn-article-header-bytes-p fn-article-wspp
                    fn-article-has-vcharp binary-append len fn-nlv-control-run
                    fn-nlv-control-run-is-actual-header-run))))

(defthm fn-lpv-new-field-line-selected-name
  (implies (and (natp pos)
                (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name) (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (len name) 1 (len bytes)) *fn-article-max-line-octets*))
           (let ((out (fn-nlv-run (append name (cons 58 (append bytes '(13 10))))
                                  s pos h pin)))
             (and (equal (fn-lpc-at 6 out)
                         (fn-lpc-name-key (fn-lpc-names-scan *fn-lpc-names* name)))
                  (equal (fn-lpc-at 8 out) (fn-lpc-close-fields s h pin)))))
  :hints (("Goal"
           :use ((:instance fn-lpv-first-line-fixed-column
                    (s (fn-nlv-run (append name '(58)) s pos h pin))
                    (pos (+ pos 1 (len name))) (k 6))
                 (:instance fn-lpv-first-line-fixed-column
                    (s (fn-nlv-run (append name '(58)) s pos h pin))
                    (pos (+ pos 1 (len name))) (k 8))
                 (:instance fn-nlv-run-append (a (append name '(58)))
                            (b (append bytes '(13 10)))))
           :in-theory
           (e/d (fn-lpc-at)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-header-byte fn-lpc-name-key fn-lpc-names-scan
                 fn-lpc-close-fields fn-article-header-bytes-p fn-article-namep
                 fn-article-wspp binary-append len fn-nlv-run-append
                 fn-lpv-first-line-fixed-column fn-lpv-initial-name-run-record)))))

(defthm fn-lpv-first-line-span-is-unfolded-value
  (implies (and (fn-lpv-value-state-p s source value)
                (equal (fn-lpc-at 0 s) :first) (natp (fn-lpc-at 1 s))
                (not (equal (fn-lpc-at 10 s) :fold-empty))
                (fn-article-header-bytes-p bytes)
                (or (not (consp bytes)) (fn-article-wspp (car bytes)))
                (<= (+ (fn-lpc-at 1 s) (len bytes)) *fn-article-max-line-octets*)
                (consp (append value bytes)))
           (let ((out (fn-nlv-run (append bytes '(13 10)) s (len source) h pin)))
             (equal (fn-nov-scrub
                     (fn-lpv-slice (append source (append bytes '(13 10)))
                                   (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                    (fn-nov-scrub (fn-nov-value-content (append value bytes))))))
  :hints (("Goal"
           :use ((:instance fn-lpv-completed-line-span-is-unfolded-value
                    (s (fn-nlv-run bytes s (len source) h pin))
                    (source (append source bytes)) (value (append value bytes))))
           :expand ((:free (s pos) (fn-nlv-run '(13 10) s pos h pin))
                    (:free (s pos) (fn-nlv-run '(10) s pos h pin)))
           :in-theory
           (disable fn-nlv-run-phase-is-control-run-phase fn-lpv-value-state-p fn-nlv-run fn-lpc-header-byte fn-lpc-at
                    fn-lpc-put fn-lpv-slice fn-nov-scrub fn-nov-value-content
                    fn-article-header-bytes-p fn-article-wspp fn-article-has-vcharp
                    binary-append len fn-lpv-completed-line-span-is-unfolded-value
                    fn-nlv-control-run fn-nlv-control-run-is-actual-header-run
                    fn-lpv-content-append fn-lpv-unfolded-append-normalization
                    fn-lpv-header-line-end))))

(defthm fn-lpv-new-field-line-span-is-unfolded-value
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                (fn-article-namep name) (fn-article-header-bytes-p bytes)
                (consp bytes) (fn-article-wspp (car bytes))
                (<= (+ (len name) 1 (len bytes)) *fn-article-max-line-octets*))
           (let* ((line (append name (cons 58 (append bytes '(13 10)))))
                  (out (fn-nlv-run line s (len source) h pin)))
             (equal (fn-nov-scrub
                     (fn-lpv-slice (append source line) (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                    (fn-nov-scrub (fn-nov-value-content bytes)))))
  :hints (("Goal"
           :use ((:instance fn-lpv-first-line-span-is-unfolded-value
                    (s (fn-nlv-run (append name '(58)) s (len source) h pin))
                    (source (append source (append name '(58)))) (value nil))
                 (:instance fn-nlv-run-append (a (append name '(58)))
                            (b (append bytes '(13 10))) (pos (len source))))
           :in-theory
           (e/d (fn-lpc-at fn-lpv-value-state-p)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-header-byte fn-lpc-name-key fn-lpc-names-scan
                 fn-lpc-close-fields fn-lpv-slice fn-nov-scrub fn-nov-value-content
                 fn-article-header-bytes-p fn-article-namep fn-article-has-vcharp
                 fn-article-body-crlfp fn-article-wspp binary-append len
                 fn-nlv-run-append fn-lpv-first-line-span-is-unfolded-value
                 fn-lpv-initial-name-run-record)))))

(defthm fn-lpv-fold-run-control
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (fn-lpc-at 2 s) (fn-article-header-bytes-p bytes)
                (fn-article-wspp (car bytes))
                (<= (len bytes) *fn-article-max-line-octets*))
           (equal (fn-nlv-control (fn-nlv-run bytes s pos h pin))
                  (fn-nlv-value-final bytes 0 t (and (fn-lpc-at 3 s) t) :fold-empty)))
  :hints (("Goal"
           :use ((:instance fn-nlv-value-run-valid (bytes (cdr bytes)) (n 1)
                    (current t) (visible (and (fn-lpc-at 3 s) t)) (mode :fold-empty)))
           :expand ((:free (c) (fn-nlv-control-run bytes c)))
           :in-theory
           (e/d (fn-nlv-control fn-nlv-control-byte fn-nlv-value fn-nlv-value-final
                 fn-lpc-at fn-article-header-bytes-p fn-article-wspp
                 fn-article-header-bytep fn-article-vcharp fn-article-has-vcharp)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-nlv-control-run len)))))

(defthm fn-lpv-fold-run-end-phase
  (implies (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (fn-lpc-at 2 s) (fn-article-header-bytes-p bytes)
                (fn-article-wspp (car bytes))
                (<= (len bytes) *fn-article-max-line-octets*))
           (and (equal (fn-lpc-at 0 (fn-nlv-run bytes s pos h pin)) :value)
                (equal (fn-lpc-at 10 (fn-nlv-run bytes s pos h pin))
                       (if (fn-article-has-vcharp bytes) :fold-visible :fold-empty))))
  :hints (("Goal"
           :use (fn-lpv-fold-run-control
                 (:instance fn-lpv-control-at-by-definition (s (fn-nlv-run bytes s pos h pin))))
           :in-theory
           (e/d (fn-nlv-value-final fn-lpc-at)
                (fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-nlv-control fn-article-header-bytes-p
                 fn-article-has-vcharp fn-article-wspp len
                 fn-lpv-fold-run-control fn-lpv-control-at-by-definition
                 fn-nlv-control-run-is-actual-header-run fn-nlv-control-run
                 fn-lpc-close-fields fn-lpc-names-scan fn-lpc-name-key)))))

(defthm fn-lpv-fold-line-fixed-column
  (implies (and (natp pos)
                (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (fn-lpc-at 2 s) (fn-article-header-bytes-p bytes)
                (fn-article-wspp (car bytes))
                (<= (len bytes) *fn-article-max-line-octets*)
                (member-equal k '(2 6 7 8)))
           (equal (fn-lpc-at k (fn-nlv-run (append bytes '(13 10)) s pos h pin))
                  (fn-lpc-at k s)))
  :hints (("Goal" :expand ((:free (s pos) (fn-nlv-run '(13 10) s pos h pin))
                           (:free (s pos) (fn-nlv-run '(10) s pos h pin)))
           :in-theory
           (disable fn-nlv-run-phase-is-control-run-phase fn-nlv-run fn-lpc-header-byte fn-lpc-value-byte fn-lpc-at
                    fn-lpc-put fn-article-header-bytes-p fn-article-wspp
                    fn-article-has-vcharp binary-append len fn-nlv-control-run
                    fn-nlv-control-run-is-actual-header-run))))

(defthm fn-lpv-fold-line-span-is-unfolded-value
  (implies (and (fn-lpv-value-state-p s source value)
                (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
                (fn-lpc-at 2 s) (fn-article-header-bytes-p bytes)
                (fn-article-wspp (car bytes)) (fn-article-has-vcharp bytes)
                (<= (len bytes) *fn-article-max-line-octets*))
           (let ((out (fn-nlv-run (append bytes '(13 10)) s (len source) h pin)))
             (equal (fn-nov-scrub
                     (fn-lpv-slice (append source (append bytes '(13 10)))
                                   (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                    (fn-nov-scrub (fn-nov-value-content (append value bytes))))))
  :hints (("Goal"
           :use ((:instance fn-lpv-completed-line-span-is-unfolded-value
                    (s (fn-nlv-run bytes s (len source) h pin))
                    (source (append source bytes)) (value (append value bytes))))
           :expand ((:free (s pos) (fn-nlv-run '(13 10) s pos h pin))
                    (:free (s pos) (fn-nlv-run '(10) s pos h pin)))
           :in-theory
           (disable fn-nlv-run-phase-is-control-run-phase fn-lpv-value-state-p fn-nlv-run fn-lpc-header-byte fn-lpc-at
                    fn-lpc-put fn-lpv-slice fn-nov-scrub fn-nov-value-content
                    fn-article-header-bytes-p fn-article-wspp fn-article-has-vcharp
                    binary-append len fn-lpv-completed-line-span-is-unfolded-value
                    fn-nlv-control-run fn-nlv-control-run-is-actual-header-run
                    fn-lpv-content-append fn-lpv-unfolded-append-normalization
                    fn-lpv-header-line-end))))
