; Acceptance composition of the actual legacy byte machine and article parser.
; Proof vocabulary only; no served allocation or host parsing is introduced.
(in-package "ACL2")
(include-book "legacy-parser-validity")

(defun fn-nlpc-scan-statep (c left)
  (declare (xargs :guard t))
  (and (fn-nlv-header-phasep c)
       (or (equal (fn-lpc-at 0 c) :bad)
           (and (natp left) (<= left 998)
                (<= 998 (+ left (nfix (fn-lpc-at 1 c))))
                (implies (equal (fn-lpc-at 0 c) :start)
                         (equal left 998))))))

(defthm fn-nlpc-scan-byte-preserves-state
  (implies (and (fn-nlpc-scan-statep c left) (not (zp left))
                (not (equal byte 13)) (not (equal byte 10)))
           (fn-nlpc-scan-statep (fn-nlv-control-byte c byte) (1- left)))
  :hints (("Goal" :in-theory (enable fn-nlpc-scan-statep fn-nlv-header-phasep
                                     fn-nlv-control-byte fn-nlv-value fn-nlv-phase fn-lpc-at))))

(local (defun fn-nlpc-scan-ind (octets prefix left c)
  (if (and (consp octets) (not (equal (car octets) 13))
           (not (equal (car octets) 10)) (not (zp left)))
      (fn-nlpc-scan-ind (cdr octets) (cons (car octets) prefix) (1- left)
                      (fn-nlv-control-byte c (car octets)))
    (list prefix left c))))

(defthm fn-nlpc-scan-state-is-header
  (implies (fn-nlpc-scan-statep c left) (fn-nlv-header-phasep c))
  :hints (("Goal" :in-theory (enable fn-nlpc-scan-statep))))
(defthm fn-nlpc-header-is-not-body
  (implies (fn-nlv-header-phasep c) (not (equal (fn-lpc-at 0 c) :body)))
  :hints (("Goal" :in-theory (enable fn-nlv-header-phasep))))
(defthm fn-nlpc-exhausted-scan-is-bad
  (implies (and (fn-nlpc-scan-statep c left) (zp left)
                (not (equal byte 13)) (not (equal byte 10)))
           (equal (fn-lpc-at 0 (fn-nlv-control-byte c byte)) :bad))
  :hints (("Goal" :in-theory (enable fn-nlpc-scan-statep fn-nlv-header-phasep
                                     fn-nlv-control-byte fn-nlv-phase fn-lpc-at))))
(defthm fn-nlpc-cr-nonlf-control-is-bad
  (implies (not (equal byte 10))
           (equal (fn-lpc-at 0 (fn-nlv-control-byte (fn-nlv-control-byte c 13) byte)) :bad))
  :hints (("Goal" :in-theory (enable fn-nlv-control-byte fn-nlv-phase fn-lpc-at))))
(defthm fn-nlpc-header-cr-is-not-body
  (implies (fn-nlv-header-phasep c)
           (not (equal (fn-lpc-at 0 (fn-nlv-control-byte c 13)) :body)))
  :hints (("Goal" :in-theory (enable fn-nlv-header-phasep fn-nlv-control-byte fn-nlv-phase fn-lpc-at))))
(defthm fn-nlpc-header-lf-is-bad
  (implies (fn-nlv-header-phasep c)
           (equal (fn-lpc-at 0 (fn-nlv-control-byte c 10)) :bad))
  :hints (("Goal" :in-theory (enable fn-nlv-header-phasep fn-nlv-control-byte fn-nlv-phase fn-lpc-at))))

(defthm fn-nlpc-failed-scanner-cannot-accept
  (implies (and (fn-nlpc-scan-statep c left)
                (not (fn-article-line-okp (fn-article-next-line-aux octets prefix left))))
           (not (equal (fn-lpc-at 0 (fn-nlv-control-run octets c)) :body)))
  :hints (("Goal" :induct (fn-nlpc-scan-ind octets prefix left c)
           :expand ((fn-nlv-control-run octets c)
                    (:free (c) (fn-nlv-control-run (cdr octets) c)))
           :in-theory (e/d (fn-article-next-line-aux fn-article-line-okp fn-article-error
                            fn-nlv-control-run)
                           (fn-nlpc-scan-statep fn-nlv-header-phasep fn-nlv-control-byte fn-lpc-at)))
          ("Subgoal *1/2" :cases ((equal (car octets) 13) (equal (car octets) 10)))))

(defthm fn-nlpc-actual-next-line-failure-cannot-accept
  (implies (and (equal (fn-lpc-at 0 s) :start)
                (not (fn-article-line-okp (fn-article-next-line octets))))
           (not (equal (fn-lpc-at 0 (fn-nlv-run octets s pos h pin)) :body)))
  :hints (("Goal" :use ((:instance fn-nlpc-failed-scanner-cannot-accept
                         (c (fn-nlv-control s)) (left 998) (prefix nil)))
           :in-theory (e/d (fn-article-next-line fn-nlpc-scan-statep
                            fn-nlv-header-phasep fn-nlv-control fn-lpc-at)
                           (fn-nlpc-failed-scanner-cannot-accept fn-nlv-control-run
                            fn-nlv-run fn-article-next-line-aux)))))

(defthm fn-nlpc-physicalp-append
  (equal (fn-nlv-physicalp (append a b))
         (and (fn-nlv-physicalp (true-list-fix a)) (fn-nlv-physicalp b)))
  :hints (("Goal" :induct (fn-nlv-physicalp a) :in-theory (enable fn-nlv-physicalp))))
(defthm fn-nlpc-physicalp-rev
  (equal (fn-nlv-physicalp (rev a)) (fn-nlv-physicalp (true-list-fix a)))
  :hints (("Goal" :induct (rev a) :in-theory (enable rev fn-nlv-physicalp))))

(local (defthm fn-nlpc-append-associative
  (equal (append (append a b) c) (append a b c))))

(defthm fn-nlpc-next-line-aux-partition
  (implies (and (fn-nlv-physicalp prefix)
                (fn-article-line-okp (fn-article-next-line-aux octets prefix left)))
    (let ((result (fn-article-next-line-aux octets prefix left)))
      (and (fn-nlv-physicalp (fn-article-line-value result))
           (equal (append (fn-article-line-value result) '(13 10) (fn-article-line-rest result))
                  (append (rev prefix) octets))
           (<= (len (fn-article-line-value result)) (+ (len prefix) (nfix left))))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets prefix left)
           :in-theory (enable fn-article-next-line-aux fn-nlv-physicalp
                              fn-article-line-okp fn-article-line-value fn-article-line-rest
                              fn-article-error reverse))))

(defthm fn-nlpc-next-line-partition
  (implies (fn-article-line-okp (fn-article-next-line octets))
    (let ((result (fn-article-next-line octets)))
      (and (fn-nlv-physicalp (fn-article-line-value result))
           (equal (append (fn-article-line-value result) '(13 10) (fn-article-line-rest result)) octets)
           (<= (len (fn-article-line-value result)) 998))))
  :hints (("Goal" :use ((:instance fn-nlpc-next-line-aux-partition (prefix nil) (left 998)))
           :in-theory (e/d (fn-article-next-line fn-nlv-physicalp)
                           (fn-article-next-line-aux fn-nlpc-next-line-aux-partition)))))

(defthm fn-nlpc-split-partition
  (implies (and (true-listp prefix)
                (fn-article-line-okp (fn-article-split-colon-aux line prefix)))
           (equal (append (fn-article-line-value (fn-article-split-colon-aux line prefix))
                          (cons 58 (fn-article-line-rest (fn-article-split-colon-aux line prefix))))
                  (append (rev prefix) line)))
  :hints (("Goal" :induct (fn-article-split-colon-aux line prefix)
           :in-theory (enable fn-article-split-colon-aux fn-article-line-okp
                              fn-article-line-value fn-article-line-rest fn-article-error reverse))))

(local (defthm fn-nlpc-len-append
  (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-nlpc-new-field-control
  (implies (and (true-listp line)
                (fn-article-line-okp (fn-article-new-field line))
                (or (not current) visible)
                (<= (len line) 998))
           (equal (fn-nlv-control-run (append line '(13 10))
                                     (list :start 0 current visible mode))
                  (list :start 0 t
                        (and (fn-article-has-vcharp
                               (fn-article-field-unfolded-value
                                (fn-article-line-value (fn-article-new-field line)))) t)
                        :plain)))
  :hints (("Goal"
           :use ((:instance fn-nlpc-split-partition (prefix nil))
                 (:instance fn-nlv-new-field-line-control
                  (name (fn-article-line-value (fn-article-split-colon-aux line nil)))
                  (value (fn-article-line-rest (fn-article-split-colon-aux line nil)))
                  (old-mode mode)))
           :in-theory (e/d (fn-article-new-field fn-article-make-field
                            fn-article-field-unfolded-value fn-article-line-okp
                            fn-article-line-value fn-article-line-rest fn-article-error)
                           (fn-nlpc-split-partition fn-nlv-new-field-line-control
                            fn-nlv-control-run fn-nlv-control-run-append
                            fn-article-split-colon-aux fn-nlv-new-field-is-name-tail fn-article-wspp
                            fn-article-namep fn-article-header-bytes-p fn-article-has-vcharp)))))

(defthm fn-nlpc-control-separator-exact
  (implies (and (booleanp current) (booleanp visible))
   (equal (equal (fn-lpc-at 0
                   (fn-nlv-control-run (append '(13 10) body)
                      (list :start 0 current visible mode))) :body)
          (and (or (not current) visible) (fn-article-body-crlfp body))))
  :hints (("Goal"
           :use ((:instance fn-nlv-actual-separator-body-exact
                  (s (list :start 0 current visible nil nil nil nil nil nil mode))
                  (pos 0) (h nil) (pin nil)))
           :in-theory (e/d (fn-nlv-control fn-lpc-at)
                           (fn-nlv-actual-separator-body-exact fn-nlv-run
                            fn-nlv-control-run fn-nlv-control-run-append
                            fn-nlv-control-byte fn-article-body-crlfp)))))

(defthm fn-nlpc-field-closed-after-fold
  (implies (fn-article-fold-linep line)
           (fn-article-field-closedp (fn-article-add-fold current line)))
  :hints (("Goal" :in-theory (enable fn-article-field-closedp fn-article-add-fold
                                     fn-article-make-field fn-article-field-unfolded-value
                                     fn-article-fold-linep fn-article-has-vcharp))))


; Counter-free logical grammar. The proof below connects it to the actual
; parser under the source-dominated counters; it is never called by the host.
(defun fn-nlpc-accept-lines (octets current)
  (declare (xargs :measure (len octets) :guard t :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-article-next-line fn-article-next-line-aux
                                                      fn-article-line-okp fn-article-line-value fn-article-line-rest)))))
  (let ((next (fn-article-next-line octets)))
    (and (fn-article-line-okp next)
         (let ((line (fn-article-line-value next)) (rest (fn-article-line-rest next)))
           (if (not line)
               (and (fn-article-field-closedp current) (fn-article-body-crlfp rest))
             (if (fn-article-wspp (car line))
                 (and current (fn-article-fold-linep line)
                      (fn-nlpc-accept-lines rest (fn-article-add-fold current line)))
               (let ((field (fn-article-new-field line)))
                 (and (fn-article-field-closedp current) (fn-article-line-okp field)
                      (fn-nlpc-accept-lines rest (fn-article-line-value field))))))))))

(defthm fn-nlpc-parser-is-counter-free-grammar
 (implies (and (< (len octets) (nfix lines-left))
               (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits))
               (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits)))
          (equal (fn-article-result-okp
                   (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current names))
                 (fn-nlpc-accept-lines octets current)))
 :hints (("Goal" :induct (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current names)
          :expand ((:free (current) (fn-nlpc-accept-lines octets current)))
          :in-theory (e/d (fn-novlp-parse-lines fn-article-error fn-article-result-okp fn-article-line-okp)
                          (fn-nlpc-accept-lines len fn-nlv-new-field-is-name-tail fn-article-fold-linep fn-article-wspp
                           fn-article-limit-fields fn-article-limit-octets fn-article-next-line fn-article-next-line-aux fn-article-new-field
                           fn-article-line-value fn-article-line-rest
                           fn-article-field-closedp fn-article-add-fold fn-novlp-add-field fn-novlp-normalize)))))

(defthm fn-nlpc-physical-line-acceptance-step
  (implies (and (fn-nlv-physicalp line) (consp line) (<= (len line) 998)
                (booleanp current) (booleanp visible))
   (equal
    (equal (fn-lpc-at 0
             (fn-nlv-control-run (append line '(13 10) suffix)
                                (list :start 0 current visible mode))) :body)
    (if (fn-article-wspp (car line))
        (and current (fn-article-fold-linep line)
             (equal (fn-lpc-at 0
                      (fn-nlv-control-run suffix (list :start 0 t t :fold-visible))) :body))
      (and (or (not current) visible)
           (fn-article-line-okp (fn-article-new-field line))
           (equal (fn-lpc-at 0
                    (fn-nlv-control-run suffix
                       (list :start 0 t
                         (and (fn-article-has-vcharp
                            (fn-article-field-unfolded-value
                             (fn-article-line-value (fn-article-new-field line)))) t)
                         :plain))) :body)))))
  :hints (("Goal"
           :do-not-induct t
           :cases (current visible (fn-article-fold-linep line)
                   (fn-article-line-okp (fn-article-new-field line)))
           :use ((:instance fn-nlv-control-run-append
                   (a (append line '(13 10))) (b suffix)
                   (c (list :start 0 current visible mode)))
                 (:instance fn-nlv-physical-line-exact-grammar (mode mode)))
           :in-theory (e/d (fn-article-fold-linep fn-lpc-at)
                           (fn-nlv-control-run fn-nlv-control-run-append fn-nlv-control-byte
                            fn-nlv-physical-line-exact-grammar fn-nlv-physical-line-phase fn-nlv-new-field-is-name-tail
                            fn-article-wspp fn-article-new-field fn-article-line-okp
                            fn-article-header-bytes-p fn-article-has-vcharp fn-nlv-physicalp)))))

(defthm fn-nlpc-new-field-current-nonempty
  (implies (fn-article-line-okp (fn-article-new-field line))
           (consp (fn-article-line-value (fn-article-new-field line))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (e/d (fn-article-new-field fn-article-line-okp fn-article-line-value
                                   fn-article-make-field fn-article-error)
                                  (fn-article-split-colon-aux fn-nlv-new-field-is-name-tail)))))

(defthm fn-nlpc-fold-has-visible
  (implies (fn-article-fold-linep line) (fn-article-has-vcharp line))
  :hints (("Goal" :in-theory (enable fn-article-fold-linep))))

(local (defun fn-nlpc-accept-ind (octets current mode)
  (declare (xargs :measure (len octets)
                  :hints (("Goal" :in-theory (disable fn-article-next-line fn-article-next-line-aux
                                                      fn-article-line-okp fn-article-line-value fn-article-line-rest)))))
  (let ((next (fn-article-next-line octets)))
    (if (fn-article-line-okp next)
        (let ((line (fn-article-line-value next)) (rest (fn-article-line-rest next)))
          (if (not line) mode
            (if (fn-article-wspp (car line))
                (if (and current (fn-article-fold-linep line))
                    (fn-nlpc-accept-ind rest (fn-article-add-fold current line) :fold-visible) mode)
              (if (and (fn-article-field-closedp current) (fn-article-line-okp (fn-article-new-field line)))
                  (fn-nlpc-accept-ind rest (fn-article-line-value (fn-article-new-field line)) :plain) mode))))
      mode))))


(defthm fn-nlpc-control-next-line-failure
  (implies (not (fn-article-line-okp (fn-article-next-line octets)))
           (not (equal (fn-lpc-at 0 (fn-nlv-control-run octets
                          (list :start 0 current visible mode))) :body)))
  :hints (("Goal" :use ((:instance fn-nlpc-failed-scanner-cannot-accept
                         (c (list :start 0 current visible mode)) (left 998) (prefix nil)))
           :in-theory (e/d (fn-article-next-line fn-nlpc-scan-statep fn-nlv-header-phasep fn-lpc-at)
                           (fn-nlpc-failed-scanner-cannot-accept fn-nlv-control-run fn-article-next-line-aux)))))

(defthm fn-nlpc-control-next-line-success
 (implies (and (fn-article-line-okp (fn-article-next-line octets))
               (booleanp current) (booleanp visible))
   (equal (equal (fn-lpc-at 0 (fn-nlv-control-run octets (list :start 0 current visible mode))) :body)
     (let ((line (fn-article-line-value (fn-article-next-line octets)))
           (rest (fn-article-line-rest (fn-article-next-line octets))))
       (if (not line)
           (and (or (not current) visible) (fn-article-body-crlfp rest))
         (if (fn-article-wspp (car line))
             (and current (fn-article-fold-linep line)
                  (equal (fn-lpc-at 0 (fn-nlv-control-run rest (list :start 0 t t :fold-visible))) :body))
           (and (or (not current) visible)
                (fn-article-line-okp (fn-article-new-field line))
                (equal (fn-lpc-at 0
                         (fn-nlv-control-run rest
                           (list :start 0 t
                             (and (fn-article-has-vcharp
                               (fn-article-field-unfolded-value
                                 (fn-article-line-value (fn-article-new-field line)))) t)
                             :plain))) :body)))))))
 :hints (("Goal" :do-not-induct t
          :use (fn-nlpc-next-line-partition
                (:instance fn-nlpc-physical-line-acceptance-step
                  (line (fn-article-line-value (fn-article-next-line octets)))
                  (suffix (fn-article-line-rest (fn-article-next-line octets))))
                (:instance fn-nlpc-control-separator-exact
                  (body (fn-article-line-rest (fn-article-next-line octets)))))
          :in-theory (disable fn-nlpc-next-line-partition fn-nlpc-physical-line-acceptance-step
                        fn-nlpc-control-separator-exact fn-nlv-control-run fn-nlv-control-run-append
                        fn-article-next-line fn-article-line-okp fn-article-line-value fn-article-line-rest
                        fn-article-new-field fn-article-field-unfolded-value fn-article-body-crlfp
                        fn-article-wspp fn-article-fold-linep fn-article-has-vcharp fn-lpc-at
                        fn-nlv-new-field-is-name-tail))))
(defthm fn-nlpc-byte-machine-is-counter-free-grammar
  (equal (equal (fn-lpc-at 0
                  (fn-nlv-control-run octets
                    (list :start 0 (and current t)
                       (and (fn-article-has-vcharp (fn-article-field-unfolded-value current)) t)
                       mode))) :body)
         (fn-nlpc-accept-lines octets current))
  :hints (("Goal" :induct (fn-nlpc-accept-ind octets current mode)
           :expand ((:free (current) (fn-nlpc-accept-lines octets current)))
           :in-theory (e/d (fn-article-field-closedp fn-article-add-fold fn-article-make-field
                            fn-article-field-unfolded-value)
                           (fn-nlpc-accept-lines fn-nlv-control-run fn-nlv-control-run-append
                            fn-nlv-control-byte fn-article-next-line fn-article-next-line-aux
                            fn-article-new-field fn-article-line-okp fn-article-line-value fn-article-line-rest
                            fn-article-fold-linep fn-article-wspp fn-article-body-crlfp
                            fn-article-has-vcharp fn-lpc-at fn-nlv-new-field-is-name-tail)))))

(defthm fn-nlpc-widest-projection-is-grammar
  (implies (and (fn-cbor-at-mostp octets *fn-article-max-octets*)
                (fn-cbor-octet-listp octets))
           (equal (fn-article-result-okp (fn-novlp-parse octets))
                  (fn-nlpc-accept-lines octets nil)))
  :hints (("Goal" :use ((:instance fn-nlpc-parser-is-counter-free-grammar
                         (limits *fn-article-ceiling-limits*) (lines-left (+ 1 *fn-article-max-octets*))
                         (header-bytes 0) (nfields 0) (columns (fn-novlp-columns nil *fn-novlp-names*))
                         (current nil) (names *fn-novlp-names*)))
           :in-theory (e/d (fn-novlp-parse fn-novlp-parse-under
                            fn-article-limit-fields fn-article-limit-lines fn-article-limit-octets)
                           (fn-novlp-parse-lines fn-novlp-columns fn-cbor-at-mostp fn-cbor-octet-listp
                            fn-nlpc-parser-is-counter-free-grammar fn-nlpc-accept-lines fn-article-result-okp
                            fn-novlp-parse-under-is-parser-projection fn-novlp-parse-is-parser-projection)))))

(defthm fn-nlpc-projection-ok-unfolds
  (equal (fn-article-result-okp (fn-novlp-result parsed names))
         (fn-article-result-okp parsed))
  :hints (("Goal" :in-theory (e/d (fn-novlp-result fn-article-result-okp)
                                 (fn-novlp-columns fn-novlp-normalize fn-article-fields
                                  fn-article-result-article)))))

(defthm fn-nlpc-actual-parser-is-grammar
  (implies (and (fn-cbor-at-mostp octets *fn-article-max-octets*)
                (fn-cbor-octet-listp octets))
           (equal (fn-article-result-okp (fn-article-parse octets))
                  (fn-nlpc-accept-lines octets nil)))
  :hints (("Goal" :use fn-nlpc-widest-projection-is-grammar
           :in-theory (disable fn-nlpc-widest-projection-is-grammar fn-article-parse
                               fn-novlp-parse fn-novlp-result fn-article-result-okp fn-nlpc-accept-lines))))

(defthm fn-nlpc-actual-byte-machine-accepts-iff-article-parser
  (implies (and (fn-cbor-at-mostp octets *fn-article-max-octets*)
                (fn-cbor-octet-listp octets))
           (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) pos h pin)) :body)
                  (fn-article-result-okp (fn-article-parse octets))))
  :hints (("Goal"
           :use ((:instance fn-nlpc-byte-machine-is-counter-free-grammar (current nil) (mode :plain)))
           :in-theory (e/d (fn-lpc-header-begin fn-nlv-control fn-lpc-at)
                           (fn-nlv-run fn-nlv-control-run fn-nlpc-byte-machine-is-counter-free-grammar
                            fn-nlpc-accept-lines fn-article-parse fn-article-result-okp
                            fn-nlpc-control-next-line-failure)))))
