; Actual byte-header machine / line grammar simulation. Proof vocabulary;
; no host changes. The span/value simulation is owned by legacy-parser-header.
(in-package "ACL2")
(include-book "legacy-parser-header")
(include-book "nov-line-projection")

(defun fn-nlv-run (bytes s pos h pin)
  (declare (xargs :guard (natp pos)))
  (if (consp bytes)
      (fn-nlv-run (cdr bytes) (fn-lpc-header-byte s (car bytes) pos h pin)
                  (+ 1 pos) h pin)
    s))

(defun fn-nlv-body-phasep (s)
  (declare (xargs :guard t))
  (member-eq (fn-lpc-at 0 s) '(:body :body-cr :bad)))

(defun fn-nlv-body-residual (bytes s)
  (declare (xargs :guard t))
  (case (fn-lpc-at 0 s)
    (:body (fn-article-body-crlfp bytes))
    (:body-cr (and (consp bytes) (equal (car bytes) 10)
                   (fn-article-body-crlfp (cdr bytes))))
    (otherwise nil)))

(defthm fn-nlv-header-byte-preserves-body-phase
  (implies (fn-nlv-body-phasep s)
           (fn-nlv-body-phasep (fn-lpc-header-byte s byte pos h pin)))
  :hints (("Goal" :in-theory
           (e/d (fn-nlv-body-phasep fn-lpc-header-byte fn-lpc-header-bad)
                (fn-lpc-at fn-lpc-put fn-lpc-value-byte fn-lpc-close-fields)))))

(defthm fn-nlv-body-byte-is-article-body-crlfp
  (implies (fn-nlv-body-phasep s)
           (equal (fn-nlv-body-residual (cons byte rest) s)
                  (fn-nlv-body-residual rest (fn-lpc-header-byte s byte pos h pin))))
  :hints (("Goal" :in-theory
           (e/d (fn-nlv-body-phasep fn-nlv-body-residual fn-lpc-header-byte
                 fn-lpc-header-bad fn-article-body-crlfp)
                (fn-lpc-at fn-lpc-put fn-lpc-value-byte fn-lpc-close-fields)))))

(defthm fn-nlv-run-preserves-body-phase
  (implies (fn-nlv-body-phasep s)
           (fn-nlv-body-phasep (fn-nlv-run bytes s pos h pin)))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :in-theory (e/d (fn-nlv-run)
                           (fn-nlv-body-phasep fn-lpc-header-byte)))))

(local (defthm fn-nlv-body-residual-empty
  (implies (not (consp bytes))
           (equal (fn-nlv-body-residual bytes s) (equal (fn-lpc-at 0 s) :body)))
  :hints (("Goal" :in-theory (enable fn-nlv-body-residual fn-article-body-crlfp)))))

(defthm fn-nlv-run-refines-body-crlfp
  (implies (fn-nlv-body-phasep s)
           (equal (fn-nlv-body-residual nil (fn-nlv-run bytes s pos h pin))
                  (fn-nlv-body-residual bytes s)))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :in-theory (e/d (fn-nlv-run)
                           (fn-nlv-body-phasep fn-lpc-header-byte fn-nlv-body-residual)))))

(defthm fn-nlv-run-append
  (implies (natp pos)
           (equal (fn-nlv-run (append a b) s pos h pin)
                  (fn-nlv-run b (fn-nlv-run a s pos h pin)
                              (+ pos (len a)) h pin)))
  :hints (("Goal" :induct (fn-nlv-run a s pos h pin)
           :in-theory (e/d (fn-nlv-run) (fn-lpc-header-byte)))))

(defthm fn-nlv-body-residual-at-end
  (implies (fn-nlv-body-phasep s)
           (equal (fn-nlv-body-residual nil s)
                  (equal (fn-lpc-at 0 s) :body)))
  :hints (("Goal" :in-theory
           (e/d (fn-nlv-body-phasep fn-nlv-body-residual fn-article-body-crlfp)
                (fn-lpc-at)))))

(defthm fn-nlv-body-run-accepts-exact-article-body
  (implies (equal (fn-lpc-at 0 s) :body)
           (equal (equal (fn-lpc-at 0 (fn-nlv-run bytes s pos h pin)) :body)
                  (fn-article-body-crlfp bytes)))
  :hints (("Goal" :use fn-nlv-run-refines-body-crlfp
           :in-theory (e/d (fn-nlv-body-phasep fn-nlv-body-residual)
                           (fn-nlv-run fn-lpc-at fn-article-body-crlfp
                            fn-nlv-run-refines-body-crlfp)))))

; Grammar control only: source offsets, names and output spans cannot
; influence whether a byte is grammatical. This is a logical abstraction
; of the actual machine, not a second host implementation.
(defun fn-nlv-control (s)
  (declare (xargs :guard t))
  (list (fn-lpc-at 0 s) (nfix (fn-lpc-at 1 s))
        (and (fn-lpc-at 2 s) t) (and (fn-lpc-at 3 s) t) (fn-lpc-at 10 s)))

(defun fn-nlv-phase (phase c)
  (declare (xargs :guard t))
  (list phase (nfix (fn-lpc-at 1 c)) (fn-lpc-at 2 c) (fn-lpc-at 3 c) (fn-lpc-at 4 c)))

(defun fn-nlv-value (c byte)
  (declare (xargs :guard t))
  (if (not (fn-article-header-bytep byte)) (fn-nlv-phase :bad c)
    (list :value (+ 1 (nfix (fn-lpc-at 1 c))) (fn-lpc-at 2 c)
          (and (or (fn-lpc-at 3 c) (fn-article-vcharp byte)) t)
          (if (and (eq (fn-lpc-at 4 c) :fold-empty) (fn-article-vcharp byte))
              :fold-visible (fn-lpc-at 4 c)))))

(defun fn-nlv-control-byte (c byte)
  (declare (xargs :guard t))
  (let ((phase (fn-lpc-at 0 c)))
    (cond
     ((eq phase :bad) c)
     ((eq phase :body)
      (cond ((equal byte 13) (fn-nlv-phase :body-cr c))
            ((equal byte 10) (fn-nlv-phase :bad c)) (t c)))
     ((eq phase :body-cr)
      (fn-nlv-phase (if (equal byte 10) :body :bad) c))
     ((eq phase :cr-start)
      (fn-nlv-phase (if (and (equal byte 10) (or (not (fn-lpc-at 2 c)) (fn-lpc-at 3 c)))
                        :body :bad) c))
     ((eq phase :cr-line)
      (if (equal byte 10) (list :start 0 (fn-lpc-at 2 c) (fn-lpc-at 3 c) (fn-lpc-at 4 c))
        (fn-nlv-phase :bad c)))
     ((equal byte 13)
      (fn-nlv-phase
       (cond ((eq phase :start) :cr-start)
             ((and (or (eq phase :first) (eq phase :value))
                   (not (eq (fn-lpc-at 4 c) :fold-empty))) :cr-line)
             (t :bad)) c))
     ((or (equal byte 10) (<= *fn-article-max-line-octets* (nfix (fn-lpc-at 1 c))))
      (fn-nlv-phase :bad c))
     ((eq phase :start)
      (if (fn-article-wspp byte)
          (if (fn-lpc-at 2 c)
              (fn-nlv-value (list :start (fn-lpc-at 1 c) (fn-lpc-at 2 c) (fn-lpc-at 3 c) :fold-empty) byte)
            (fn-nlv-phase :bad c))
        (if (and (fn-article-ftextp byte) (or (not (fn-lpc-at 2 c)) (fn-lpc-at 3 c)))
            (list :name 1 t nil :plain) (fn-nlv-phase :bad c))))
     ((eq phase :name)
      (cond ((equal byte 58) (list :first (+ 1 (nfix (fn-lpc-at 1 c))) (fn-lpc-at 2 c) (fn-lpc-at 3 c) (fn-lpc-at 4 c)))
            ((fn-article-ftextp byte) (list :name (+ 1 (nfix (fn-lpc-at 1 c))) (fn-lpc-at 2 c) (fn-lpc-at 3 c) (fn-lpc-at 4 c)))
            (t (fn-nlv-phase :bad c))))
     ((eq phase :first)
      (if (fn-article-wspp byte) (fn-nlv-value c byte) (fn-nlv-phase :bad c)))
     ((eq phase :value) (fn-nlv-value c byte))
     (t (fn-nlv-phase :bad c)))))

(defthm fn-nlv-control-byte-is-generic-header-byte
  (equal (fn-nlv-control (fn-lpc-header-byte-names s byte pos h pin names))
         (fn-nlv-control-byte (fn-nlv-control s) byte))
  :hints (("Goal" :in-theory
           (e/d (fn-nlv-control fn-nlv-control-byte fn-nlv-phase fn-nlv-value
                 fn-lpc-header-byte-names fn-lpc-header-bad fn-lpc-value-byte fn-lpc-at)
                (fn-lpc-put fn-lpc-close-fields
                 fn-lpc-name-key fn-lpc-name-step fn-article-header-bytep
                 fn-article-vcharp fn-article-ftextp fn-article-wspp)))))

(defthm fn-nlv-control-byte-is-actual-header-byte
  (equal (fn-nlv-control (fn-lpc-header-byte s byte pos h pin))
         (fn-nlv-control-byte (fn-nlv-control s) byte))
  :hints (("Goal" :in-theory (e/d (fn-lpc-header-byte)
                                  (fn-lpc-header-byte-names fn-nlv-control fn-nlv-control-byte)))))

(defun fn-nlv-control-run (bytes c)
  (declare (xargs :guard t))
  (if (consp bytes)
      (fn-nlv-control-run (cdr bytes) (fn-nlv-control-byte c (car bytes))) c))

(defthm fn-nlv-control-run-is-actual-header-run
  (equal (fn-nlv-control (fn-nlv-run bytes s pos h pin))
         (fn-nlv-control-run bytes (fn-nlv-control s)))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :in-theory (e/d (fn-nlv-run fn-nlv-control-run)
                           (fn-nlv-control fn-nlv-control-byte fn-lpc-header-byte)))))

; Proof-only runs of the actual shared name-parameterized header transition.
; Stored field names affect selection, never grammar acceptance.
(defun fn-nlv-generic-run (bytes s pos h pin names)
  (declare (xargs :guard (natp pos)
                  :guard-hints (("Goal" :in-theory (disable fn-lpc-header-byte-names)))))
  (if (consp bytes)
      (fn-nlv-generic-run (cdr bytes)
        (fn-lpc-header-byte-names s (car bytes) pos h pin names)
        (+ 1 pos) h pin names)
    s))

(defthm fn-nlv-control-run-is-generic-header-run
  (equal (fn-nlv-control (fn-nlv-generic-run bytes s pos h pin names))
         (fn-nlv-control-run bytes (fn-nlv-control s)))
  :hints (("Goal" :induct (fn-nlv-generic-run bytes s pos h pin names)
           :in-theory (e/d (fn-nlv-generic-run fn-nlv-control-run)
                           (fn-nlv-control fn-nlv-control-byte fn-lpc-header-byte-names)))))

(local (defthm fn-nlv-control-first
  (equal (fn-lpc-at 0 (fn-nlv-control s)) (fn-lpc-at 0 s))
  :hints (("Goal" :in-theory
           (union-theories '(fn-nlv-control fn-lpc-at fn-ag-car fn-ag-cdr car-cons cdr-cons)
             (union-theories (theory 'minimal-theory)
                             (executable-counterpart-theory :here)))))))

(defthm fn-nlv-generic-run-has-original-grammar
  (equal (fn-lpc-at 0 (fn-nlv-generic-run bytes s pos h pin names))
         (fn-lpc-at 0 (fn-nlv-run bytes s pos h pin)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-nlv-control-run-is-generic-header-run
                 fn-nlv-control-run-is-actual-header-run
                 (:instance fn-nlv-control-first
                   (s (fn-nlv-generic-run bytes s pos h pin names)))
                 (:instance fn-nlv-control-first (s (fn-nlv-run bytes s pos h pin))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (executable-counterpart-theory :here)))))

(defthm fn-nlv-control-run-append
  (equal (fn-nlv-control-run (append a b) c)
         (fn-nlv-control-run b (fn-nlv-control-run a c)))
  :hints (("Goal" :induct (fn-nlv-control-run a c)
           :in-theory (e/d (fn-nlv-control-run) (fn-nlv-control-byte)))))

(defthm fn-nlv-control-run-bad
  (implies (equal (fn-lpc-at 0 c) :bad)
           (equal (fn-nlv-control-run bytes c) c))
  :hints (("Goal" :induct (fn-nlv-control-run bytes c)
           :in-theory (enable fn-nlv-control-run fn-nlv-control-byte))))

(defun fn-nlv-value-final (bytes n current visible mode)
  (declare (xargs :guard (natp n)))
  (list :value (+ n (len bytes)) current
        (and (or visible (fn-article-has-vcharp bytes)) t)
        (if (and (eq mode :fold-empty) (fn-article-has-vcharp bytes))
            :fold-visible mode)))

(local (defun fn-nlv-value-ind (bytes n visible mode)
  (if (consp bytes)
      (fn-nlv-value-ind (cdr bytes) (+ 1 n)
                        (and (or visible (fn-article-vcharp (car bytes))) t)
                        (if (and (eq mode :fold-empty)
                                 (fn-article-vcharp (car bytes))) :fold-visible mode))
    (list n visible mode))))

(defthm fn-nlv-value-run-valid
  (implies (and (natp n) (booleanp visible)
                (fn-article-header-bytes-p bytes)
                (<= (+ n (len bytes)) *fn-article-max-line-octets*))
           (equal (fn-nlv-control-run bytes (list :value n current visible mode))
                  (fn-nlv-value-final bytes n current visible mode)))
  :hints (("Goal" :induct (fn-nlv-value-ind bytes n visible mode)
           :in-theory (e/d (fn-nlv-control-run fn-nlv-control-byte fn-nlv-value
                             fn-nlv-value-final fn-nlv-phase fn-lpc-at
                             fn-article-header-bytes-p fn-article-header-bytep
                             fn-article-has-vcharp fn-article-vcharp fn-article-wspp)
                            ()))))

; A fold's own visible byte is required even when the preceding field
; already had one. This equation exposes the repaired physical-line rule.
(defthm fn-nlv-fold-line-control
  (implies (and (fn-article-header-bytes-p line)
                (fn-article-wspp (car line)) (booleanp visible)
                (<= (len line) *fn-article-max-line-octets*))
           (equal
            (fn-nlv-control-run (append line '(13 10))
                                (list :start 0 t visible old-mode))
            (if (fn-article-has-vcharp line)
                (list :start 0 t t :fold-visible)
              (list :bad (len line) t visible :fold-empty))))
  :hints (("Goal"
           :use ((:instance fn-nlv-value-run-valid
                   (bytes (cdr line)) (n 1) (current t)
                   (mode :fold-empty)))
           :expand ((fn-nlv-control-run line (list :start 0 t visible old-mode))
                    (:free (c) (fn-nlv-control-run '(13 10) c))
                    (:free (c) (fn-nlv-control-run '(10) c))
                    (:free (c) (fn-nlv-control-run nil c)))
           :in-theory
           (e/d (fn-nlv-control-byte fn-nlv-phase fn-nlv-value fn-nlv-value-final
                 fn-lpc-at fn-article-header-bytes-p fn-article-header-bytep
                 fn-article-vcharp fn-article-wspp fn-article-has-vcharp)
                (fn-nlv-control-run)))))

(local (defun fn-nlv-name-ind (bytes n)
  (if (consp bytes) (fn-nlv-name-ind (cdr bytes) (+ 1 n)) n)))

(defthm fn-nlv-name-run-valid
  (implies (and (natp n) (fn-article-ftext-listp bytes)
                (<= (+ n (len bytes)) *fn-article-max-line-octets*))
           (equal (fn-nlv-control-run bytes (list :name n current visible mode))
                  (list :name (+ n (len bytes)) current visible mode)))
  :hints (("Goal" :induct (fn-nlv-name-ind bytes n)
           :in-theory (enable fn-nlv-control-run fn-nlv-control-byte fn-lpc-at
                               fn-article-ftext-listp fn-article-ftextp))))

(defthm fn-nlv-initial-name-control
  (implies (and (fn-article-namep name) (or (not current) visible)
                (<= (len name) *fn-article-max-line-octets*))
           (equal (fn-nlv-control-run name (list :start 0 current visible old-mode))
                  (list :name (len name) t nil :plain)))
  :hints (("Goal" :use ((:instance fn-nlv-name-run-valid
                          (bytes (cdr name)) (n 1) (current t)
                          (visible nil) (mode :plain)))
           :expand ((:free (c) (fn-nlv-control-run name c)))
           :in-theory (e/d (fn-article-namep fn-article-ftext-listp fn-article-ftextp
                             fn-article-wspp fn-nlv-control-byte fn-lpc-at)
                            (fn-nlv-control-run)))))

(defthm fn-nlv-initial-value-control
  (implies (and (natp n) (consp bytes) (booleanp visible)
                (fn-article-wspp (car bytes)) (fn-article-header-bytes-p bytes)
                (<= (+ n (len bytes)) *fn-article-max-line-octets*))
           (equal (fn-nlv-control-run bytes (list :first n current visible mode))
                  (fn-nlv-value-final bytes n current visible mode)))
  :hints (("Goal"
           :use ((:instance fn-nlv-value-run-valid (bytes (cdr bytes)) (n (+ 1 n))))
           :expand ((:free (c) (fn-nlv-control-run bytes c)))
           :in-theory
           (e/d (fn-nlv-control-byte fn-nlv-value fn-nlv-value-final fn-nlv-phase
                 fn-lpc-at fn-article-header-bytes-p fn-article-header-bytep
                 fn-article-vcharp fn-article-wspp fn-article-has-vcharp)
                (fn-nlv-control-run)))))

(local (defthm fn-nlv-control-run-colon-unfolds
  (equal (fn-nlv-control-run (cons 58 bytes) c)
         (fn-nlv-control-run bytes (fn-nlv-control-byte c 58)))
  :hints (("Goal" :expand ((fn-nlv-control-run (cons 58 bytes) c))
           :in-theory (disable fn-nlv-control-run fn-nlv-control-byte)))))

(defthm fn-nlv-new-field-line-control
  (implies (and (fn-article-namep name)
                (or (not current) visible)
                (fn-article-header-bytes-p value)
                (or (not (consp value)) (fn-article-wspp (car value)))
                (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*))
           (equal
            (fn-nlv-control-run (append name (cons 58 (append value '(13 10))))
                                (list :start 0 current visible old-mode))
            (list :start 0 t (and (fn-article-has-vcharp value) t) :plain)))
  :hints (("Goal"
           :expand ((:free (c) (fn-nlv-control-run (cons 58 (append value '(13 10))) c))
                    (:free (c) (fn-nlv-control-run '(13 10) c))
                    (:free (c) (fn-nlv-control-run '(10) c))
                    (:free (c) (fn-nlv-control-run nil c)))
           :in-theory
           (e/d (fn-nlv-control-byte fn-nlv-phase fn-nlv-value-final fn-lpc-at
                 fn-article-header-bytes-p fn-article-namep)
                (fn-nlv-control-run fn-nlv-value fn-article-ftext-listp
                 fn-article-vcharp fn-article-wspp fn-article-has-vcharp)))))

; A complete physical line may contain any non-CR/LF object. Malformed
; header bytes are rejected by the grammar, not excluded by this domain.
(local (defthm fn-nlv-control-run-cons-unfolds
 (equal (fn-nlv-control-run (cons byte rest) c)
        (fn-nlv-control-run rest (fn-nlv-control-byte c byte)))
 :hints (("Goal" :expand ((fn-nlv-control-run (cons byte rest) c))
          :in-theory (disable fn-nlv-control-run fn-nlv-control-byte)))))
(local (defthm fn-nlv-control-run-empty-unfolds
 (equal (fn-nlv-control-run nil c) c)
 :hints (("Goal" :in-theory (enable fn-nlv-control-run)))))
(defun fn-nlv-physicalp (line)
  (declare (xargs :guard t))
  (if (consp line)
      (and (not (equal (car line) 13)) (not (equal (car line) 10))
           (fn-nlv-physicalp (cdr line)))
    (null line)))

(defthm fn-nlv-value-line-phase
  (implies (and (natp n) (<= n 998) (fn-nlv-physicalp line))
    (equal (fn-lpc-at 0 (fn-nlv-control-run (append line '(13 10))
                          (list :value n current visible mode)))
           (if (and (fn-article-header-bytes-p line)
                    (<= (+ n (len line)) 998)
                    (or (not (equal mode :fold-empty))
                        (fn-article-has-vcharp line)))
               :start :bad)))
  :hints (("Goal" :induct (fn-nlv-value-ind line n visible mode)
           :expand ((:free (c) (fn-nlv-control-run (append line '(13 10)) c))
                    (:free (c) (fn-nlv-control-run '(13 10) c))
                    (:free (c) (fn-nlv-control-run '(10) c))
                    (:free (c) (fn-nlv-control-run nil c)))
           :in-theory (e/d (fn-nlv-control-byte fn-nlv-value
                              fn-nlv-phase fn-lpc-at fn-nlv-physicalp
                              fn-article-header-bytes-p fn-article-has-vcharp
                              fn-article-header-bytep fn-article-wspp fn-article-vcharp)
                             (fn-nlv-control-run fn-nlv-control-run-append)))))

(defthm fn-nlv-first-line-phase
  (implies (and (natp n) (<= n 998) (fn-nlv-physicalp line))
    (equal (fn-lpc-at 0 (fn-nlv-control-run (append line '(13 10))
                          (list :first n current visible :plain)))
           (if (and (fn-article-header-bytes-p line)
                    (<= (+ n (len line)) 998)
                    (or (not (consp line)) (fn-article-wspp (car line))))
               :start :bad)))
  :hints (("Goal"
           :use ((:instance fn-nlv-value-line-phase
                   (line (cdr line)) (n (+ 1 n)) (mode :plain)
                   (visible (and visible t))))
           :expand ((:free (c) (fn-nlv-control-run (append line '(13 10)) c)))
           :in-theory (e/d (fn-nlv-control-byte fn-nlv-value fn-nlv-phase fn-lpc-at
                              fn-nlv-physicalp fn-article-header-bytes-p
                              fn-article-header-bytep fn-article-wspp fn-article-vcharp)
                           (fn-nlv-control-run fn-nlv-control-run-append)))))


(local (defthm fn-nlv-first-line-car-unfolds
 (implies (and (natp n) (<= n 998) (fn-nlv-physicalp line))
  (equal (car (fn-nlv-control-run (append line '(13 10)) (list :first n current visible :plain)))
   (if (and (fn-article-header-bytes-p line) (<= (+ n (len line)) 998)
            (or (not (consp line)) (fn-article-wspp (car line)))) :start :bad)))
 :hints (("Goal" :use fn-nlv-first-line-phase
          :in-theory (e/d (fn-lpc-at) (fn-nlv-control-run fn-nlv-control-run-append fn-nlv-first-line-phase))))))

(defun fn-nlv-name-tailp (line)
  (declare (xargs :guard t))
  (and (consp line)
       (if (equal (car line) 58)
           (and (fn-article-header-bytes-p (cdr line))
                (or (not (consp (cdr line))) (fn-article-wspp (cadr line))))
         (and (fn-article-ftextp (car line)) (fn-nlv-name-tailp (cdr line))))))

(defthm fn-nlv-name-line-phase
  (implies (and (natp n) (<= n 998) (fn-nlv-physicalp line))
    (equal (fn-lpc-at 0 (fn-nlv-control-run (append line '(13 10))
                          (list :name n current visible :plain)))
           (if (and (fn-nlv-name-tailp line) (<= (+ n (len line)) 998))
               :start :bad)))
  :hints (("Goal" :induct (fn-nlv-name-ind line n)
           :expand ((:free (c) (fn-nlv-control-run (append line '(13 10)) c)))
           :in-theory (e/d (fn-nlv-control-byte fn-nlv-phase fn-lpc-at
                            fn-nlv-physicalp fn-nlv-name-tailp fn-article-ftextp)
                           (fn-nlv-control-run fn-nlv-control-run-append)))))

(defthm fn-nlv-ftext-append
  (equal (fn-article-ftext-listp (append a b))
         (and (fn-article-ftext-listp (true-list-fix a)) (fn-article-ftext-listp b)))
  :hints (("Goal" :induct (fn-article-ftext-listp a)
           :in-theory (enable fn-article-ftext-listp))))
(defthm fn-nlv-ftext-rev
  (equal (fn-article-ftext-listp (rev a))
         (fn-article-ftext-listp (true-list-fix a)))
  :hints (("Goal" :induct (rev a) :in-theory (enable rev fn-article-ftext-listp))))
(defthm fn-nlv-name-tail-is-split
  (implies (true-listp prefix)
   (equal (and (fn-article-ftext-listp prefix) (fn-nlv-name-tailp line))
          (let ((split (fn-article-split-colon-aux line prefix)))
            (and (fn-article-line-okp split)
                 (fn-article-ftext-listp (fn-article-line-value split))
                 (fn-article-header-bytes-p (fn-article-line-rest split))
                 (or (not (consp (fn-article-line-rest split)))
                     (fn-article-wspp (car (fn-article-line-rest split)))))))))

(defthm fn-nlv-split-rest-true-listp
  (implies (true-listp line)
           (true-listp (fn-article-line-rest (fn-article-split-colon-aux line prefix))))
  :hints (("Goal" :induct (fn-article-split-colon-aux line prefix)
           :in-theory (enable fn-article-split-colon-aux fn-article-line-rest fn-article-error))))
(defthm fn-nlv-split-name-consp
  (implies (and (consp prefix) (true-listp prefix)
                (fn-article-line-okp (fn-article-split-colon-aux line prefix)))
           (consp (fn-article-line-value (fn-article-split-colon-aux line prefix))))
  :hints (("Goal" :induct (fn-article-split-colon-aux line prefix)
           :in-theory (enable fn-article-split-colon-aux fn-article-line-value
                              fn-article-line-okp fn-article-error reverse))))

(defthm fn-nlv-new-field-is-name-tail
  (implies (true-listp line)
   (equal (fn-article-line-okp (fn-article-new-field line))
          (and (consp line) (fn-article-ftextp (car line))
               (fn-nlv-name-tailp (cdr line)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-nlv-split-rest-true-listp (line (cdr line)) (prefix (list (car line))))
                 (:instance fn-nlv-split-name-consp (line (cdr line)) (prefix (list (car line))))
                 (:instance fn-nlv-name-tail-is-split (line (cdr line))
                           (prefix (list (car line)))))
           :expand ((fn-article-split-colon-aux line nil))
           :in-theory (e/d (fn-article-new-field fn-article-namep fn-article-line-okp
                            fn-article-line-value fn-article-line-rest fn-article-make-field
                            fn-article-error fn-article-ftext-listp fn-article-ftextp)
                           (fn-nlv-name-tail-is-split fn-article-split-colon-aux fn-nlv-name-tailp)))))

(defthm fn-nlv-physical-line-phase
  (implies (and (consp line) (fn-nlv-physicalp line))
    (equal (fn-lpc-at 0 (fn-nlv-control-run (append line '(13 10))
                          (list :start 0 current visible mode)))
           (if (and (<= (len line) 998)
                    (if (fn-article-wspp (car line))
                        (and current (fn-article-fold-linep line))
                      (and (or (not current) visible)
                           (fn-article-ftextp (car line))
                           (fn-nlv-name-tailp (cdr line)))))
               :start :bad)))
  :hints (("Goal"
           :use ((:instance fn-nlv-value-line-phase (line (cdr line)) (n 1)
                           (visible (and visible t)) (mode :fold-empty))
                 (:instance fn-nlv-name-line-phase (line (cdr line)) (n 1)
                           (current t) (visible nil)))
           :in-theory (e/d (fn-nlv-control-byte fn-nlv-value fn-nlv-phase fn-lpc-at
                            fn-nlv-physicalp fn-article-fold-linep fn-article-header-bytes-p
                            fn-article-has-vcharp fn-article-header-bytep
                            fn-article-wspp fn-article-vcharp fn-article-ftextp)
                           (fn-nlv-control-run fn-nlv-control-run-append
                            fn-nlv-value-line-phase fn-nlv-name-line-phase fn-nlv-name-tailp)))))

(defthm fn-nlv-physicalp-true-listp
  (implies (fn-nlv-physicalp line) (true-listp line))
  :hints (("Goal" :induct (fn-nlv-physicalp line) :in-theory (enable fn-nlv-physicalp))))

(defthm fn-nlv-physical-line-exact-grammar
  (implies (and (consp line) (fn-nlv-physicalp line))
    (equal (fn-lpc-at 0 (fn-nlv-control-run (append line '(13 10))
                          (list :start 0 current visible mode)))
           (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and current (fn-article-fold-linep line))
                      (and (or (not current) visible)
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))
  :hints (("Goal" :use (fn-nlv-physical-line-phase fn-nlv-new-field-is-name-tail)
           :in-theory (disable fn-nlv-physical-line-phase fn-nlv-new-field-is-name-tail
                               fn-nlv-control-run fn-nlv-control-run-append fn-nlv-control-run-cons-unfolds
                               fn-nlv-control-byte fn-lpc-at fn-nlv-physicalp
                               fn-article-line-okp fn-article-new-field
                               fn-article-fold-linep fn-article-ftextp fn-nlv-name-tailp))))

(defthm fn-nlv-run-phase-is-control-run-phase
  (equal (fn-lpc-at 0 (fn-nlv-run bytes s pos h pin))
         (fn-lpc-at 0 (fn-nlv-control-run bytes (fn-nlv-control s))))
  :hints (("Goal" :use fn-nlv-control-run-is-actual-header-run
           :in-theory (e/d (fn-lpc-at fn-nlv-control)
                           (fn-nlv-run fn-nlv-control-run fn-nlv-control-run-is-actual-header-run
                            fn-nlv-control-byte fn-nlv-control-run-append)))))

(defthm fn-nlv-actual-physical-line-exact-grammar
  (implies (and (equal (fn-lpc-at 0 s) :start)
                (equal (nfix (fn-lpc-at 1 s)) 0)
                (consp line) (fn-nlv-physicalp line))
    (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s pos h pin))
           (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))
  :hints (("Goal"
           :use ((:instance fn-nlv-physical-line-exact-grammar
                  (current (and (fn-lpc-at 2 s) t))
                  (visible (and (fn-lpc-at 3 s) t)) (mode (fn-lpc-at 10 s)))
                 (:instance fn-nlv-run-phase-is-control-run-phase
                  (bytes (append line '(13 10)))))
           :in-theory (e/d (fn-nlv-control)
                           (fn-nlv-physical-line-exact-grammar fn-nlv-control-run-is-actual-header-run
                            fn-nlv-control-run fn-nlv-control-run-append fn-nlv-control-run-cons-unfolds
                            fn-nlv-control-byte fn-nlv-run fn-lpc-at
                            fn-nlv-physical-line-phase fn-nlv-new-field-is-name-tail
                            fn-nlv-run-phase-is-control-run-phase fn-nlv-physicalp
                            fn-article-fold-linep fn-article-line-okp fn-article-new-field)))))

; Framing faults and the exact separator/body join.
(defun fn-nlv-header-phasep (c)
  (declare (xargs :guard t))
  (member-eq (fn-lpc-at 0 c) '(:start :name :first :value :bad)))

(defthm fn-nlv-physical-byte-preserves-header-phase
  (implies (and (fn-nlv-header-phasep c)
                (not (equal byte 13)) (not (equal byte 10)))
           (fn-nlv-header-phasep (fn-nlv-control-byte c byte)))
  :hints (("Goal" :in-theory (enable fn-nlv-header-phasep fn-nlv-control-byte
                                     fn-nlv-value fn-nlv-phase fn-lpc-at))))

(defthm fn-nlv-physical-run-preserves-header-phase
  (implies (and (fn-nlv-header-phasep c) (fn-nlv-physicalp line))
           (fn-nlv-header-phasep (fn-nlv-control-run line c)))
  :hints (("Goal" :induct (fn-nlv-control-run line c)
           :in-theory (e/d (fn-nlv-control-run fn-nlv-physicalp)
                           (fn-nlv-header-phasep fn-nlv-control-byte)))))

(defthm fn-nlv-unfinished-header-is-not-body
  (implies (and (fn-nlv-header-phasep c) (fn-nlv-physicalp line))
           (and (not (equal (fn-lpc-at 0 (fn-nlv-control-run line c)) :body))
                (not (equal (fn-lpc-at 0 (fn-nlv-control-run (append line '(13)) c)) :body))))
  :hints (("Goal" :use fn-nlv-physical-run-preserves-header-phase
           :in-theory (e/d (fn-nlv-header-phasep fn-nlv-control-byte fn-nlv-phase fn-lpc-at)
                           (fn-nlv-control-run fn-nlv-physical-run-preserves-header-phase fn-nlv-physicalp)))))

(defthm fn-nlv-bare-lf-is-absorbing-error
  (implies (and (fn-nlv-header-phasep c) (fn-nlv-physicalp line))
           (equal (fn-lpc-at 0 (fn-nlv-control-run (append line (cons 10 suffix)) c)) :bad))
  :hints (("Goal" :use fn-nlv-physical-run-preserves-header-phase
           :in-theory (e/d (fn-nlv-header-phasep fn-nlv-control-byte fn-nlv-phase fn-lpc-at)
                           (fn-nlv-control-run fn-nlv-physical-run-preserves-header-phase fn-nlv-physicalp)))))

(defthm fn-nlv-actual-run-bad
  (implies (equal (fn-lpc-at 0 s) :bad) (equal (fn-nlv-run bytes s pos h pin) s))
  :hints (("Goal" :induct (fn-nlv-run bytes s pos h pin)
           :in-theory (e/d (fn-nlv-run fn-lpc-header-byte)
                           (fn-lpc-at fn-lpc-put fn-lpc-value-byte fn-lpc-close-fields)))))

(defthm fn-nlv-actual-separator-body-exact
  (implies (equal (fn-lpc-at 0 s) :start)
           (equal (equal (fn-lpc-at 0 (fn-nlv-run (append '(13 10) body) s pos h pin)) :body)
                  (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                       (fn-article-body-crlfp body))))
  :hints (("Goal"
           :expand ((fn-nlv-run (append '(13 10) body) s pos h pin))
           :in-theory (e/d (fn-nlv-run fn-lpc-header-byte fn-lpc-header-bad fn-nlv-body-phasep)
                           (fn-lpc-at fn-lpc-put fn-lpc-value-byte fn-lpc-close-fields
                            fn-article-body-crlfp fn-nlv-run-append fn-nlv-run-phase-is-control-run-phase)))))

(defthm fn-nlv-header-phasep-of-control
  (equal (fn-nlv-header-phasep (fn-nlv-control s)) (fn-nlv-header-phasep s))
  :hints (("Goal" :in-theory (enable fn-nlv-header-phasep fn-nlv-control fn-lpc-at))))

(defthm fn-nlv-actual-unfinished-header-is-not-body
  (implies (and (equal (fn-lpc-at 0 s) :start) (fn-nlv-physicalp line))
           (and (not (equal (fn-lpc-at 0 (fn-nlv-run line s pos h pin)) :body))
                (not (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13)) s pos h pin)) :body))))
  :hints (("Goal" :use ((:instance fn-nlv-unfinished-header-is-not-body (c (fn-nlv-control s))))
           :in-theory (e/d (fn-nlv-header-phasep)
                           (fn-nlv-run fn-nlv-control-run fn-nlv-control fn-lpc-at
                            fn-nlv-control-byte fn-nlv-control-run-append fn-nlv-control-run-cons-unfolds
                            fn-nlv-unfinished-header-is-not-body fn-nlv-physicalp)))))

(defthm fn-nlv-actual-bare-lf-is-absorbing-error
  (implies (and (equal (fn-lpc-at 0 s) :start) (fn-nlv-physicalp line))
           (equal (fn-lpc-at 0 (fn-nlv-run (append line (cons 10 suffix)) s pos h pin)) :bad))
  :hints (("Goal" :use ((:instance fn-nlv-bare-lf-is-absorbing-error (c (fn-nlv-control s))))
           :in-theory (e/d (fn-nlv-header-phasep)
                           (fn-nlv-run fn-nlv-control-run fn-nlv-control fn-lpc-at
                            fn-nlv-control-byte fn-nlv-control-run-append fn-nlv-control-run-cons-unfolds
                            fn-nlv-bare-lf-is-absorbing-error fn-nlv-physicalp)))))


(defthm fn-nlv-cr-nonlf-byte-is-always-bad
  (implies (not (equal byte 10))
    (equal (fn-lpc-at 0 (fn-lpc-header-byte (fn-lpc-header-byte s 13 pos h pin) byte (+ 1 pos) h pin)) :bad))
  :hints (("Goal" :in-theory (e/d (fn-lpc-header-byte fn-lpc-header-bad)
                                 (fn-lpc-at fn-lpc-put fn-lpc-value-byte fn-lpc-close-fields)))))

(defthm fn-nlv-actual-cr-nonlf-always-rejects
  (implies (not (equal byte 10))
    (equal (fn-lpc-at 0 (fn-nlv-run (append prefix (cons 13 (cons byte suffix))) s pos h pin)) :bad))
  :hints (("Goal" :induct (fn-nlv-run prefix s pos h pin)
           :in-theory (e/d (fn-nlv-run)
                           (fn-lpc-header-byte fn-lpc-at fn-nlv-run-phase-is-control-run-phase
                            fn-nlv-run-append)))))

; Widest counters are dominated by source consumption, not a grammar ceiling.
(defthm fn-nlv-next-line-aux-consumes
  (implies (and (true-listp prefix)
                (fn-article-line-okp (fn-article-next-line-aux octets prefix left)))
           (<= (+ 2 (len (fn-article-line-value (fn-article-next-line-aux octets prefix left)))
                    (len (fn-article-line-rest (fn-article-next-line-aux octets prefix left))))
               (+ (len octets) (len prefix))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-article-next-line-aux octets prefix left)
           :in-theory (enable fn-article-next-line-aux fn-article-line-okp
                              fn-article-line-value fn-article-line-rest fn-article-error reverse))))

(defthm fn-nlv-next-line-consumes
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (<= (+ 2 (len (fn-article-line-value (fn-article-next-line octets)))
                    (len (fn-article-line-rest (fn-article-next-line octets))))
               (len octets)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-nlv-next-line-aux-consumes (prefix nil) (left 998)))
           :in-theory (e/d (fn-article-next-line) (fn-article-next-line-aux)))))

(defthm fn-nlv-next-line-aux-no-counter-errors
  (not (member-equal (fn-article-next-line-aux octets prefix left)
        '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets prefix left)
           :in-theory (enable fn-article-next-line-aux fn-article-error))))
(defthm fn-nlv-split-colon-no-counter-errors
  (not (member-equal (fn-article-split-colon-aux line prefix)
        '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))
  :hints (("Goal" :induct (fn-article-split-colon-aux line prefix)
           :in-theory (enable fn-article-split-colon-aux fn-article-error))))
(defthm fn-nlv-new-field-no-counter-errors
  (not (member-equal (fn-article-new-field line)
        '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))
  :hints (("Goal" :use ((:instance fn-nlv-split-colon-no-counter-errors (prefix nil)))
           :in-theory (e/d (fn-article-new-field fn-article-make-field fn-article-error)
                                 (fn-nlv-split-colon-no-counter-errors fn-article-split-colon-aux fn-article-namep fn-article-header-bytes-p)))))

(defthm fn-nlv-ok-no-counter-errors
  (not (member-equal (cons :ok rest)
         '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit)))))

(defthm fn-nlv-next-line-does-not-return-counter-errors
  (not (member-equal (fn-article-next-line octets)
        '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))
  :hints (("Goal" :use ((:instance fn-nlv-next-line-aux-no-counter-errors (prefix nil) (left 998)))
           :in-theory (e/d (fn-article-next-line fn-article-next-line-aux fn-article-error) (fn-nlv-next-line-aux-no-counter-errors)))))

(defthm fn-nlv-parser-counters-covered-by-source
 (implies (and (< (len octets) (nfix lines-left))
               (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits))
               (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits)))
          (not (member-equal (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current names)
             '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit)))))
 :hints (("Goal" :induct (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current names)
          :in-theory (e/d (fn-novlp-parse-lines fn-article-error)
                          (member-equal len fn-nlv-new-field-is-name-tail fn-article-fold-linep fn-article-wspp
                           fn-article-limit-fields fn-article-limit-octets fn-article-next-line fn-article-next-line-aux fn-article-new-field
                           fn-article-line-okp fn-article-line-value fn-article-line-rest
                           fn-article-field-closedp fn-article-add-fold fn-novlp-add-field fn-novlp-normalize)))))

(defthm fn-nlv-preflight-bounds-length
  (implies (fn-cbor-at-mostp octets bound) (<= (len octets) (nfix bound)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-cbor-at-mostp octets bound)
           :in-theory (enable fn-cbor-at-mostp))))

(defthm fn-nlv-widest-projection-never-counter-error
  (not (member-equal (fn-novlp-parse octets)
        '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))
  :hints (("Goal" :use ((:instance fn-nlv-parser-counters-covered-by-source
                          (limits *fn-article-ceiling-limits*) (lines-left (+ 1 *fn-article-max-octets*))
                          (header-bytes 0) (nfields 0)
                          (columns (fn-novlp-columns nil *fn-novlp-names*)) (current nil) (names *fn-novlp-names*)))
           :in-theory (e/d (fn-novlp-parse fn-novlp-parse-under fn-article-error
                            fn-article-limit-fields fn-article-limit-lines fn-article-limit-octets)
                           (fn-novlp-parse-lines fn-novlp-columns fn-cbor-at-mostp fn-cbor-octet-listp
                            fn-nlv-parser-counters-covered-by-source fn-novlp-parse-under-is-parser-projection
                            fn-novlp-parse-is-parser-projection)))))

(defthm fn-nlv-projection-counter-errors-unfolds
  (equal (member-equal (fn-novlp-result parsed names)
          '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit)))
         (member-equal parsed
          '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))
  :hints (("Goal" :in-theory (e/d (fn-novlp-result fn-article-result-okp)
                                 (fn-novlp-normalize fn-novlp-columns fn-article-fields
                                  fn-article-result-article)))))

(defthm fn-nlv-actual-parser-never-counter-error
  (not (member-equal (fn-article-parse octets)
        '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))
  :hints (("Goal" :use fn-nlv-widest-projection-never-counter-error
           :in-theory (disable fn-nlv-widest-projection-never-counter-error
                               fn-article-parse fn-novlp-parse fn-novlp-result member-equal))))
