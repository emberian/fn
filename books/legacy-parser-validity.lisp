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

(defthm fn-nlv-control-byte-is-actual-header-byte
  (equal (fn-nlv-control (fn-lpc-header-byte s byte pos h pin))
         (fn-nlv-control-byte (fn-nlv-control s) byte))
  :hints (("Goal" :in-theory
           (e/d (fn-nlv-control fn-nlv-control-byte fn-nlv-phase fn-nlv-value
                 fn-lpc-header-byte fn-lpc-header-bad fn-lpc-value-byte fn-lpc-at)
                (fn-lpc-put fn-lpc-close-fields
                 fn-lpc-name-key fn-lpc-name-step fn-article-header-bytep
                 fn-article-vcharp fn-article-ftextp fn-article-wspp)))))

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
