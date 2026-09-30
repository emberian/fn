(in-package "ACL2")
(include-book "../../books/legacy-parser-validity")
; Literal component witnesses. This is not the full header/parser simulation.
(defconst *nlvt-line* '(83 117 98 106 101 99 116 58 32 120 13 10))
(defconst *nlvt-open* (fn-nlv-run *nlvt-line* (fn-lpc-header-begin) 0 7 11))
; Actual source-reachable state, complete unconditional control commutation.
(assert-event
 (and (equal (fn-lpc-at 0 *nlvt-open*) :start)
      (equal (fn-nlv-control (fn-lpc-header-byte *nlvt-open* 32 12 7 11))
             (fn-nlv-control-byte (fn-nlv-control *nlvt-open*) 32))))
; Body positive and sole-hypothesis removal; NUL/255 are accepted by the
; article body grammar, while line-count facts intentionally differ.
(defconst *nlvt-body* '(0 255 13 10 120))
(defconst *nlvt-body-state* (fn-nlv-run '(13 10) *nlvt-open* 12 7 11))
(assert-event
 (and (equal (fn-lpc-at 0 *nlvt-body-state*) :body)
      (equal (equal (fn-lpc-at 0 (fn-nlv-run *nlvt-body* *nlvt-body-state* 14 7 11)) :body)
             (fn-article-body-crlfp *nlvt-body*))))
; Corrupted-phase removal, not a source-reachable positive.
(assert-event
 (let ((s (fn-lpc-header-bad *nlvt-body-state*)))
  (and (not (equal (fn-lpc-at 0 s) :body))
       (not (equal (equal (fn-lpc-at 0 (fn-nlv-run *nlvt-body* s 14 7 11)) :body)
                   (fn-article-body-crlfp *nlvt-body*))))))
; New-field theorem: full antecedent/conclusion, then each hypothesis removed.
(assert-event (and
 (fn-article-namep '(83 117 98 106 101 99 116))
 (or (not nil) nil)
 (fn-article-header-bytes-p '(32 120))
 (or (not (consp '(32 120))) (fn-article-wspp (car '(32 120))))
 (<= (+ (len '(83 117 98 106 101 99 116)) 1 (len '(32 120))) *fn-article-max-line-octets*)
 (equal (fn-nlv-control-run (append '(83 117 98 106 101 99 116) (cons 58 (append '(32 120) '(13 10))))
                          (list :start 0 nil nil :plain))
                   (list :start 0 t (and (fn-article-has-vcharp '(32 120)) t) :plain))))
(assert-event (and
 (not (fn-article-namep nil))
 (or (not nil) nil)
 (fn-article-header-bytes-p '(32 120))
 (or (not (consp '(32 120))) (fn-article-wspp (car '(32 120))))
 (<= (+ (len nil) 1 (len '(32 120))) *fn-article-max-line-octets*)
 (not (equal (fn-nlv-control-run (append nil (cons 58 (append '(32 120) '(13 10))))
                          (list :start 0 nil nil :plain))
                   (list :start 0 t (and (fn-article-has-vcharp '(32 120)) t) :plain)))))
(assert-event (and
 (fn-article-namep '(83 117 98 106 101 99 116))
 (not (or (not t) nil))
 (fn-article-header-bytes-p '(32 120))
 (or (not (consp '(32 120))) (fn-article-wspp (car '(32 120))))
 (<= (+ (len '(83 117 98 106 101 99 116)) 1 (len '(32 120))) *fn-article-max-line-octets*)
 (not (equal (fn-nlv-control-run (append '(83 117 98 106 101 99 116) (cons 58 (append '(32 120) '(13 10))))
                          (list :start 0 t nil :plain))
                   (list :start 0 t (and (fn-article-has-vcharp '(32 120)) t) :plain)))))
(assert-event (and
 (fn-article-namep '(83 117 98 106 101 99 116))
 (or (not nil) nil)
 (not (fn-article-header-bytes-p '(32 0)))
 (or (not (consp '(32 0))) (fn-article-wspp (car '(32 0))))
 (<= (+ (len '(83 117 98 106 101 99 116)) 1 (len '(32 0))) *fn-article-max-line-octets*)
 (not (equal (fn-nlv-control-run (append '(83 117 98 106 101 99 116) (cons 58 (append '(32 0) '(13 10))))
                          (list :start 0 nil nil :plain))
                   (list :start 0 t (and (fn-article-has-vcharp '(32 0)) t) :plain)))))
(assert-event (and
 (fn-article-namep '(83 117 98 106 101 99 116))
 (or (not nil) nil)
 (fn-article-header-bytes-p '(120))
 (not (or (not (consp '(120))) (fn-article-wspp (car '(120)))))
 (<= (+ (len '(83 117 98 106 101 99 116)) 1 (len '(120))) *fn-article-max-line-octets*)
 (not (equal (fn-nlv-control-run (append '(83 117 98 106 101 99 116) (cons 58 (append '(120) '(13 10))))
                          (list :start 0 nil nil :plain))
                   (list :start 0 t (and (fn-article-has-vcharp '(120)) t) :plain)))))
(defun nlvt-repeat (n) (if (zp n) nil (cons 120 (nlvt-repeat (1- n)))))
(defconst *nlvt-long-value* (cons 32 (nlvt-repeat 997)))
(assert-event (and
 (fn-article-namep '(83))
 (or (not nil) nil)
 (fn-article-header-bytes-p *nlvt-long-value*)
 (or (not (consp *nlvt-long-value*)) (fn-article-wspp (car *nlvt-long-value*)))
 (not (<= (+ (len '(83)) 1 (len *nlvt-long-value*)) *fn-article-max-line-octets*))
 (not (equal (fn-nlv-control-run (append '(83) (cons 58 (append *nlvt-long-value* '(13 10))))
                          (list :start 0 nil nil :plain))
                   (list :start 0 t (and (fn-article-has-vcharp *nlvt-long-value*) t) :plain)))))
; Fold theorem: positive visible and whitespace-only lines; every retained hypothesis checked.
(assert-event (and
 (fn-article-header-bytes-p '(32 120))
 (fn-article-wspp (car '(32 120)))
 (booleanp t)
 (<= (len '(32 120)) *fn-article-max-line-octets*)
 (equal (fn-nlv-control-run (append '(32 120) '(13 10)) (list :start 0 t t :plain))
                  (if (fn-article-has-vcharp '(32 120)) (list :start 0 t t :fold-visible)
                    (list :bad (len '(32 120)) t t :fold-empty)))))
(assert-event (and
 (fn-article-header-bytes-p '(32 9))
 (fn-article-wspp (car '(32 9)))
 (booleanp t)
 (<= (len '(32 9)) *fn-article-max-line-octets*)
 (equal (fn-nlv-control-run (append '(32 9) '(13 10)) (list :start 0 t t :plain))
                  (if (fn-article-has-vcharp '(32 9)) (list :start 0 t t :fold-visible)
                    (list :bad (len '(32 9)) t t :fold-empty)))))
(assert-event (and
 (not (fn-article-header-bytes-p '(32 0)))
 (fn-article-wspp (car '(32 0)))
 (booleanp t)
 (<= (len '(32 0)) *fn-article-max-line-octets*)
 (not (equal (fn-nlv-control-run (append '(32 0) '(13 10)) (list :start 0 t t :plain))
                  (if (fn-article-has-vcharp '(32 0)) (list :start 0 t t :fold-visible)
                    (list :bad (len '(32 0)) t t :fold-empty))))))
(assert-event (and
 (fn-article-header-bytes-p '(120))
 (not (fn-article-wspp (car '(120))))
 (booleanp t)
 (<= (len '(120)) *fn-article-max-line-octets*)
 (not (equal (fn-nlv-control-run (append '(120) '(13 10)) (list :start 0 t t :plain))
                  (if (fn-article-has-vcharp '(120)) (list :start 0 t t :fold-visible)
                    (list :bad (len '(120)) t t :fold-empty))))))
(assert-event (and
 (fn-article-header-bytes-p '(32 9))
 (fn-article-wspp (car '(32 9)))
 (not (booleanp 7))
 (<= (len '(32 9)) *fn-article-max-line-octets*)
 (not (equal (fn-nlv-control-run (append '(32 9) '(13 10)) (list :start 0 t 7 :plain))
                  (if (fn-article-has-vcharp '(32 9)) (list :start 0 t t :fold-visible)
                    (list :bad (len '(32 9)) t 7 :fold-empty))))))
(defconst *nlvt-long-fold* (cons 32 (nlvt-repeat 998)))
(assert-event (and
 (fn-article-header-bytes-p *nlvt-long-fold*)
 (fn-article-wspp (car *nlvt-long-fold*))
 (booleanp t)
 (not (<= (len *nlvt-long-fold*) *fn-article-max-line-octets*))
 (not (equal (fn-nlv-control-run (append *nlvt-long-fold* '(13 10)) (list :start 0 t t :plain))
                  (if (fn-article-has-vcharp *nlvt-long-fold*) (list :start 0 t t :fold-visible)
                    (list :bad (len *nlvt-long-fold*) t t :fold-empty))))))

; Full actual physical-line grammar theorem: every antecedent and conclusion.

; ordinary field
(assert-event
 (let ((line '(83 58 32 120)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; full ftext endpoints
(assert-event
 (let ((line '(33 126 58 9 120)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; open empty value
(assert-event
 (let ((line '(83 58)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; missing colon
(assert-event
 (let ((line '(83)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; empty name
(assert-event
 (let ((line '(58 32 120)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; invalid name
(assert-event
 (let ((line '(83 32 58 32 120)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; non-WSP first value
(assert-event
 (let ((line '(83 58 120)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; NUL header byte
(assert-event
 (let ((line '(83 58 32 0)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; non-ASCII header byte
(assert-event
 (let ((line '(83 58 32 255)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; orphan continuation
(assert-event
 (let ((line '(32 120)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; exactly 998
(assert-event
 (let ((line (append '(83 58 32) (nlvt-repeat 995))) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; 999 octets
(assert-event
 (let ((line (append '(83 58 32) (nlvt-repeat 996))) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; reachable continuation
(assert-event
 (let ((line '(32 120)) (s *nlvt-open*))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; whitespace-only fold after visible field
(assert-event
 (let ((line '(32 9)) (s *nlvt-open*))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; invalid fold byte
(assert-event
 (let ((line '(32 255)) (s *nlvt-open*))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad)))))

; phase removal, source-reachable body state
(assert-event
 (let ((line '(83 58 32 120)) (s *nlvt-body-state*))
  (and (not (equal (fn-lpc-at 0 s) :start))
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (fn-nlv-physicalp line)
       (not (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad))))))

; corrupted-state length removal; other hypotheses hold
(assert-event
 (let ((line '(83 58 32 120)) (s (fn-lpc-put 1 998 (fn-lpc-header-begin))))
  (and (equal (fn-lpc-at 0 s) :start)
       (not (equal (nfix (fn-lpc-at 1 s)) 0))
       (consp line)
       (fn-nlv-physicalp line)
       (not (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad))))))

; nonempty removal: separator enters body
(assert-event
 (let ((line nil) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (not (consp line))
       (fn-nlv-physicalp line)
       (not (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad))))))

; physical-line removal: two valid physical lines
(assert-event
 (let ((line '(83 58 32 120 13 10 84 58 32 121)) (s (fn-lpc-header-begin)))
  (and (equal (fn-lpc-at 0 s) :start)
       (equal (nfix (fn-lpc-at 1 s)) 0)
       (consp line)
       (not (fn-nlv-physicalp line))
       (not (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13 10)) s 0 7 11)) (if (and (<= (len line) *fn-article-max-line-octets*)
                    (if (fn-article-wspp (car line))
                        (and (fn-lpc-at 2 s) (fn-article-fold-linep line))
                      (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
                           (fn-article-line-okp (fn-article-new-field line)))))
               :start :bad))))))

; separator plus opaque binary body
(assert-event (let ((body '(0 255 13 10 120)) (s *nlvt-open*))
 (and (equal (fn-lpc-at 0 s) :start)
      (equal (equal (fn-lpc-at 0 (fn-nlv-run (append '(13 10) body) s 0 7 11)) :body) (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)) (fn-article-body-crlfp body))))))

; separator then malformed body
(assert-event (let ((body '(0 10)) (s *nlvt-open*))
 (and (equal (fn-lpc-at 0 s) :start)
      (equal (equal (fn-lpc-at 0 (fn-nlv-run (append '(13 10) body) s 0 7 11)) :body) (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)) (fn-article-body-crlfp body))))))

; unclosed field refuses separator
(assert-event (let ((body '(0)) (s (fn-nlv-run '(83 58 13 10) (fn-lpc-header-begin) 0 7 11)))
 (and (equal (fn-lpc-at 0 s) :start)
      (equal (equal (fn-lpc-at 0 (fn-nlv-run (append '(13 10) body) s 0 7 11)) :body) (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)) (fn-article-body-crlfp body))))))

; separator phase removal: reachable bad state
(assert-event (let ((body '(0)) (s (fn-nlv-run '(0) (fn-lpc-header-begin) 0 7 11)))
 (and (not (equal (fn-lpc-at 0 s) :start))
      (not (equal (equal (fn-lpc-at 0 (fn-nlv-run (append '(13 10) body) s 0 7 11)) :body) (and (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)) (fn-article-body-crlfp body)))))))

; unfinished physical header and trailing CR
(assert-event (let ((line '(83 58 32 120)) (s (fn-lpc-header-begin)))
 (and (equal (fn-lpc-at 0 s) :start)
      (fn-nlv-physicalp line)
      (and (not (equal (fn-lpc-at 0 (fn-nlv-run line s 0 7 11)) :body)) (not (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13)) s 0 7 11)) :body))))))

; unfinished phase removal: reachable body
(assert-event (let ((line '(120)) (s *nlvt-body-state*))
 (and (not (equal (fn-lpc-at 0 s) :start))
      (fn-nlv-physicalp line)
      (not (and (not (equal (fn-lpc-at 0 (fn-nlv-run line s 0 7 11)) :body)) (not (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13)) s 0 7 11)) :body)))))))

; unfinished physical-prefix removal: complete separator
(assert-event (let ((line '(13 10)) (s (fn-lpc-header-begin)))
 (and (equal (fn-lpc-at 0 s) :start)
      (not (fn-nlv-physicalp line))
      (not (and (not (equal (fn-lpc-at 0 (fn-nlv-run line s 0 7 11)) :body)) (not (equal (fn-lpc-at 0 (fn-nlv-run (append line '(13)) s 0 7 11)) :body)))))))

; bare LF remains rejected through arbitrary suffix
(assert-event (let ((line '(83 58 32 120)) (suffix '(13 10 0)) (s (fn-lpc-header-begin)))
 (and (equal (fn-lpc-at 0 s) :start)
      (fn-nlv-physicalp line)
      (equal (fn-lpc-at 0 (fn-nlv-run (append line (cons 10 suffix)) s 0 7 11)) :bad))))

; bare LF phase removal: reachable CR-start accepts LF
(assert-event (let ((line nil) (suffix '(0)) (s (fn-nlv-run '(13) (fn-lpc-header-begin) 0 7 11)))
 (and (not (equal (fn-lpc-at 0 s) :start))
      (fn-nlv-physicalp line)
      (not (equal (fn-lpc-at 0 (fn-nlv-run (append line (cons 10 suffix)) s 0 7 11)) :bad)))))

; bare LF physical-prefix removal: CR followed by LF is valid
(assert-event (let ((line '(13)) (suffix '(0)) (s (fn-lpc-header-begin)))
 (and (equal (fn-lpc-at 0 s) :start)
      (not (fn-nlv-physicalp line))
      (not (equal (fn-lpc-at 0 (fn-nlv-run (append line (cons 10 suffix)) s 0 7 11)) :bad)))))

; bare CR rejects from arbitrary header/body prefix and any state
(assert-event (let ((prefix '(13 10 0 255)) (byte 0) (suffix '(13 10 120)) (s (fn-lpc-header-begin)))
 (and (not (equal byte 10))
      (equal (fn-lpc-at 0 (fn-nlv-run (append prefix (cons 13 (cons byte suffix))) s 0 7 11)) :bad))))

; bare CR sole-hypothesis removal: CRLF valid body separator
(assert-event (let ((prefix nil) (byte 10) (suffix '(0)) (s (fn-lpc-header-begin)))
 (and (not (not (equal byte 10)))
      (not (equal (fn-lpc-at 0 (fn-nlv-run (append prefix (cons 13 (cons byte suffix))) s 0 7 11)) :bad)))))

; counter domination: nonempty successful article
(assert-event (let ((octets '(83 58 32 120 13 10 13 10 0)) (limits '(100 100 100)) (lines-left 100)
 (header-bytes 0) (nfields 0) (columns nil) (current nil) (names *fn-novlp-names*))
 (and (< (len octets) (nfix lines-left))
      (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits))
      (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits))
      (not (member-equal (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current names) '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit)))))))

; counter line-fuel removal; both other bounds hold
(assert-event (let ((octets '(83 58 32 120 13 10 13 10 0)) (limits '(100 100 100)) (lines-left 0)
 (header-bytes 0) (nfields 0) (columns nil) (current nil) (names *fn-novlp-names*))
 (and (not (< (len octets) (nfix lines-left)))
      (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits))
      (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits))
      (not (not (member-equal (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current names) '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))))))

; counter octet-budget removal; both other bounds hold
(assert-event (let ((octets '(83 58 32 120 13 10 13 10 0)) (limits '(100 100 0)) (lines-left 100)
 (header-bytes 0) (nfields 0) (columns nil) (current nil) (names *fn-novlp-names*))
 (and (< (len octets) (nfix lines-left))
      (not (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits)))
      (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits))
      (not (not (member-equal (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current names) '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))))))

; counter field-budget removal; both other bounds hold
(assert-event (let ((octets '(83 58 32 120 13 10 13 10 0)) (limits '(0 100 100)) (lines-left 100)
 (header-bytes 0) (nfields 0) (columns nil) (current nil) (names *fn-novlp-names*))
 (and (< (len octets) (nfix lines-left))
      (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits))
      (not (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits)))
      (not (not (member-equal (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current names) '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))))))

; Unconditional widest logical projection: nonempty positive, independent success.
(assert-event (and (fn-article-result-okp (fn-article-parse '(83 58 32 120 13 10 13 10 0)))
 (not (member-equal (fn-novlp-parse '(83 58 32 120 13 10 13 10 0)) '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))))

; Unconditional actual parser at codec ceiling limits: nonempty positive, independent success.
(assert-event (and (fn-article-result-okp (fn-article-parse '(83 58 32 120 13 10 13 10 0)))
 (not (member-equal (fn-article-parse '(83 58 32 120 13 10 13 10 0)) '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))))

; Mutated limits, not a hypothesis removal for an unconditional theorem.
(assert-event (member-equal (fn-article-parse-under '(83 58 32 120 13 10 13 10 0) '(0 100 100)) '((:error :header-lines-limit) (:error :header-fields-limit) (:error :header-octets-limit))))
