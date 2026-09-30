(in-package "ACL2")
(include-book "../../books/legacy-parser-composition")

; Full actual theorem, source-reachable nonempty accepted and malformed inputs.
; ordinary.
(assert-event
 (let ((octets '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 98 111 100 121)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) t))))
; open field completed by fold.
(assert-event
 (let ((octets '(83 117 98 106 101 99 116 58 13 10 32 120 13 10 13 10 0 255)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) t))))
; empty header binary body.
(assert-event
 (let ((octets '(13 10 0 255 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) t))))
; repeated unknown ftext names.
(assert-event
 (let ((octets '(33 58 32 97 13 10 33 58 32 98 13 10 126 58 32 99 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) t))))
; empty field.
(assert-event
 (let ((octets '(83 117 98 106 101 99 116 58 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; whitespace-only fold after visible value.
(assert-event
 (let ((octets '(83 117 98 106 101 99 116 58 32 120 13 10 32 9 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; orphan fold.
(assert-event
 (let ((octets '(32 120 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; malformed name.
(assert-event
 (let ((octets '(83 117 32 98 58 32 120 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; no colon.
(assert-event
 (let ((octets '(83 117 98 106 101 99 116 32 120 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; no post-colon WSP.
(assert-event
 (let ((octets '(83 117 98 106 101 99 116 58 120 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; NUL header.
(assert-event
 (let ((octets '(83 58 32 0 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; nonASCII header.
(assert-event
 (let ((octets '(83 58 32 255 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; bare LF.
(assert-event
 (let ((octets '(83 58 32 120 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; CR nonLF.
(assert-event
 (let ((octets '(83 58 32 120 13 122 13 10 13 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; unfinished line.
(assert-event
 (let ((octets '(83 58 32 120)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; trailing CR.
(assert-event
 (let ((octets '(83 58 32 120 13)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; body bare LF.
(assert-event
 (let ((octets '(83 58 32 120 13 10 13 10 97 10)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))
; body trailing CR.
(assert-event
 (let ((octets '(83 58 32 120 13 10 13 10 97 13)))
  (and (consp octets)
       (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (fn-cbor-octet-listp octets)
       (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
              (fn-article-result-okp (fn-article-parse octets)))
       (equal (fn-article-result-okp (fn-article-parse octets)) nil))))

; Octet-domain removal: framing is valid, but the body contains a non-octet.
(assert-event
 (let ((octets '(13 10 256)))
  (and (fn-cbor-at-mostp octets *fn-article-max-octets*)
       (not (fn-cbor-octet-listp octets))
       (not (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
                   (fn-article-result-okp (fn-article-parse octets)))))))

; Scanner rejection, both retained-hypothesis removals. Phase removal is a
; reachable body state; scanner-success removal is an ordinary complete source.
(assert-event
 (let ((s (fn-lpc-header-begin)) (octets '(83 58 32 120 13)))
  (and (equal (fn-lpc-at 0 s) :start)
       (not (fn-article-line-okp (fn-article-next-line octets)))
       (not (equal (fn-lpc-at 0 (fn-nlv-run octets s 0 7 11)) :body)))))
(assert-event
 (let ((s (fn-nlv-run '(13 10) (fn-lpc-header-begin) 0 7 11)) (octets '(0)))
  (and (not (equal (fn-lpc-at 0 s) :start))
       (not (fn-article-line-okp (fn-article-next-line octets)))
       (not (not (equal (fn-lpc-at 0 (fn-nlv-run octets s 2 7 11)) :body))))))
(assert-event
 (let ((s (fn-lpc-header-begin)) (octets '(83 58 32 120 13 10 13 10 0)))
  (and (equal (fn-lpc-at 0 s) :start)
       (not (not (fn-article-line-okp (fn-article-next-line octets))))
       (not (not (equal (fn-lpc-at 0 (fn-nlv-run octets s 0 7 11)) :body))))))

; Symbolic codec-ceiling removal: proving a finite witness avoids allocating
; more than four billion cons cells merely to evaluate the same witness.
(defun fn-nlpct-zero-body (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 0 (fn-nlpct-zero-body (1- n)))))
(defthm fn-nlpct-zero-body-octets
  (fn-cbor-octet-listp (fn-nlpct-zero-body n))
  :hints (("Goal" :induct (fn-nlpct-zero-body n)
           :in-theory (enable fn-nlpct-zero-body fn-cbor-octet-listp fn-cbor-octetp))))
(defthm fn-nlpct-zero-body-framing
  (fn-article-body-crlfp (fn-nlpct-zero-body n))
  :hints (("Goal" :induct (fn-nlpct-zero-body n)
           :in-theory (enable fn-nlpct-zero-body fn-article-body-crlfp))))
(defthm fn-nlpct-at-most-is-length
  (equal (fn-cbor-at-mostp bytes bound) (<= (len bytes) (nfix bound)))
  :hints (("Goal" :induct (fn-cbor-at-mostp bytes bound) :in-theory (enable fn-cbor-at-mostp))))
(defthm fn-nlpct-zero-body-length
  (equal (len (fn-nlpct-zero-body n)) (nfix n))
  :hints (("Goal" :induct (fn-nlpct-zero-body n) :in-theory (enable fn-nlpct-zero-body))))
(defthm fn-nlpct-codec-ceiling-removal
  (let ((octets (cons 13 (cons 10 (fn-nlpct-zero-body *fn-article-max-octets*)))))
    (and (not (fn-cbor-at-mostp octets *fn-article-max-octets*))
         (fn-cbor-octet-listp octets)
         (not (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
                     (fn-article-result-okp (fn-article-parse octets))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-nlv-actual-separator-body-exact
                   (body (fn-nlpct-zero-body *fn-article-max-octets*))
                   (s (fn-lpc-header-begin)) (pos 0) (h 7) (pin 11)))
           :in-theory
           (e/d (fn-article-parse fn-article-parse-under fn-article-result-okp
                 fn-cbor-octet-listp fn-lpc-header-begin fn-lpc-at)
                (fn-nlv-actual-separator-body-exact fn-nlpct-zero-body (:executable-counterpart fn-nlpct-zero-body)
                 fn-nlv-run fn-nlv-run-phase-is-control-run-phase fn-nlv-run-append
                 fn-article-body-crlfp fn-cbor-at-mostp)))))

(defun fn-nlpct-xs (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 120 (fn-nlpct-xs (1- n)))))
; Exact physical bound, admitted and rejected through the full parser join.
(assert-event
 (let ((octets (append '(83 58 32) (fn-nlpct-xs 995) '(13 10 13 10 0))))
   (and (fn-cbor-at-mostp octets *fn-article-max-octets*) (fn-cbor-octet-listp octets)
        (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
               (fn-article-result-okp (fn-article-parse octets)))
        (fn-article-result-okp (fn-article-parse octets)))))
(assert-event
 (let ((octets (append '(83 58 32) (fn-nlpct-xs 996) '(13 10 13 10 0))))
   (and (fn-cbor-at-mostp octets *fn-article-max-octets*) (fn-cbor-octet-listp octets)
        (equal (equal (fn-lpc-at 0 (fn-nlv-run octets (fn-lpc-header-begin) 0 7 11)) :body)
               (fn-article-result-okp (fn-article-parse octets)))
        (not (fn-article-result-okp (fn-article-parse octets))))))

; Counter-free grammar join: literal positive, then each retained inequality.
(assert-event
 (let ((octets '(83 58 32 120 13 10 13 10 0)) (limits '(20 20 20))
       (lines-left 10) (header-bytes 0) (nfields 0))
  (and (< (len octets) (nfix lines-left))
       (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits))
       (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits))
       (equal (fn-article-result-okp (fn-novlp-parse-lines octets limits lines-left header-bytes nfields nil nil nil))
              (fn-nlpc-accept-lines octets nil))
       (fn-nlpc-accept-lines octets nil))))
(assert-event
 (let ((octets '(83 58 32 120 13 10 13 10 0)) (limits '(20 20 20))
       (lines-left 1) (header-bytes 0) (nfields 0))
  (and (not (< (len octets) (nfix lines-left)))
       (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits))
       (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits))
       (not (equal (fn-article-result-okp (fn-novlp-parse-lines octets limits lines-left header-bytes nfields nil nil nil))
                   (fn-nlpc-accept-lines octets nil))))))
(assert-event
 (let ((octets '(83 58 32 120 13 10 13 10 0)) (limits '(20 20 5))
       (lines-left 10) (header-bytes 0) (nfields 0))
  (and (< (len octets) (nfix lines-left))
       (not (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits)))
       (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits))
       (not (equal (fn-article-result-okp (fn-novlp-parse-lines octets limits lines-left header-bytes nfields nil nil nil))
                   (fn-nlpc-accept-lines octets nil))))))
(assert-event
 (let ((octets '(83 58 32 120 13 10 13 10 0)) (limits '(0 20 20))
       (lines-left 10) (header-bytes 0) (nfields 0))
  (and (< (len octets) (nfix lines-left))
       (<= (+ header-bytes (len octets)) (fn-article-limit-octets limits))
       (not (<= (+ (nfix nfields) (len octets)) (fn-article-limit-fields limits)))
       (not (equal (fn-article-result-okp (fn-novlp-parse-lines octets limits lines-left header-bytes nfields nil nil nil))
                   (fn-nlpc-accept-lines octets nil))))))
; Unconditional byte-machine grammar join from a current field awaiting a fold.
(assert-event
 (let ((octets '(32 120 13 10 13 10 0))
       (current (fn-article-line-value (fn-article-new-field '(83 58)))))
  (and current (consp octets)
       (equal (equal (fn-lpc-at 0
                       (fn-nlv-control-run octets
                         (list :start 0 (and current t)
                           (and (fn-article-has-vcharp (fn-article-field-unfolded-value current)) t)
                           :plain))) :body)
              (fn-nlpc-accept-lines octets current))
       (fn-nlpc-accept-lines octets current))))
