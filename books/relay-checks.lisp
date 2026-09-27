; fn: the relaying agent's article checks that the transfer decision was
; missing (PRF-236, planning/nntp-gap-inventory-2026-09-26.md T2), and the
; two operator limits the transit hygiene reads (PRF-235, PRF-236).
;
;   the date   RFC 5537 section 3.6 step 2: "examine the Injection-Date
;              header field or, if absent, the Date header field, and reject
;              the article if that date is more than 24 hours into the
;              future.  It MAY reject articles with dates in the future with
;              a smaller margin".  `fn-rck-date-instant' reads an RFC 5322
;              section 3.3 date-time, with the section 4.3 obsolete forms
;              (two- and three-digit years, alphabetic zones, a missing
;              day-of-week, comments and folding white space), to seconds
;              since 1970-01-01T00:00:00Z.  A field that is not a date-time is
;              refused by step 4's "MAY reject any article that contains
;              header fields that do not have valid contents" (INN refuses it
;              as well).  The margin is the operator's `relay-date-skew'
;              limit in seconds, never more than the RFC's 24 hours.
;   the Path   RFC 5536 section 3.1 makes Path mandatory and section 3.1.5
;              gives its grammar; RFC 5537 section 3.6 step 4: "SHOULD
;              reject any article that does not include all the mandatory
;              header fields.  It MAY reject any article that contains
;              header fields that do not have valid contents."
;              `fn-rck-path-wellformedp' is the grammar over the entries
;              books/path.lisp splits: a first <path-identity>, then
;              identities, empty <diag-match> entries and "."-diagnostics,
;              and a <path-nodot> <tail-entry>.
;
; Every reader is total, structural and linear in the field; no octet goes
; through the Lisp reader.  The field values arrive unfolded from
; books/article.lisp, whose parser bounds the work per article.
;
; This book owns the prefix `fn-rck-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "path")
(include-book "config")

; -----------------------------------------------------------------------------
; Octet classes

(defun fn-rck-digitp (b)
  (declare (xargs :guard t))
  (and (integerp b) (<= 48 b) (<= b 57)))

(defun fn-rck-alphap (b)
  (declare (xargs :guard t))
  (and (integerp b)
       (or (and (<= 65 b) (<= b 90)) (and (<= 97 b) (<= b 122)))))

(defun fn-rck-lower (b)
  (declare (xargs :guard t))
  (if (and (integerp b) (<= 65 b) (<= b 90)) (+ b 32) b))

(defun fn-rck-wspp (b)
  (declare (xargs :guard t))
  (and (member-equal b '(32 9 13 10)) t))

; -----------------------------------------------------------------------------
; The lexer: numbers, words and single punctuation octets; white space and
; comments (RFC 5322 section 3.2.2, nested, with quoted-pairs) separate
; tokens and are dropped.  A token is (:num . digits), (:word . lower-case
; letters) or (:punct . octet); :bad for an unbalanced comment.

(defun fn-rck-rev (xs acc)
  (declare (xargs :guard t))
  (if (consp xs) (fn-rck-rev (cdr xs) (cons (car xs) acc)) acc))

(defun fn-rck-flush (kind cur acc)
  (declare (xargs :guard t))
  (if kind (cons (cons kind (fn-rck-rev cur nil)) acc) acc))

(defun fn-rck-lex (xs depth kind cur acc)
  (declare (xargs :guard (natp depth) :measure (len xs)))
  (cond ((not (consp xs))
         (if (equal depth 0)
             (fn-rck-rev (fn-rck-flush kind cur acc) nil)
           :bad))
        ((< 0 depth)
         (let ((b (car xs)))
           (cond ((equal b 40) (fn-rck-lex (cdr xs) (+ 1 depth) nil nil acc))
                 ((equal b 41) (fn-rck-lex (cdr xs) (- depth 1) nil nil acc))
                 ((and (equal b 92) (consp (cdr xs)))
                  (fn-rck-lex (cddr xs) depth nil nil acc))
                 (t (fn-rck-lex (cdr xs) depth nil nil acc)))))
        (t
         (let ((b (car xs)))
           (cond ((fn-rck-digitp b)
                  (if (equal kind :num)
                      (fn-rck-lex (cdr xs) 0 :num (cons b cur) acc)
                    (fn-rck-lex (cdr xs) 0 :num (list b)
                                (fn-rck-flush kind cur acc))))
                 ((fn-rck-alphap b)
                  (if (equal kind :word)
                      (fn-rck-lex (cdr xs) 0 :word (cons (fn-rck-lower b) cur)
                                  acc)
                    (fn-rck-lex (cdr xs) 0 :word (list (fn-rck-lower b))
                                (fn-rck-flush kind cur acc))))
                 ((fn-rck-wspp b)
                  (fn-rck-lex (cdr xs) 0 nil nil (fn-rck-flush kind cur acc)))
                 ((equal b 40)
                  (fn-rck-lex (cdr xs) 1 nil nil (fn-rck-flush kind cur acc)))
                 ((equal b 41) :bad)
                 (t (fn-rck-lex (cdr xs) 0 nil nil
                                (cons (cons :punct b)
                                      (fn-rck-flush kind cur acc)))))))))

(defun fn-rck-tokens (octets)
  (declare (xargs :guard t))
  (fn-rck-lex octets 0 nil nil nil))

; -----------------------------------------------------------------------------
; Token readers

(defun fn-rck-digits-value (ds acc)
  (declare (xargs :guard (natp acc)))
  (if (consp ds)
      (fn-rck-digits-value (cdr ds)
                           (+ (* 10 acc)
                              (if (fn-rck-digitp (car ds)) (- (car ds) 48) 0)))
    acc))

(defthm fn-rck-digits-value-natp
  (implies (natp acc) (natp (fn-rck-digits-value ds acc)))
  :rule-classes (:rewrite :type-prescription))

(defun fn-rck-num-tokenp (tok)
  (declare (xargs :guard t))
  (and (consp tok) (equal (car tok) :num) (consp (cdr tok))
       (true-listp (cdr tok))))

(defun fn-rck-num-width (tok)
  (declare (xargs :guard t))
  (if (fn-rck-num-tokenp tok) (len (cdr tok)) 0))

(defun fn-rck-num-value (tok)
  (declare (xargs :guard t))
  (if (fn-rck-num-tokenp tok) (fn-rck-digits-value (cdr tok) 0) 0))

(defthm fn-rck-num-value-natp
  (natp (fn-rck-num-value tok))
  :rule-classes :type-prescription)

(defun fn-rck-word-tokenp (tok word)
  (declare (xargs :guard t))
  (and (consp tok) (equal (car tok) :word) (equal (cdr tok) word)))

(defun fn-rck-punct-tokenp (tok b)
  (declare (xargs :guard t))
  (and (consp tok) (equal (car tok) :punct) (equal (cdr tok) b)))

(defconst *fn-rck-day-names*
  '((109 111 110) (116 117 101) (119 101 100) (116 104 117) (102 114 105)
    (115 97 116) (115 117 110)))                  ; mon tue wed thu fri sat sun

(defconst *fn-rck-month-names*
  '((106 97 110) (102 101 98) (109 97 114) (97 112 114) (109 97 121)
    (106 117 110) (106 117 108) (97 117 103) (115 101 112) (111 99 116)
    (110 111 118) (100 101 99)))                  ; jan .. dec

(defun fn-rck-month-index (word names i)
  (declare (xargs :guard (natp i)))
  (if (consp names)
      (if (equal word (car names)) i (fn-rck-month-index word (cdr names) (+ 1 i)))
    nil))

(defun fn-rck-month-of (tok)
  (declare (xargs :guard t))
  (if (and (consp tok) (equal (car tok) :word))
      (fn-rck-month-index (cdr tok) *fn-rck-month-names* 1)
    nil))

(defun fn-rck-day-name-tokenp (tok)
  (declare (xargs :guard t))
  (and (consp tok) (equal (car tok) :word)
       (member-equal (cdr tok) *fn-rck-day-names*) t))

; RFC 5322 section 4.3 obs-zone, in minutes east of UTC.  The military
; letters "SHOULD all be considered equivalent to "-0000"" there, so they
; read as UTC.
(defconst *fn-rck-obs-zones*
  '(((117 116) . 0) ((103 109 116) . 0)               ; ut gmt
    ((101 115 116) . -300) ((101 100 116) . -240)     ; est edt
    ((99 115 116) . -360) ((99 100 116) . -300)       ; cst cdt
    ((109 115 116) . -420) ((109 100 116) . -360)     ; mst mdt
    ((112 115 116) . -480) ((112 100 116) . -420)))   ; pst pdt

(defun fn-rck-obs-zone-minutes (word)
  (declare (xargs :guard t))
  (let ((hit (assoc-equal word *fn-rck-obs-zones*)))
    (cond (hit (cdr hit))
          ((and (consp word) (null (cdr word)) (integerp (car word))
                (<= 97 (car word)) (<= (car word) 122)
                (not (equal (car word) 106)))          ; any letter but j
           0)
          (t nil))))

; The year of RFC 5322 section 4.3: two digits below 50 are 20xx, other two
; and three digit years add 1900.
(defun fn-rck-year-of (tok)
  (declare (xargs :guard t))
  (let ((w (fn-rck-num-width tok)) (v (fn-rck-num-value tok)))
    (cond ((equal w 2) (if (< v 50) (+ 2000 v) (+ 1900 v)))
          ((equal w 3) (+ 1900 v))
          ((<= 4 w) v)
          (t nil))))

; -----------------------------------------------------------------------------
; Civil time

(defun fn-rck-days-from-civil (y m d)
  ; Days from 1970-01-01 of the proleptic Gregorian date (y m d).
  (declare (xargs :guard (and (integerp y) (integerp m) (integerp d))))
  (let* ((y2 (if (<= m 2) (- y 1) y))
         (era (floor y2 400))
         (yoe (- y2 (* era 400)))
         (mp (if (< 2 m) (- m 3) (+ m 9)))
         (doy (+ (floor (+ (* 153 mp) 2) 5) (- d 1)))
         (doe (+ (* yoe 365) (floor yoe 4) (- (floor yoe 100)) doy)))
    (+ (* era 146097) doe -719468)))

; (y m d hh mm ss zone-minutes) of a token list, or nil.
(defun fn-rck-zone-minutes (ts)
  ; The zone and nothing after it.
  (declare (xargs :guard t))
  (cond ((and (consp ts) (consp (cdr ts)) (null (cddr ts))
              (or (fn-rck-punct-tokenp (car ts) 43)
                  (fn-rck-punct-tokenp (car ts) 45))
              (equal (fn-rck-num-width (cadr ts)) 4))
         (let* ((v (fn-rck-num-value (cadr ts)))
                (hh (floor v 100)) (mm (mod v 100))
                (mins (+ (* 60 hh) mm)))
           (if (< mm 60)
               (if (fn-rck-punct-tokenp (car ts) 45) (- mins) mins)
             nil)))
        ((and (consp ts) (null (cdr ts)) (consp (car ts))
              (equal (car (car ts)) :word))
         (fn-rck-obs-zone-minutes (cdr (car ts))))
        (t nil)))

(defun fn-rck-small-nump (tok lo hi)
  ; A one- or two-digit number in [lo, hi].
  (declare (xargs :guard (and (integerp lo) (integerp hi))))
  (and (member-equal (fn-rck-num-width tok) '(1 2))
       (<= lo (fn-rck-num-value tok))
       (<= (fn-rck-num-value tok) hi)))

(defun fn-rck-time-fields (ts)
  ; hour ":" minute [":" second] zone  ->  (hh mm ss zone) or nil
  (declare (xargs :guard t))
  (if (and (consp ts) (consp (cdr ts)) (consp (cddr ts))
           (fn-rck-small-nump (car ts) 0 23)
           (fn-rck-punct-tokenp (cadr ts) 58)
           (equal (fn-rck-num-width (caddr ts)) 2)
           (<= (fn-rck-num-value (caddr ts)) 59))
      (let ((rest (cdddr ts)))
        (if (and (consp rest) (consp (cdr rest))
                 (fn-rck-punct-tokenp (car rest) 58))
            (let ((zone (fn-rck-zone-minutes (cddr rest))))
              (if (and (equal (fn-rck-num-width (cadr rest)) 2)
                       (<= (fn-rck-num-value (cadr rest)) 60)
                       (integerp zone))
                  (list (fn-rck-num-value (car ts))
                        (fn-rck-num-value (caddr ts))
                        (fn-rck-num-value (cadr rest)) zone)
                nil))
          (let ((zone (fn-rck-zone-minutes rest)))
            (if (integerp zone)
                (list (fn-rck-num-value (car ts)) (fn-rck-num-value (caddr ts))
                      0 zone)
              nil))))
    nil))

(defthm fn-rck-time-fields-true-listp
  (true-listp (fn-rck-time-fields ts))
  :rule-classes :type-prescription)

(in-theory (disable fn-rck-time-fields fn-rck-small-nump fn-rck-year-of
                    fn-rck-month-of fn-rck-day-name-tokenp fn-rck-punct-tokenp))

(defun fn-rck-date-fields (ts)
  ; [day-name ","] day month year time  ->  (y m d hh mm ss zone) or nil
  (declare (xargs :guard t))
  (let ((ts (if (and (consp ts) (consp (cdr ts))
                     (fn-rck-day-name-tokenp (car ts))
                     (fn-rck-punct-tokenp (cadr ts) 44))
                (cddr ts)
              ts)))
    (if (and (consp ts) (consp (cdr ts)) (consp (cddr ts))
             (fn-rck-small-nump (car ts) 1 31)
             (fn-rck-month-of (cadr ts))
             (fn-rck-year-of (caddr ts)))
        (let ((tm (fn-rck-time-fields (cdddr ts))))
          (if tm
              (list (fn-rck-year-of (caddr ts)) (fn-rck-month-of (cadr ts))
                    (fn-rck-num-value (car ts))
                    (car tm) (cadr tm) (caddr tm) (cadddr tm))
            nil))
      nil)))

; KEYSTONE subject.  Seconds since 1970-01-01T00:00:00Z of an RFC 5322
; date-time field value (octets), or nil when it is not one.
(defun fn-rck-date-instant (octets)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-rck-date-fields)))))
  (let ((ts (fn-rck-tokens octets)))
    (if (true-listp ts)
        (let ((f (fn-rck-date-fields ts)))
          (if (and (true-listp f) (equal (len f) 7)
                   (integerp (nth 0 f)) (integerp (nth 1 f)) (integerp (nth 2 f))
                   (integerp (nth 3 f)) (integerp (nth 4 f)) (integerp (nth 5 f))
                   (integerp (nth 6 f)))
              (- (+ (* 86400 (fn-rck-days-from-civil (nth 0 f) (nth 1 f) (nth 2 f)))
                    (* 3600 (nth 3 f)) (* 60 (nth 4 f)) (nth 5 f))
                 (* 60 (nth 6 f)))
            nil))
      nil)))

; -----------------------------------------------------------------------------
; The article's date: Injection-Date, or if absent Date (RFC 5537 3.6 step 2).
; A field present more than once has no single value and reads as no date.

(defun fn-rck-date-field-value (article)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (if (consp (fn-article-get-headers article *fn-path-injection-date-name*))
      (fn-path-single-field-value article *fn-path-injection-date-name*)
    (fn-path-single-field-value article *fn-path-date-name*)))

(defun fn-rck-article-instant (article)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (fn-rck-date-instant (fn-rck-date-field-value article)))

; -----------------------------------------------------------------------------
; The operator's limits (`:set-limit' rows; `policy set SLOT N',
; books/native-admin.lisp).  Neither has a data ceiling of fn's own: the skew
; is capped by the RFC's MUST, the capacity by nothing but the operator.

(defconst *fn-rck-skew-slot* "relay-date-skew")
(defconst *fn-rck-capacity-slot* "refused-offer-capacity")
(defconst *fn-rck-require-path-slot* "relay-require-path")
(defconst *fn-rck-rfc-skew* 86400)
; 2000-01-01T00:00:00Z in seconds since 1970 (10957 days): the DTN epoch of
; books/clock.lisp's wall reading.
(defconst *fn-rck-dtn-epoch-unix-seconds* 946684800)
(defconst *fn-rck-default-capacity* 4096)

(defun fn-rck-limit-row (cfg slot)
  (declare (xargs :guard t))
  (fn-cfg-row-lookup (fn-cfg-limits (fn-cfg-value cfg)) slot))

; The margin in seconds: the operator's value, at most 24 hours; 24 hours
; when the operator set none.
(defun fn-rck-skew (cfg)
  (declare (xargs :guard t))
  (let ((row (fn-rck-limit-row cfg *fn-rck-skew-slot*)))
    (if (consp row)
        (min (nfix (fn-cfg-limit-value row)) *fn-rck-rfc-skew*)
      *fn-rck-rfc-skew*)))

(defthm fn-rck-skew-within-the-rfc
  (and (natp (fn-rck-skew cfg))
       (<= (fn-rck-skew cfg) *fn-rck-rfc-skew*))
  :rule-classes ((:rewrite :corollary (natp (fn-rck-skew cfg)))
                 (:linear :corollary (<= (fn-rck-skew cfg) 86400))))

(defun fn-rck-refused-capacity (cfg)
  (declare (xargs :guard t))
  (let ((row (fn-rck-limit-row cfg *fn-rck-capacity-slot*)))
    (if (consp row) (nfix (fn-cfg-limit-value row)) *fn-rck-default-capacity*)))

; 1 refuses a relayed article with no Path (RFC 5537 section 3.6 step 4);
; 0 or no row accepts it (books/peer-inbound.lisp fn-peer-path-missingp says
; why that is the default).
(defun fn-rck-require-pathp (cfg)
  (declare (xargs :guard t))
  (let ((row (fn-rck-limit-row cfg *fn-rck-require-path-slot*)))
    (and (consp row) (equal (nfix (fn-cfg-limit-value row)) 1))))

(defun fn-rck-limit-slotp (slot)
  (declare (xargs :guard t))
  (and (member-equal slot (list *fn-rck-skew-slot* *fn-rck-capacity-slot*
                                *fn-rck-require-path-slot*))
       t))

; What the operator may write: the skew within the RFC's MUST, a capacity the
; configuration's row can carry (every limit row is under
; `fn-cfg-limit-ceiling', the codec's own width).
(defun fn-rck-limit-valuep (slot n)
  (declare (xargs :guard t))
  (and (natp n)
       (<= n (fn-cfg-limit-ceiling slot))
       (or (not (equal slot *fn-rck-skew-slot*)) (<= n *fn-rck-rfc-skew*))
       (or (not (equal slot *fn-rck-require-path-slot*)) (<= n 1))))

; RFC 5537 section 3.6 step 2 as a predicate: the article's instant is more
; than SKEW seconds after NOW.  NOW is a natural (seconds) or the check has
; no clock and does not decide.
(defun fn-rck-date-futurep (instant now skew)
  (declare (xargs :guard t))
  (and (integerp instant) (natp now) (natp skew)
       (< (+ now skew) instant)))

; -----------------------------------------------------------------------------
; Path (RFC 5536 section 3.1.5)

(defun fn-rck-nodot-charsp (xs)
  ; 1*( alphanum / "-" / "_" )
  (declare (xargs :guard t))
  (if (consp xs)
      (and (or (fn-rck-digitp (car xs)) (fn-rck-alphap (car xs))
               (equal (car xs) 45) (equal (car xs) 95))
           (fn-rck-nodot-charsp (cdr xs)))
    (null xs)))

(defun fn-rck-nodotp (xs)
  (declare (xargs :guard t))
  (and (consp xs) (fn-rck-nodot-charsp xs)))

(defun fn-rck-diagp (entry)
  ; "." diag-keyword [ "." diag-identity ]: a "." and a letter first.
  (declare (xargs :guard t))
  (and (consp entry) (equal (car entry) 46)
       (consp (cdr entry)) (fn-rck-alphap (cadr entry))))

(defun fn-rck-middle-entryp (entry)
  ; What a <path-list> element may leave between two "!": an identity (with
  ; the deprecated IPv4 diagnostic, which the identity characters admit), the
  ; empty <diag-match>, or a diagnostic.
  (declare (xargs :guard t))
  (or (null entry) (fn-rck-diagp entry) (fn-path-identityp entry)))

(defun fn-rck-entries-okp (entries)
  ; Every entry but the last is a middle entry; the last is the <tail-entry>.
  ; RFC 5536 makes the tail a <path-nodot>; a dotted name there (a site name,
  ; as older software wrote it and fn's own loop tests use) is read as one
  ; too, since the tail is informational and names no relaying agent (RFC
  ; 5537 section 3.2: local policy, liberal in what is accepted).
  (declare (xargs :guard t))
  (if (consp entries)
      (if (consp (cdr entries))
          (and (fn-rck-middle-entryp (car entries))
               (fn-rck-entries-okp (cdr entries)))
        (or (fn-rck-nodotp (car entries)) (fn-path-identityp (car entries))))
    nil))

(defun fn-rck-path-wellformedp (value)
  (declare (xargs :guard t))
  (let ((entries (fn-path-entries value)))
    (and (consp entries)
         (or (null (cdr entries)) (fn-path-identityp (car entries)))
         (fn-rck-entries-okp entries)
         t)))

(deftheory fn-rck-vocabulary
  '((:d fn-rck-lex) (:d fn-rck-tokens) (:d fn-rck-date-fields)
    (:d fn-rck-time-fields) (:d fn-rck-zone-minutes) (:d fn-rck-date-instant)
    (:d fn-rck-date-field-value) (:d fn-rck-article-instant)
    (:d fn-rck-path-wellformedp) (:d fn-rck-entries-okp)
    (:d fn-rck-skew) (:d fn-rck-refused-capacity) (:d fn-rck-limit-row)
    (:d fn-rck-require-pathp)
    (:d fn-rck-days-from-civil)))

(in-theory (disable fn-rck-vocabulary))
