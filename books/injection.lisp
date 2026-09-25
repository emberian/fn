;; fn: RFC 5537 section 3.5 injection of a proto-article.
;
; An injecting agent takes a proto-article from a posting agent and produces
; the exact octets of an article, or refuses it with a reason.  This book is
; that decision.  It is a function of three things and nothing else: the exact
; source octets the posting agent supplied, one host clock observation
; (books/clock.lisp), and a configuration record naming the injecting agent's
; identity, the groups it accepts, and its size bound.  No value here is
; computed by the host: the generated Message-ID, the Injection-Date, the
; Injection-Info and the Path field are built here, and so are the injected
; article's octets.
;
; RFC 5537 section 3.5 item 2 (reject a proto-article with Injection-Info or
; Xref, or one that is not syntactically valid), item 4 (the Newsgroups
; check), item 5 (add Message-ID and Date when absent), item 6 (never alter
; the body, never alter an existing Message-ID) and item 11 (the
; Injection-Date) are the clauses implemented.
;
; Item 11 has three cases, and each is decided here:
;
;   * A proto-article that carries an Injection-Date is refused
;     (:injection-date-present).  This is a local acceptance policy, not an
;     RFC requirement.  Item 11 says only that a supplied Injection-Date MUST
;     NOT be modified or replaced; refusing the article modifies nothing.  fn
;     refuses rather than keeps it for two reasons: item 3 would have fn judge
;     how far that date lies in the past or future, and fn has no date-time
;     parser; and the generated Date below is recognised by its equality with
;     the Injection-Date fn wrote, which a poster's Injection-Date would not be.
;   * Both Date and Message-ID supplied: no Injection-Date is added (item 11's
;     MUST NOT; the proto-article may have been injected more than once by a
;     posting agent).  The injected article then does not depend on the clock.
;   * Otherwise the Injection-Date is added, with the current clock reading.
;
; The injected block (fn-inj-prefix) is Path, then the generated fields in a
; fixed order -- Injection-Date, Message-ID, Date -- then Injection-Info,
; which closes the block: every octet after the Injection-Info line is the
; poster's.  So the injected octets name which fields were generated, and
; fn-inj-source-of recovers the source exactly (the injection inverse, D25).
; Before 2026-09-24 (recipe v1) the block was Path, Injection-Date,
; Injection-Info, then the generated Message-ID and Date; fn-inj-source-of
; reads a v1 record only where that recipe is unambiguous.
; The mandatory header fields of RFC 5536 section 3 are Date, From,
; Message-ID, Newsgroups, Path and Subject; RFC 5537 section 3.4.1 permits a
; proto-article to omit Message-ID, Date and Path, so From, Subject and
; Newsgroups must be supplied and the other three are generated.
;
; Two local policy choices, neither of them an RFC requirement:
;
;   * A proto-article that already carries a Path header field is refused
;     (:path-present).  RFC 5537 section 3.2.1 would have the injecting agent
;     prepend its identity to an existing Path.  Rewriting a supplied field
;     would break the property this book does prove, that the supplied source
;     octets are a verbatim suffix of the injected article, so fn refuses
;     instead of rewriting.  fn is the origin injecting agent for a POST.
;
;   * The wall clock must be present and must lie inside the 400-year
;     Gregorian cycle beginning 2000-01-01 (:clock-unusable,
;     :clock-out-of-range).  The calendar below walks that cycle; outside it
;     there is no Injection-Date this book will render.
;
; Retry identity is a design choice and is stated, not assumed: a supplied
; Message-ID is retained octet for octet, so a posting agent that supplies one
; has an exact retry identity across clock readings; a generated Message-ID is
; derived from the clock, so a retry that omits Message-ID is a new article.
; books/injection-invariants.lisp carries both statements.

(in-package "ACL2")
(include-book "article-fields")
(include-book "mailbox")
(include-book "clock")
(local (include-book "arithmetic/top" :dir :system))
; books/clock.lisp withdraws its observation recognizer at export (bp CHANGE,
; 8983f24); the guard of fn-inj-decide reads the wall reading through it.
(local (in-theory (enable fn-clock-observationp)))

; -----------------------------------------------------------------------------
; Literal octets

(defconst *fn-inj-crlf* '(13 10))
(defconst *fn-inj-path-name* '(112 97 116 104))
(defconst *fn-inj-from-name* '(102 114 111 109))
(defconst *fn-inj-subject-name* '(115 117 98 106 101 99 116))
(defconst *fn-inj-date-name* '(100 97 116 101))
(defconst *fn-inj-injection-date-name* '(105 110 106 101 99 116 105 111 110 45 100 97 116 101))
(defconst *fn-inj-path-field* '(80 97 116 104 58 32))
(defconst *fn-inj-path-tail* '(33 110 111 116 45 102 111 114 45 109 97 105 108))
(defconst *fn-inj-injection-date-field* '(73 110 106 101 99 116 105 111 110 45 68 97 116 101 58 32))
(defconst *fn-inj-injection-info-field* '(73 110 106 101 99 116 105 111 110 45 73 110 102 111 58 32))
(defconst *fn-inj-message-id-field* '(77 101 115 115 97 103 101 45 73 68 58 32))
(defconst *fn-inj-date-field* '(68 97 116 101 58 32))
(defconst *fn-inj-id-tail* '(46 102 110 64))
(defconst *fn-inj-max-agent-octets* 128)
(defconst *fn-inj-cycle-days* 146097)
(defconst *fn-inj-ms-per-day* 86400000)

; -----------------------------------------------------------------------------
; Total list and digit helpers.  Every function in this book is total: its
; guard is t and it coerces its arguments, so no caller has a guard obligation
; and every rule below is unconditional in its argument types.

(defun fn-inj-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-inj-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

(defun fn-inj-nth (k xs)
  (declare (xargs :guard t :measure (nfix k)))
  (let ((k (nfix k)))
    (if (zp k) (fn-inj-car xs)
      (fn-inj-nth (- k 1) (fn-inj-cdr xs)))))

(defun fn-inj-hi2 (n)
  (declare (xargs :guard t))
  (+ 48 (floor (nfix n) 10)))

(defun fn-inj-lo2 (n)
  (declare (xargs :guard t))
  (+ 48 (- (nfix n) (* 10 (floor (nfix n) 10)))))

(defun fn-inj-r1 (n)
  (declare (xargs :guard t))
  (- (nfix n) (* 1000 (floor (nfix n) 1000))))

(defun fn-inj-r2 (n)
  (declare (xargs :guard t))
  (- (fn-inj-r1 n) (* 100 (floor (fn-inj-r1 n) 100))))

(defun fn-inj-y-th (n) (declare (xargs :guard t)) (+ 48 (floor (nfix n) 1000)))
(defun fn-inj-y-hu (n) (declare (xargs :guard t)) (+ 48 (floor (fn-inj-r1 n) 100)))
(defun fn-inj-y-te (n) (declare (xargs :guard t)) (+ 48 (floor (fn-inj-r2 n) 10)))
(defun fn-inj-y-un (n)
  (declare (xargs :guard t))
  (+ 48 (- (fn-inj-r2 n) (* 10 (floor (fn-inj-r2 n) 10)))))

(defun fn-inj-un2 (a b)
  (declare (xargs :guard t))
  (+ (* 10 (- (ifix a) 48)) (- (ifix b) 48)))

(defun fn-inj-un4 (a b c d)
  (declare (xargs :guard t))
  (+ (* 1000 (- (ifix a) 48)) (* 100 (- (ifix b) 48))
     (* 10 (- (ifix c) 48)) (- (ifix d) 48)))

(defun fn-inj-rev-append (xs acc)
  (declare (xargs :guard t))
  (if (consp xs) (fn-inj-rev-append (cdr xs) (cons (car xs) acc)) acc))

; A fixed-width decimal, least significant octet first.  The width, not the
; value, carries the recursion, so no arithmetic library is needed to admit
; it and the rendering of any natural is exactly w octets.  Twenty digits
; cover every fn-clock-timep value (2^64-1 has twenty digits).
(defun fn-inj-digits-rev (n w)
  (declare (xargs :guard t :measure (nfix w)))
  (let ((w (nfix w)) (n (nfix n)))
    (if (zp w) nil
      (cons (+ 48 (mod n 10)) (fn-inj-digits-rev (floor n 10) (- w 1))))))

(defun fn-inj-digits (n w)
  (declare (xargs :guard t))
  (fn-inj-rev-append (fn-inj-digits-rev n w) nil))

; -----------------------------------------------------------------------------
; The Gregorian calendar of the 400-year cycle beginning 2000-01-01
;
; Both walks below are written so that they have an exact left inverse: the
; offset of the unit they stop in, plus the remainder they return, is the
; input.  fn-inj-year-of-inverts and fn-inj-month-of-inverts in
; books/injection-invariants.lisp are that statement, and injectivity of the
; whole decomposition follows from them with no arithmetic library.

(defun fn-inj-leapp (y)
  (declare (xargs :guard t))
  (let ((y (nfix y)))
    (and (equal (mod y 4) 0)
         (or (not (equal (mod y 100) 0)) (equal (mod y 400) 0)))))

(defun fn-inj-year-days (y)
  (declare (xargs :guard t))
  (if (fn-inj-leapp y) 366 365))

(defun fn-inj-month-days (m leap)
  (declare (xargs :guard t))
  (cond
   ((equal m 2) (if leap 29 28))
   ((equal m 1) 31)
   ((equal m 2) 0)
   ((equal m 3) 31)
   ((equal m 4) 30)
   ((equal m 5) 31)
   ((equal m 6) 30)
   ((equal m 7) 31)
   ((equal m 8) 31)
   ((equal m 9) 30)
   ((equal m 10) 31)
   ((equal m 11) 30)
   ((equal m 12) 31)
   (t 30)))

(defun fn-inj-days-before-year (y)
  ; Days from 2000-01-01 to (y)-01-01.
  (declare (xargs :guard t :measure (nfix y)))
  (let ((y (nfix y)))
    (if (<= y 2000) 0
      (+ (fn-inj-days-before-year (- y 1)) (fn-inj-year-days (- y 1))))))

(defun fn-inj-days-before-month (m leap)
  ; Days from January 1 to the first of month m.
  (declare (xargs :guard t :measure (nfix m)))
  (let ((m (nfix m)))
    (if (<= m 1) 0
      (+ (fn-inj-days-before-month (- m 1) leap)
         (fn-inj-month-days (- m 1) leap)))))

(defun fn-inj-year-of (days y fuel)
  ; (year . day-of-year), walking one year at a time from y.
  (declare (xargs :guard t :measure (nfix fuel)))
  (let ((days (nfix days)) (y (nfix y)) (fuel (nfix fuel)))
    (if (zp fuel) (cons y days)
      (if (< days (fn-inj-year-days y)) (cons y days)
        (fn-inj-year-of (- days (fn-inj-year-days y)) (+ y 1) (- fuel 1))))))

(defun fn-inj-month-of (doy m leap fuel)
  ; (month . day-of-month-minus-one), walking one month at a time from m.
  (declare (xargs :guard t :measure (nfix fuel)))
  (let ((doy (nfix doy)) (m (nfix m)) (fuel (nfix fuel)))
    (if (zp fuel) (cons m doy)
      (if (< doy (fn-inj-month-days m leap)) (cons m doy)
        (fn-inj-month-of (- doy (fn-inj-month-days m leap)) (+ m 1) leap
                         (- fuel 1))))))

; An instant is (year month day hour minute second day-of-week).
(defun fn-inj-instant-of (ms)
  (declare (xargs :guard t))
  (let* ((ms (nfix ms))
         (days (floor ms *fn-inj-ms-per-day*))
         (sec (floor (mod ms *fn-inj-ms-per-day*) 1000))
         (ym (fn-inj-year-of days 2000 400))
         (year (fn-inj-car ym))
         (md (fn-inj-month-of (fn-inj-cdr ym) 1 (fn-inj-leapp year) 12)))
    (list year (fn-inj-car md) (+ 1 (nfix (fn-inj-cdr md)))
          (floor sec 3600) (floor (mod sec 3600) 60) (mod sec 60)
          ; 2000-01-01 was a Saturday; 0 is Sunday.
          (mod (+ 6 days) 7))))

(defun fn-inj-instant-year (x) (declare (xargs :guard t)) (fn-inj-nth 0 x))
(defun fn-inj-instant-month (x) (declare (xargs :guard t)) (fn-inj-nth 1 x))
(defun fn-inj-instant-day (x) (declare (xargs :guard t)) (fn-inj-nth 2 x))
(defun fn-inj-instant-hour (x) (declare (xargs :guard t)) (fn-inj-nth 3 x))
(defun fn-inj-instant-minute (x) (declare (xargs :guard t)) (fn-inj-nth 4 x))
(defun fn-inj-instant-second (x) (declare (xargs :guard t)) (fn-inj-nth 5 x))
(defun fn-inj-instant-dow (x) (declare (xargs :guard t)) (fn-inj-nth 6 x))

(defun fn-inj-month-c1 (m)
  (declare (xargs :guard t))
  (cond
   ((equal m 1) 74)
   ((equal m 2) 70)
   ((equal m 3) 77)
   ((equal m 4) 65)
   ((equal m 5) 77)
   ((equal m 6) 74)
   ((equal m 7) 74)
   ((equal m 8) 65)
   ((equal m 9) 83)
   ((equal m 10) 79)
   ((equal m 11) 78)
   ((equal m 12) 68)
   (t 63)))

(defun fn-inj-month-c2 (m)
  (declare (xargs :guard t))
  (cond
   ((equal m 1) 97)
   ((equal m 2) 101)
   ((equal m 3) 97)
   ((equal m 4) 112)
   ((equal m 5) 97)
   ((equal m 6) 117)
   ((equal m 7) 117)
   ((equal m 8) 117)
   ((equal m 9) 101)
   ((equal m 10) 99)
   ((equal m 11) 111)
   ((equal m 12) 101)
   (t 63)))

(defun fn-inj-month-c3 (m)
  (declare (xargs :guard t))
  (cond
   ((equal m 1) 110)
   ((equal m 2) 98)
   ((equal m 3) 114)
   ((equal m 4) 114)
   ((equal m 5) 121)
   ((equal m 6) 110)
   ((equal m 7) 108)
   ((equal m 8) 103)
   ((equal m 9) 112)
   ((equal m 10) 116)
   ((equal m 11) 118)
   ((equal m 12) 99)
   (t 63)))

(defun fn-inj-month-index (a b c)
  (declare (xargs :guard t))
  (cond
   ((and (equal a 74) (equal b 97) (equal c 110)) 1)
   ((and (equal a 70) (equal b 101) (equal c 98)) 2)
   ((and (equal a 77) (equal b 97) (equal c 114)) 3)
   ((and (equal a 65) (equal b 112) (equal c 114)) 4)
   ((and (equal a 77) (equal b 97) (equal c 121)) 5)
   ((and (equal a 74) (equal b 117) (equal c 110)) 6)
   ((and (equal a 74) (equal b 117) (equal c 108)) 7)
   ((and (equal a 65) (equal b 117) (equal c 103)) 8)
   ((and (equal a 83) (equal b 101) (equal c 112)) 9)
   ((and (equal a 79) (equal b 99) (equal c 116)) 10)
   ((and (equal a 78) (equal b 111) (equal c 118)) 11)
   ((and (equal a 68) (equal b 101) (equal c 99)) 12)
   (t 0)))

(defun fn-inj-dow-c1 (d)
  (declare (xargs :guard t))
  (cond
   ((equal d 0) 83)
   ((equal d 1) 77)
   ((equal d 2) 84)
   ((equal d 3) 87)
   ((equal d 4) 84)
   ((equal d 5) 70)
   ((equal d 6) 83)
   (t 63)))

(defun fn-inj-dow-c2 (d)
  (declare (xargs :guard t))
  (cond
   ((equal d 0) 117)
   ((equal d 1) 111)
   ((equal d 2) 117)
   ((equal d 3) 101)
   ((equal d 4) 104)
   ((equal d 5) 114)
   ((equal d 6) 97)
   (t 63)))

(defun fn-inj-dow-c3 (d)
  (declare (xargs :guard t))
  (cond
   ((equal d 0) 110)
   ((equal d 1) 110)
   ((equal d 2) 101)
   ((equal d 3) 100)
   ((equal d 4) 117)
   ((equal d 5) 105)
   ((equal d 6) 116)
   (t 63)))

; -----------------------------------------------------------------------------
; The RFC 5322 date-time rendered by RFC 5536 section 3.1.1 for Date and by
; section 3.2.6 for Injection-Date.  Exactly 31 octets, every component at a
; fixed width, so the decoder below reads each component back by position.

(defun fn-inj-date-octets (inst)
  ; A flat list of 31 octets: every component is rendered by a closed function
  ; of one number, and fn-inj-date-decode recombines the same functions by the
  ; same weights.  The round trip is then pure cancellation; it needs no
  ; property of `floor`, so no arithmetic library and no case split.
  (declare (xargs :guard t))
  (list (fn-inj-dow-c1 (fn-inj-instant-dow inst))
        (fn-inj-dow-c2 (fn-inj-instant-dow inst))
        (fn-inj-dow-c3 (fn-inj-instant-dow inst)) 44 32
        (fn-inj-hi2 (fn-inj-instant-day inst))
        (fn-inj-lo2 (fn-inj-instant-day inst)) 32
        (fn-inj-month-c1 (fn-inj-instant-month inst))
        (fn-inj-month-c2 (fn-inj-instant-month inst))
        (fn-inj-month-c3 (fn-inj-instant-month inst)) 32
        (fn-inj-y-th (fn-inj-instant-year inst))
        (fn-inj-y-hu (fn-inj-instant-year inst))
        (fn-inj-y-te (fn-inj-instant-year inst))
        (fn-inj-y-un (fn-inj-instant-year inst)) 32
        (fn-inj-hi2 (fn-inj-instant-hour inst))
        (fn-inj-lo2 (fn-inj-instant-hour inst)) 58
        (fn-inj-hi2 (fn-inj-instant-minute inst))
        (fn-inj-lo2 (fn-inj-instant-minute inst)) 58
        (fn-inj-hi2 (fn-inj-instant-second inst))
        (fn-inj-lo2 (fn-inj-instant-second inst)) 32
        43 48 48 48 48))

(defun fn-inj-date-decode (x)
  ; (year month day hour minute second), read back from the rendering.
  (declare (xargs :guard t))
  (list (fn-inj-un4 (fn-inj-nth 12 x) (fn-inj-nth 13 x)
                    (fn-inj-nth 14 x) (fn-inj-nth 15 x))
        (fn-inj-month-index (fn-inj-nth 8 x) (fn-inj-nth 9 x)
                            (fn-inj-nth 10 x))
        (fn-inj-un2 (fn-inj-nth 5 x) (fn-inj-nth 6 x))
        (fn-inj-un2 (fn-inj-nth 17 x) (fn-inj-nth 18 x))
        (fn-inj-un2 (fn-inj-nth 20 x) (fn-inj-nth 21 x))
        (fn-inj-un2 (fn-inj-nth 23 x) (fn-inj-nth 24 x))))

; -----------------------------------------------------------------------------
; The configuration record.  Opaque: shape and accessor-of-constructor lemmas
; are proved once here and the definition runes are withdrawn immediately.

(defun fn-inj-config-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
(defun fn-inj-config-allow (x) (declare (xargs :guard t)) (fn-inj-nth 0 x))
(defun fn-inj-config-agent (x) (declare (xargs :guard t)) (fn-inj-nth 1 x))
(defun fn-inj-config-groups (x) (declare (xargs :guard t)) (fn-inj-nth 2 x))
(defun fn-inj-config-max-octets (x) (declare (xargs :guard t)) (fn-inj-nth 3 x))

(defun fn-inj-make-config (allow agent groups max-octets)
  (declare (xargs :guard t))
  (list allow agent groups max-octets))

(defthm fn-inj-config-shapep-of-fn-inj-make-config
  (fn-inj-config-shapep (fn-inj-make-config allow agent groups max-octets)))
(defthm fn-inj-config-allow-of-fn-inj-make-config
  (equal (fn-inj-config-allow (fn-inj-make-config allow agent groups max))
         allow))
(defthm fn-inj-config-agent-of-fn-inj-make-config
  (equal (fn-inj-config-agent (fn-inj-make-config allow agent groups max))
         agent))
(defthm fn-inj-config-groups-of-fn-inj-make-config
  (equal (fn-inj-config-groups (fn-inj-make-config allow agent groups max))
         groups))
(defthm fn-inj-config-max-octets-of-fn-inj-make-config
  (equal (fn-inj-config-max-octets (fn-inj-make-config allow agent groups max))
         max))

(in-theory (disable (:d fn-inj-config-shapep) (:d fn-inj-make-config)
                    (:d fn-inj-config-allow) (:d fn-inj-config-agent)
                    (:d fn-inj-config-groups) (:d fn-inj-config-max-octets)))

(defun fn-inj-group-namesp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cbor-octet-listp (car xs))
           (fn-af-newsgroup-namep (car xs))
           (fn-inj-group-namesp (cdr xs)))
    (null xs)))

(defun fn-inj-configp (x)
  (declare (xargs :guard t))
  (and (fn-inj-config-shapep x)
       (booleanp (fn-inj-config-allow x))
       (fn-cbor-octet-listp (fn-inj-config-agent x))
       (consp (fn-inj-config-agent x))
       (<= (len (fn-inj-config-agent x)) *fn-inj-max-agent-octets*)
       (fn-af-dot-atom-textp (fn-inj-config-agent x))
       (fn-inj-group-namesp (fn-inj-config-groups x))
       (posp (fn-inj-config-max-octets x))
       (<= (fn-inj-config-max-octets x) *fn-article-max-octets*)))

; -----------------------------------------------------------------------------
; The decision record.  Opaque, and the only thing this book returns.

(defun fn-inj-decision-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5)))
(defun fn-inj-decision-status (x) (declare (xargs :guard t)) (fn-inj-nth 0 x))
(defun fn-inj-decision-reason (x) (declare (xargs :guard t)) (fn-inj-nth 1 x))
(defun fn-inj-decision-msgid (x) (declare (xargs :guard t)) (fn-inj-nth 2 x))
(defun fn-inj-decision-groups (x) (declare (xargs :guard t)) (fn-inj-nth 3 x))
(defun fn-inj-decision-octets (x) (declare (xargs :guard t)) (fn-inj-nth 4 x))

(defun fn-inj-make-decision (status reason msgid groups octets)
  (declare (xargs :guard t))
  (list status reason msgid groups octets))

(defthm fn-inj-decision-shapep-of-fn-inj-make-decision
  (fn-inj-decision-shapep
   (fn-inj-make-decision status reason msgid groups octets)))
(defthm fn-inj-decision-status-of-fn-inj-make-decision
  (equal (fn-inj-decision-status
          (fn-inj-make-decision status reason msgid groups octets))
         status))
(defthm fn-inj-decision-reason-of-fn-inj-make-decision
  (equal (fn-inj-decision-reason
          (fn-inj-make-decision status reason msgid groups octets))
         reason))
(defthm fn-inj-decision-msgid-of-fn-inj-make-decision
  (equal (fn-inj-decision-msgid
          (fn-inj-make-decision status reason msgid groups octets))
         msgid))
(defthm fn-inj-decision-groups-of-fn-inj-make-decision
  (equal (fn-inj-decision-groups
          (fn-inj-make-decision status reason msgid groups octets))
         groups))
(defthm fn-inj-decision-octets-of-fn-inj-make-decision
  (equal (fn-inj-decision-octets
          (fn-inj-make-decision status reason msgid groups octets))
         octets))

(in-theory (disable (:d fn-inj-decision-shapep) (:d fn-inj-make-decision)
                    (:d fn-inj-decision-status) (:d fn-inj-decision-reason)
                    (:d fn-inj-decision-msgid) (:d fn-inj-decision-groups)
                    (:d fn-inj-decision-octets)))

(defun fn-inj-refuse (reason)
  (declare (xargs :guard t))
  (fn-inj-make-decision :refused reason nil nil nil))

(defun fn-inj-injectedp (d)
  (declare (xargs :guard t))
  (equal (fn-inj-decision-status d) :injected))

; -----------------------------------------------------------------------------
; Generated field lines and the generated Message-ID

(defun fn-inj-append (a b)
  (declare (xargs :guard t))
  (if (consp a) (cons (car a) (fn-inj-append (cdr a) b)) b))

(defun fn-inj-path-line (agent)
  (declare (xargs :guard t))
  (fn-inj-append *fn-inj-path-field*
                 (fn-inj-append agent
                                (fn-inj-append *fn-inj-path-tail* *fn-inj-crlf*))))

(defun fn-inj-injection-info-line (agent)
  (declare (xargs :guard t))
  (fn-inj-append *fn-inj-injection-info-field*
                 (fn-inj-append agent *fn-inj-crlf*)))

(defun fn-inj-injection-date-line (date)
  (declare (xargs :guard t))
  (fn-inj-append *fn-inj-injection-date-field*
                 (fn-inj-append date *fn-inj-crlf*)))

(defun fn-inj-date-line (date)
  (declare (xargs :guard t))
  (fn-inj-append *fn-inj-date-field* (fn-inj-append date *fn-inj-crlf*)))

(defun fn-inj-message-id-line (id)
  (declare (xargs :guard t))
  (fn-inj-append *fn-inj-message-id-field* (fn-inj-append id *fn-inj-crlf*)))

; <wall.monotonic.fn@agent>.  Both numbers come from the one clock
; observation; `agent` is the configured dot-atom identity, so the whole
; identifier is an RFC 5536 msg-id (fn-inj-generated-id-is-a-message-id).
(defun fn-inj-generated-message-id (obs config)
  (declare (xargs :guard (fn-clock-observationp obs)))
  (fn-inj-append
   '(60)
   (fn-inj-append
    (fn-inj-digits (fn-clock-wall obs) 20)
    (fn-inj-append
     '(46)
     (fn-inj-append
      (fn-inj-digits (fn-clock-monotonic obs) 20)
      (fn-inj-append *fn-inj-id-tail*
                     (fn-inj-append (fn-inj-config-agent config) '(62))))))))

; -----------------------------------------------------------------------------
; Field presence, as RFC 5536 section 3 mandatory fields

(defun fn-inj-single-fieldp (article name)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (let ((fields (fn-article-get-headers article name)))
    (and (consp fields) (null (cdr fields)))))

(defun fn-inj-absentp (article name)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (null (fn-article-get-headers article name)))

; RFC 5536 section 3.1.2: From is an RFC 5322 mailbox-list (books/mailbox.lisp,
; the bounded recognizer).  Presence alone was checked until 2026-09-22, and
; `From: yue' was injected and served (planning/evidence/agents-on-hbox-
; 2026-09-22.md).  Read only after :from-missing and :from-duplicate, so the
; field is the one From field.
(defun fn-inj-from-validp (article)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (let ((fields (fn-article-get-headers article *fn-inj-from-name*)))
    (and (consp fields)
         (fn-article-fieldp (car fields))
         (fn-mbx-mailbox-listp (fn-article-field-unfolded-value (car fields))))))

(defun fn-inj-memberp (x xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (or (equal x (car xs)) (fn-inj-memberp x (cdr xs)))
    nil))

(defun fn-inj-groups-admissiblep (names allowed)
  (declare (xargs :guard t))
  (if (consp names)
      (and (fn-inj-memberp (car names) allowed)
           (fn-inj-groups-admissiblep (cdr names) allowed))
    (null names)))

(defun fn-inj-mandatory-reason (article)
  ; nil when every field a proto-article must supply is present exactly once
  ; and no field this agent generates is already present.
  (declare (xargs :guard (fn-article-syntax-p article)))
  (cond
   ((not (fn-inj-absentp article *fn-inj-path-name*)) :path-present)
   ((not (fn-inj-absentp article *fn-inj-injection-date-name*))
    :injection-date-present)
   ((fn-inj-absentp article *fn-inj-from-name*) :from-missing)
   ((not (fn-inj-single-fieldp article *fn-inj-from-name*)) :from-duplicate)
   ((not (fn-inj-from-validp article)) :from-invalid)
   ((fn-inj-absentp article *fn-inj-subject-name*) :subject-missing)
   ((not (fn-inj-single-fieldp article *fn-inj-subject-name*))
    :subject-duplicate)
   ((and (not (fn-inj-absentp article *fn-inj-date-name*))
         (not (fn-inj-single-fieldp article *fn-inj-date-name*)))
    :date-duplicate)
   (t nil)))

; -----------------------------------------------------------------------------
; The injection decision
;
; The one entry point.  Its three arguments are the whole of its input.

(defun fn-inj-proto-reason (check)
  (declare (xargs :guard t))
  (if (equal (fn-inj-nth 0 check) :error) (fn-inj-nth 1 check) nil))

; The injected block of recipe v2.  The Injection-Date is written exactly
; when a field is generated (RFC 5537 section 3.5 item 11: none when the
; poster supplied both Date and Message-ID; fn-inj-mandatory-reason has
; already refused a supplied Injection-Date), and the Injection-Info line
; comes last.
(defun fn-inj-prefix (date msgid agent generate-id generate-date)
  (declare (xargs :guard t))
  (fn-inj-append
   (fn-inj-path-line agent)
   (fn-inj-append
    (if (or generate-id generate-date) (fn-inj-injection-date-line date) nil)
    (fn-inj-append
     (if generate-id (fn-inj-message-id-line msgid) nil)
     (fn-inj-append
      (if generate-date (fn-inj-date-line date) nil)
      (fn-inj-injection-info-line agent))))))

; -----------------------------------------------------------------------------
; The injection inverse: the poster's source of a stored article
;
; `fn-inj-source-of stored agent msgid' is (t . source) when `stored' is
; exactly an injection of `source' by `agent' under Message-ID `msgid', and
; nil when the octets do not say which source that was.  It is the D25
; comparison subject: two submissions under one Message-ID are one article
; when their sources are one, whatever the clock read at either injection
; (books/poster-bytes.lisp fn-pb-existing-action).
;
; Recipe v2 (fn-inj-prefix above): this agent's Path line; then, when a field
; was generated, an Injection-Date line with some 31-octet date, the
; generated Message-ID line of `msgid' if the id was generated, a Date line
; with that same date if the Date was generated; then this agent's
; Injection-Info line; then the source.  Which fields were generated is read
; off the block, and nothing after the Injection-Info line is read as
; injected, so the source is recovered exactly
; (fn-inj-source-of-inverts-the-injection, books/injection-invariants.lisp).
;
; Recipe v1, before 2026-09-24: Path, Injection-Date, Injection-Info, then
; the generated Message-ID and Date lines, then the source; the
; Injection-Date was always written.  A v1 record is recognised by its
; Injection-Info line directly after the Injection-Date line, which v2 never
; writes.  Its source is read only where v1 is unambiguous: when what follows
; the Injection-Info line opens with a Message-ID line of `msgid' or a Date
; line of the injection's date, that line may be the poster's or the
; injector's, and the answer is nil -- the caller then compares octets
; exactly, never a guessed source.

(defun fn-inj-strip (prefix x)
  ; x with `prefix' removed from its front, or :no.
  (declare (xargs :guard t))
  (if (consp prefix)
      (if (and (consp x) (equal (car x) (car prefix)))
          (fn-inj-strip (cdr prefix) (cdr x))
        :no)
    x))

(defun fn-inj-take (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (or (zp n) (atom x)) nil
      (cons (car x) (fn-inj-take (- n 1) (cdr x))))))

(defun fn-inj-drop (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (or (zp n) (atom x)) x
      (fn-inj-drop (- n 1) (cdr x)))))

; `line' removed from the front of x when x opens with it, else x unchanged.
(defun fn-inj-strip-optional (line x)
  (declare (xargs :guard t))
  (let ((r (fn-inj-strip line x)))
    (if (equal r :no) x r)))

(defun fn-inj-source-after-stamp (r2 date agent msgid)
  ; r2 is what follows an Injection-Date line carrying `date'.
  (declare (xargs :guard t))
  (let ((v1 (fn-inj-strip (fn-inj-injection-info-line agent) r2)))
    (if (not (equal v1 :no))
        (if (or (not (equal (fn-inj-strip (fn-inj-message-id-line msgid) v1) :no))
                (not (equal (fn-inj-strip (fn-inj-date-line date) v1) :no)))
            nil
          (cons t v1))
      (let ((s (fn-inj-strip
                (fn-inj-injection-info-line agent)
                (fn-inj-strip-optional
                 (fn-inj-date-line date)
                 (fn-inj-strip-optional (fn-inj-message-id-line msgid) r2)))))
        (if (equal s :no) nil (cons t s))))))

(defun fn-inj-source-of (stored agent msgid)
  (declare (xargs :guard t))
  (let ((r1 (fn-inj-strip (fn-inj-path-line agent) stored)))
    (cond ((equal r1 :no) nil)
          ((equal (fn-inj-strip *fn-inj-injection-date-field* r1) :no)
           (let ((s (fn-inj-strip (fn-inj-injection-info-line agent) r1)))
             (if (equal s :no) nil (cons t s))))
          (t
           (let* ((date (fn-inj-take 31 (fn-inj-drop
                                         (len *fn-inj-injection-date-field*)
                                         r1)))
                  (r2 (fn-inj-strip (fn-inj-injection-date-line date) r1)))
             (if (equal r2 :no)
                 nil
               (fn-inj-source-after-stamp r2 date agent msgid)))))))

; `stored' is an injection of `source' by `agent' under `msgid': the
; operator's retry test (books/owner.lisp fn-own-operator-decision).  Since
; 2026-09-24 it is exactly the inverse above; before, it also accepted a
; source with or without a Date line equal to the injection's, in either
; direction.
(defun fn-inj-reinjectionp (stored source agent msgid)
  (declare (xargs :guard t))
  (let ((r1 (fn-inj-strip (fn-inj-path-line agent) stored)))
    (and (not (equal r1 :no))
         (equal (fn-inj-source-of stored agent msgid) (cons t source)))))

(defun fn-inj-decide (source config observation)
  (declare (xargs :guard t))
  (if (not (fn-inj-configp config)) (fn-inj-refuse :config-invalid)
    (if (not (fn-inj-config-allow config)) (fn-inj-refuse :posting-disallowed)
      (if (or (not (fn-clock-observationp observation))
              (not (fn-clock-has-wall observation)))
          (fn-inj-refuse :clock-unusable)
        (if (<= *fn-inj-cycle-days*
                (floor (fn-clock-wall observation) *fn-inj-ms-per-day*))
            (fn-inj-refuse :clock-out-of-range)
          (let ((parsed (fn-article-parse source)))
            (if (not (fn-article-result-okp parsed))
                (fn-inj-refuse :unparsable)
              (let ((article (fn-article-result-article parsed)))
                (if (not (fn-article-syntax-p article))
                    (fn-inj-refuse :unparsable)
                  (let ((check (fn-af-proto-article-check article)))
                    (if (fn-inj-proto-reason check)
                        (fn-inj-refuse (fn-inj-proto-reason check))
                      (let ((mandatory (fn-inj-mandatory-reason article)))
                        (if mandatory (fn-inj-refuse mandatory)
                          (let ((supplied (fn-inj-nth 1 check))
                                (groups (fn-inj-nth 2 check)))
                            (if (not (consp groups)) (fn-inj-refuse :no-groups)
                              (if (not (fn-inj-groups-admissiblep
                                        groups (fn-inj-config-groups config)))
                                  (fn-inj-refuse :unknown-group)
                                (let* ((date (fn-inj-date-octets
                                              (fn-inj-instant-of
                                               (fn-clock-wall observation))))
                                       (msgid
                                        (if supplied supplied
                                          (fn-inj-generated-message-id
                                           observation config)))
                                       (octets
                                        (fn-inj-append
                                         (fn-inj-prefix
                                          date msgid
                                          (fn-inj-config-agent config)
                                          (not supplied)
                                          (fn-inj-absentp
                                           article *fn-inj-date-name*))
                                         source)))
                                  (if (< (fn-inj-config-max-octets config)
                                         (len octets))
                                      (fn-inj-refuse :oversize)
                                    (fn-inj-make-decision
                                     :injected nil msgid groups
                                     octets)))))))))))))))))))

(verify-guards fn-inj-car)
(verify-guards fn-inj-cdr)
(verify-guards fn-inj-nth)
(verify-guards fn-inj-hi2)
(verify-guards fn-inj-lo2)
(verify-guards fn-inj-r1)
(verify-guards fn-inj-r2)
(verify-guards fn-inj-y-th)
(verify-guards fn-inj-y-hu)
(verify-guards fn-inj-y-te)
(verify-guards fn-inj-y-un)
(verify-guards fn-inj-un2)
(verify-guards fn-inj-un4)
(verify-guards fn-inj-rev-append)
(verify-guards fn-inj-digits-rev)
(verify-guards fn-inj-digits)
(verify-guards fn-inj-leapp)
(verify-guards fn-inj-year-days)
(verify-guards fn-inj-month-days)
(verify-guards fn-inj-days-before-year)
(verify-guards fn-inj-days-before-month)
(verify-guards fn-inj-year-of)
(verify-guards fn-inj-month-of)
(verify-guards fn-inj-instant-of)
(verify-guards fn-inj-instant-year)
(verify-guards fn-inj-month-c1)
(verify-guards fn-inj-month-c2)
(verify-guards fn-inj-month-c3)
(verify-guards fn-inj-month-index)
(verify-guards fn-inj-dow-c1)
(verify-guards fn-inj-dow-c2)
(verify-guards fn-inj-dow-c3)
(verify-guards fn-inj-date-octets)
(verify-guards fn-inj-date-decode)
(verify-guards fn-inj-config-shapep)
(verify-guards fn-inj-make-config)
(verify-guards fn-inj-group-namesp)
(verify-guards fn-inj-configp)
(verify-guards fn-inj-decision-shapep)
(verify-guards fn-inj-make-decision)
(verify-guards fn-inj-refuse)
(verify-guards fn-inj-injectedp)
(verify-guards fn-inj-append)
(verify-guards fn-inj-path-line)
(verify-guards fn-inj-injection-info-line)
(verify-guards fn-inj-injection-date-line)
(verify-guards fn-inj-date-line)
(verify-guards fn-inj-message-id-line)
(verify-guards fn-inj-generated-message-id)
(verify-guards fn-inj-single-fieldp)
(verify-guards fn-inj-absentp)
(verify-guards fn-inj-from-validp)
(verify-guards fn-inj-memberp)
(verify-guards fn-inj-groups-admissiblep)
(verify-guards fn-inj-mandatory-reason)
(verify-guards fn-inj-proto-reason)
(verify-guards fn-inj-prefix)
(verify-guards fn-inj-decide)
(verify-guards fn-inj-strip)
(verify-guards fn-inj-take)
(verify-guards fn-inj-drop)
(verify-guards fn-inj-strip-optional)
(verify-guards fn-inj-source-after-stamp)
(verify-guards fn-inj-source-of)
(verify-guards fn-inj-reinjectionp)

; ---------------------------------------------------------------------------
; Export theory.  The definitions are proof vocabulary for
; books/injection-invariants.lisp and books/nntp-post.lisp, not rules an
; includer inherits; ground evaluation is unaffected.

(deftheory fn-inj-vocabulary
  (quote (fn-inj-car fn-inj-cdr fn-inj-nth fn-inj-hi2 fn-inj-lo2 fn-inj-r1 fn-inj-r2
          fn-inj-y-th fn-inj-y-hu fn-inj-y-te fn-inj-y-un
          fn-inj-un2 fn-inj-un4
          fn-inj-rev-append fn-inj-digits-rev fn-inj-digits
          fn-inj-leapp fn-inj-year-days
          fn-inj-month-days fn-inj-days-before-year fn-inj-days-before-month
          fn-inj-year-of fn-inj-month-of fn-inj-instant-of
          fn-inj-instant-year fn-inj-instant-month fn-inj-instant-day
          fn-inj-instant-hour fn-inj-instant-minute fn-inj-instant-second
          fn-inj-instant-dow fn-inj-month-index
          fn-inj-month-c1 fn-inj-month-c2 fn-inj-month-c3
          fn-inj-dow-c1 fn-inj-dow-c2 fn-inj-dow-c3
          fn-inj-date-octets fn-inj-date-decode
          fn-inj-group-namesp fn-inj-configp fn-inj-refuse fn-inj-injectedp
          fn-inj-append fn-inj-path-line fn-inj-injection-info-line
          fn-inj-injection-date-line fn-inj-date-line fn-inj-message-id-line
          fn-inj-generated-message-id fn-inj-single-fieldp fn-inj-absentp
          fn-inj-from-validp
          fn-inj-memberp fn-inj-groups-admissiblep fn-inj-mandatory-reason
          fn-inj-proto-reason fn-inj-prefix fn-inj-decide
          fn-inj-strip fn-inj-take fn-inj-drop fn-inj-strip-optional
          fn-inj-source-after-stamp fn-inj-source-of fn-inj-reinjectionp)))

(in-theory (disable fn-inj-vocabulary))
