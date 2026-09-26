; fn: `tls reload' and the served certificate line (PRF-212, HST-020).
;
; The running owner reads its certificate chain and private key at `run'
; (host/native/tls.lisp fnn-tls-open-context).  A Let's Encrypt renewal
; replaces those files every sixty days or so; `operator CONFIG tls reload'
; asks the owner, over its control socket, to take the new pair for NEW
; connections while every session already open keeps the context it
; handshook with.
;
; The host builds a candidate SSL_CTX from the configured paths and reports
; what the library observed, as primitive facts:
;
;   chain     SSL_CTX_use_certificate_chain_file returned 1
;   key       SSL_CTX_use_PrivateKey_file returned 1 (an encrypted key is
;             refused there: the callback supplies no password)
;   match     SSL_CTX_check_private_key returned 1
;   not-before, not-after
;             the leaf's validity times, the ASN1_TIME contents octets
;             (ASN1_STRING_get0_data: UTCTime YYMMDDHHMMSSZ or
;             GeneralizedTime YYYYMMDDHHMMSSZ)
;   san       the leaf's subjectAltName extension value, DER GeneralNames
;             (X509_EXTENSION_get_data), or nil when it has none
;   now       the host clock, in seconds since 1970-01-01T00:00:00Z
;
; This book parses the two times and the dNSNames and decides:
; `fn-tlsr-decide' accepts exactly when the chain and key loaded, the key
; matches the chain's leaf, the host clock lies inside the validity window,
; the names are readable, and every dNSName the served certificate answers
; for is still named (a renewal never drops a name a peer verifies this node
; by).  Every other answer is a refusal by name, and the host keeps the
; context it was serving.
;
; The control frames are FNCT kind 19 (the request: the word `reload' or
; `status') and kind 20 (the reply: the status, the reason word, and the
; line the owner now serves, rendered here).  FNCT kinds 1 to 18 are
; books/native-control-reason.lisp's list.  An owner that predates kind 19
; answers the plain refusal (kind 2) to a frame it cannot decode, which the
; client reads as :owner-lacks-tls-reload.

(in-package "ACL2")
(include-book "native-control")
(include-book "native-control-reason")

; -----------------------------------------------------------------------------
; Decimal fields and the validity times

(defun fn-tlsr-digitsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= 48 (car xs)) (<= (car xs) 57)
           (fn-tlsr-digitsp (cdr xs)))
    t))

(defun fn-tlsr-digits-value (xs acc)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-tlsr-digits-value (cdr xs) (+ (* 10 (nfix acc))
                                         (nfix (- (nfix (car xs)) 48))))
    (nfix acc)))

; The first N elements of XS and the rest (a tail of XS).
(defun fn-tlsr-split (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (consp xs)))
      (cons nil xs)
    (let ((r (fn-tlsr-split (- n 1) (cdr xs))))
      (cons (cons (car xs) (car r)) (cdr r)))))

(defthm fn-tlsr-split-rest-shorter
  (<= (len (cdr (fn-tlsr-split n xs))) (len xs))
  :rule-classes :linear)

(defthm fn-tlsr-split-rest-strictly-shorter
  (implies (and (posp n) (consp xs))
           (< (len (cdr (fn-tlsr-split n xs))) (len xs)))
  :rule-classes :linear)

; The decimal value of WIDTH digits at START, or nil.
(defun fn-tlsr-field (xs start width)
  (declare (xargs :guard (and (natp start) (natp width))))
  (let ((part (car (fn-tlsr-split width (cdr (fn-tlsr-split start xs))))))
    (if (and (equal (len part) width) (fn-tlsr-digitsp part))
        (fn-tlsr-digits-value part 0)
      nil)))

(defun fn-tlsr-leap-yearp (y)
  (declare (xargs :guard (natp y)))
  (and (equal (mod y 4) 0)
       (or (not (equal (mod y 100) 0)) (equal (mod y 400) 0))))

(defun fn-tlsr-month-days (y m)
  (declare (xargs :guard (and (natp y) (natp m))))
  (cond ((equal m 2) (if (fn-tlsr-leap-yearp y) 29 28))
        ((member m '(4 6 9 11)) 30)
        (t 31)))

; RFC 5280 section 4.1.2.5: UTCTime YYMMDDHHMMSSZ (YY below 50 is 20YY,
; else 19YY) or GeneralizedTime YYYYMMDDHHMMSSZ, both in UTC.  The fields
; (YEAR MONTH DAY HOUR MINUTE SECOND), or nil for anything else.
(defun fn-tlsr-time-fields (octets)
  (declare (xargs :guard t))
  (let* ((n (len octets))
         (generalized (equal n 15))
         (yw (if generalized 4 2)))
    (if (not (and (true-listp octets)
                  (or (equal n 13) generalized)
                  (equal (nth (- n 1) octets) 90))) ; Z
        nil
      (let ((y0 (fn-tlsr-field octets 0 yw))
            (mo (fn-tlsr-field octets yw 2))
            (d (fn-tlsr-field octets (+ yw 2) 2))
            (h (fn-tlsr-field octets (+ yw 4) 2))
            (mi (fn-tlsr-field octets (+ yw 6) 2))
            (s (fn-tlsr-field octets (+ yw 8) 2)))
        (if (not (and (natp y0) (natp mo) (natp d) (natp h) (natp mi) (natp s)))
            nil
          (let ((y (cond (generalized y0)
                         ((< y0 50) (+ 2000 y0))
                         (t (+ 1900 y0)))))
            (if (and (<= 1 mo) (<= mo 12)
                     (<= 1 d) (<= d (fn-tlsr-month-days y mo))
                     (< h 24) (< mi 60) (< s 60))
                (list y mo d h mi s)
              nil)))))))

; Days since 1970-01-01 of a proleptic Gregorian date (the civil-from-days
; inverse in eras of 400 years).
(defun fn-tlsr-days-from-civil (y m d)
  (declare (xargs :guard (and (integerp y) (integerp m) (integerp d))))
  (let* ((y1 (if (<= m 2) (- y 1) y))
         (era (floor y1 400))
         (yoe (- y1 (* era 400)))
         (mp (if (> m 2) (- m 3) (+ m 9)))
         (doy (+ (floor (+ (* 153 mp) 2) 5) (- d 1)))
         (doe (+ (* yoe 365) (floor yoe 4) (- (floor yoe 100)) doy)))
    (+ (* era 146097) doe -719468)))

(defthm fn-tlsr-days-from-civil-integerp
  (implies (and (integerp y) (integerp m) (integerp d))
           (integerp (fn-tlsr-days-from-civil y m d)))
  :rule-classes :type-prescription)

(in-theory (disable fn-tlsr-days-from-civil))

(defun fn-tlsr-seconds (fields)
  (declare (xargs :guard t))
  (if (and (true-listp fields) (equal (len fields) 6))
      (+ (* 86400 (fn-tlsr-days-from-civil (ifix (nth 0 fields))
                                           (ifix (nth 1 fields))
                                           (ifix (nth 2 fields))))
         (* 3600 (ifix (nth 3 fields)))
         (* 60 (ifix (nth 4 fields)))
         (ifix (nth 5 fields)))
    0))

(defthm fn-tlsr-seconds-integerp
  (integerp (fn-tlsr-seconds fields))
  :rule-classes :type-prescription)

(in-theory (disable fn-tlsr-seconds fn-tlsr-time-fields))

; -----------------------------------------------------------------------------
; The leaf's DNS names: subjectAltName's GeneralNames (RFC 5280 section
; 4.2.1.6), SEQUENCE OF GeneralName, each dNSName [2] IMPLICIT IA5String
; (tag 0x82).  Every other GeneralName is skipped by its length.  The
; library has already parsed the certificate; this reads the one extension's
; octets it hands over, and the work is one pass over them.

(defun fn-tlsr-der-long (k xs acc)
  (declare (xargs :guard (natp k)))
  (cond ((zp k) (cons (nfix acc) xs))
        ((not (consp xs)) nil)
        ((not (natp (car xs))) nil)
        (t (fn-tlsr-der-long (- k 1) (cdr xs)
                             (+ (* 256 (nfix acc)) (car xs))))))

; A DER length at the head of XS: (LENGTH . REST), REST the octets after it.
; The long form takes one to four length octets.
(defun fn-tlsr-der-length (xs)
  (declare (xargs :guard t))
  (cond ((not (consp xs)) nil)
        ((not (natp (car xs))) nil)
        ((< (car xs) 128) (cons (car xs) (cdr xs)))
        ((and (<= 129 (car xs)) (<= (car xs) 132))
         (fn-tlsr-der-long (- (car xs) 128) (cdr xs) 0))
        (t nil)))

(defthm fn-tlsr-der-long-rest-shorter
  (implies (consp (fn-tlsr-der-long k xs acc))
           (<= (len (cdr (fn-tlsr-der-long k xs acc))) (len xs)))
  :rule-classes :linear)

(defthm fn-tlsr-der-long-length-natp
  (implies (consp (fn-tlsr-der-long k xs acc))
           (natp (car (fn-tlsr-der-long k xs acc))))
  :rule-classes :type-prescription)

(defthm fn-tlsr-der-length-rest-shorter
  (implies (consp (fn-tlsr-der-length xs))
           (< (len (cdr (fn-tlsr-der-length xs))) (len xs)))
  :rule-classes :linear)

(defthm fn-tlsr-der-length-natp
  (implies (consp (fn-tlsr-der-length xs))
           (natp (car (fn-tlsr-der-length xs))))
  :rule-classes :type-prescription)

(in-theory (disable fn-tlsr-der-length))

; A host name's octets: printable ASCII without a space, at least one.
(defun fn-tlsr-name-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (or (not (consp (cdr xs))) (fn-tlsr-name-octetsp (cdr xs))))
    nil))

; The dNSNames of GeneralName items XS, in order, or :malformed.
(defun fn-tlsr-general-names (xs)
  (declare (xargs :guard t :measure (len xs)))
  (if (not (consp xs))
      nil
    (let ((tag (car xs))
          (header (fn-tlsr-der-length (cdr xs))))
      (if (or (not (natp tag)) (<= 256 tag) (equal (logand tag 31) 31)
              (not (consp header))
              (< (len (cdr header)) (car header)))
          :malformed
        (let* ((split (fn-tlsr-split (car header) (cdr header)))
               (content (car split))
               (rest (fn-tlsr-general-names (cdr split))))
          (cond ((equal rest :malformed) :malformed)
                ((not (equal tag 130)) rest)
                ((fn-tlsr-name-octetsp content) (cons content rest))
                (t :malformed)))))))

; The extension value: one SEQUENCE (0x30) holding exactly the items.  No
; extension (nil) names nothing; anything else unreadable is :malformed.
(defun fn-tlsr-san-names (octets)
  (declare (xargs :guard t))
  (cond ((null octets) nil)
        ((not (and (consp octets) (equal (car octets) 48))) :malformed)
        (t (let ((header (fn-tlsr-der-length (cdr octets))))
             (if (not (and (consp header)
                           (equal (len (cdr header)) (car header))))
                 :malformed
               (fn-tlsr-general-names (cdr header)))))))

(defthm fn-tlsr-general-names-true-listp
  (implies (not (equal (fn-tlsr-general-names xs) :malformed))
           (true-listp (fn-tlsr-general-names xs))))

(defthm fn-tlsr-san-names-true-listp
  (implies (not (equal (fn-tlsr-san-names octets) :malformed))
           (true-listp (fn-tlsr-san-names octets))))

(in-theory (disable fn-tlsr-san-names))

; -----------------------------------------------------------------------------
; The facts and the decision

(defun fn-tlsr-facts (chain key match not-before not-after san now)
  (declare (xargs :guard t))
  (list chain key match not-before not-after san now))

(defun fn-tlsr-fact (i facts)
  (declare (xargs :guard (natp i)))
  (if (true-listp facts) (nth i facts) nil))

(defun fn-tlsr-chain-loadedp (facts) (declare (xargs :guard t)) (and (fn-tlsr-fact 0 facts) t))
(defun fn-tlsr-key-loadedp (facts) (declare (xargs :guard t)) (and (fn-tlsr-fact 1 facts) t))
(defun fn-tlsr-key-matchesp (facts) (declare (xargs :guard t)) (and (fn-tlsr-fact 2 facts) t))
(defun fn-tlsr-not-before (facts) (declare (xargs :guard t)) (fn-tlsr-time-fields (fn-tlsr-fact 3 facts)))
(defun fn-tlsr-not-after (facts) (declare (xargs :guard t)) (fn-tlsr-time-fields (fn-tlsr-fact 4 facts)))
(defun fn-tlsr-names (facts) (declare (xargs :guard t)) (fn-tlsr-san-names (fn-tlsr-fact 5 facts)))
(defun fn-tlsr-now (facts) (declare (xargs :guard t)) (fn-tlsr-fact 6 facts))

; The window holds: both times parse, the clock is an integer, and
; notBefore <= now < notAfter (RFC 5280 section 4.1.2.5 makes both ends
; inclusive; a certificate is no longer used at its notAfter second here).
(defun fn-tlsr-currentp (facts)
  (declare (xargs :guard t))
  (and (fn-tlsr-not-before facts)
       (fn-tlsr-not-after facts)
       (integerp (fn-tlsr-now facts))
       (<= (fn-tlsr-seconds (fn-tlsr-not-before facts)) (fn-tlsr-now facts))
       (< (fn-tlsr-now facts) (fn-tlsr-seconds (fn-tlsr-not-after facts)))
       t))

; The names a served context answers for: its leaf's dNSNames, none when it
; has no subjectAltName or it is unreadable.
(defun fn-tlsr-served-names (served)
  (declare (xargs :guard t))
  (let ((names (fn-tlsr-names served)))
    (if (true-listp names) names nil)))

; (:accept NAMES NOT-AFTER-FIELDS) or (:refuse REASON).  FACTS are the
; candidate's, SERVED the facts of the context the owner serves now (nil at
; none).  The refusal names the first fact that fails, in the order the host
; observed them.  A renewal keeps every name the node answers for: a peer
; that verifies this node by one of them (SSL_set1_host) would otherwise
; fail its next handshake, so dropping a name is a restart, not a reload.
(defun fn-tlsr-decide (facts served)
  (declare (xargs :guard t))
  (cond ((not (fn-tlsr-chain-loadedp facts)) (list :refuse :chain-unreadable))
        ((not (fn-tlsr-key-loadedp facts)) (list :refuse :key-unreadable))
        ((not (fn-tlsr-key-matchesp facts)) (list :refuse :key-mismatch))
        ((not (and (fn-tlsr-not-before facts) (fn-tlsr-not-after facts)))
         (list :refuse :validity-malformed))
        ((not (integerp (fn-tlsr-now facts))) (list :refuse :clock-unusable))
        ((< (fn-tlsr-now facts) (fn-tlsr-seconds (fn-tlsr-not-before facts)))
         (list :refuse :not-yet-valid))
        ((<= (fn-tlsr-seconds (fn-tlsr-not-after facts)) (fn-tlsr-now facts))
         (list :refuse :expired))
        ((equal (fn-tlsr-names facts) :malformed) (list :refuse :names-malformed))
        ((not (subsetp-equal (fn-tlsr-served-names served) (fn-tlsr-names facts)))
         (list :refuse :names-dropped))
        (t (list :accept (fn-tlsr-names facts) (fn-tlsr-not-after facts)))))

(defun fn-tlsr-acceptp (decision)
  (declare (xargs :guard t))
  (and (consp decision) (equal (car decision) :accept)))

(defconst *fn-tlsr-refusals*
  '(:chain-unreadable :key-unreadable :key-mismatch :validity-malformed
    :clock-unusable :not-yet-valid :expired :names-malformed :names-dropped))

; KEYSTONE (PRF-212).  The subject is `fn-tlsr-decide', which
; host/tls-reload-host.lisp fn-tlsr-host-decide calls for
; host/native/tls-reload.lisp fnn-tls-owner-reload, the owner's handler of
; the kind-19 `reload' request; the host swaps the served context exactly
; when the decision is :accept and frees the candidate otherwise.  The new
; material is taken exactly when the chain and key loaded, the key matches,
; the clock lies in the validity window, the names are readable, and every
; name the served material answers for is still among them.
(defthm fn-tlsr-decide-accepts-exactly-loaded-matching-current-covering-material
  (iff (fn-tlsr-acceptp (fn-tlsr-decide facts served))
       (and (fn-tlsr-chain-loadedp facts)
            (fn-tlsr-key-loadedp facts)
            (fn-tlsr-key-matchesp facts)
            (fn-tlsr-currentp facts)
            (not (equal (fn-tlsr-names facts) :malformed))
            (subsetp-equal (fn-tlsr-served-names served) (fn-tlsr-names facts))))
  :hints (("Goal" :in-theory (disable fn-tlsr-chain-loadedp fn-tlsr-key-loadedp
                                      fn-tlsr-key-matchesp fn-tlsr-names
                                      fn-tlsr-served-names
                                      fn-tlsr-not-before fn-tlsr-not-after
                                      fn-tlsr-now fn-tlsr-seconds))))

; What an accepted decision carries is the parsed facts, and a refusal names
; one of the reasons above: the operator's line always has a word.
(defthm fn-tlsr-decide-carries-the-facts-or-a-named-refusal
  (let ((d (fn-tlsr-decide facts served)))
    (if (fn-tlsr-acceptp d)
        (equal d (list :accept (fn-tlsr-names facts) (fn-tlsr-not-after facts)))
      (and (equal (car d) :refuse)
           (member-equal (cadr d) *fn-tlsr-refusals*))))
  :hints (("Goal" :in-theory (disable fn-tlsr-chain-loadedp fn-tlsr-key-loadedp
                                      fn-tlsr-key-matchesp fn-tlsr-names
                                      fn-tlsr-served-names
                                      fn-tlsr-not-before fn-tlsr-not-after
                                      fn-tlsr-now fn-tlsr-seconds))))

; -----------------------------------------------------------------------------
; The served line, from the served context's facts:
;   tls names=A,B not-after=YYYY-MM-DDTHH:MM:SSZ
; with `names=none' for a leaf without dNSNames (a CN-only certificate),
; `unreadable' for a field that does not parse, and `tls none' when the
; owner serves no TLS.

(defun fn-tlsr-decimal (n width)
  (declare (xargs :guard (natp width)))
  (if (zp width)
      nil
    (append (fn-tlsr-decimal (floor (nfix n) 10) (- width 1))
            (list (+ 48 (mod (nfix n) 10))))))

(defun fn-tlsr-time-octets (fields)
  (declare (xargs :guard t))
  (if (and (true-listp fields) (equal (len fields) 6))
      (append (fn-tlsr-decimal (nth 0 fields) 4) (list 45)
              (fn-tlsr-decimal (nth 1 fields) 2) (list 45)
              (fn-tlsr-decimal (nth 2 fields) 2) (list 84)
              (fn-tlsr-decimal (nth 3 fields) 2) (list 58)
              (fn-tlsr-decimal (nth 4 fields) 2) (list 58)
              (fn-tlsr-decimal (nth 5 fields) 2) (list 90))
    (fn-record-string-octets "unreadable")))

(defun fn-tlsr-names-octets (names)
  (declare (xargs :guard t))
  (if (consp names)
      (append (if (fn-cbor-octet-listp (car names)) (true-list-fix (car names)) nil)
              (if (consp (cdr names))
                  (cons 44 (fn-tlsr-names-octets (cdr names)))
                nil))
    nil))

(defconst *fn-tlsr-none-line* (fn-record-string-octets "tls none"))

(defun fn-tlsr-served-line (served)
  (declare (xargs :guard t))
  (let ((names (fn-tlsr-names served)))
    (append (fn-record-string-octets "tls names=")
            (cond ((equal names :malformed) (fn-record-string-octets "unreadable"))
                  ((consp names) (fn-tlsr-names-octets names))
                  (t (fn-record-string-octets "none")))
            (fn-record-string-octets " not-after=")
            (fn-tlsr-time-octets (fn-tlsr-not-after served)))))

; The owner's log line for a reload, as octets: ACL2's words, the host
; writes them.  FACTS are the candidate's (served, when accepted).
(defun fn-tlsr-log-line (decision facts)
  (declare (xargs :guard t))
  (if (fn-tlsr-acceptp decision)
      (append (fn-record-string-octets "tls reload accepted: ")
              (fn-tlsr-served-line facts))
    (append (fn-record-string-octets "tls reload refused ")
            (fn-nctrl-reason-word (and (consp decision) (consp (cdr decision))
                                        (cadr decision)))
            (fn-record-string-octets ": the served certificate is unchanged"))))

; -----------------------------------------------------------------------------
; The frames: kind 19 (request) and kind 20 (reply)

(defconst *fn-tlsr-request-kind* 19)
(defconst *fn-tlsr-reply-kind* 20)
(defconst *fn-tlsr-max-word* 16)
(defconst *fn-tlsr-request-spec* (list (cons :blob *fn-tlsr-max-word*)))
(defconst *fn-tlsr-reload-word* (fn-record-string-octets "reload"))
(defconst *fn-tlsr-status-word* (fn-record-string-octets "status"))

; The served line is bounded by the record payload bound; a line over it is
; answered as the count of names (fn-tlsr-bounded-line), never cut.
(defconst *fn-tlsr-max-line* *fn-record-max-payload*)
(defconst *fn-tlsr-reply-spec*
  (list (cons :enum *fn-nctrl-statuses*)
        (cons :blob *fn-nctrl-max-reason-octets*)
        (cons :blob *fn-tlsr-max-line*)))

(defun fn-tlsr-request-encode (verb)
  (declare (xargs :guard t))
  (let ((word (cond ((equal verb :reload) *fn-tlsr-reload-word*)
                    ((equal verb :status) *fn-tlsr-status-word*)
                    (t nil))))
    (if (not word)
        :bad
      (fn-nctrl-seal *fn-tlsr-request-kind*
                     (fn-frame-fields-octets *fn-tlsr-request-spec* (list word))))))

(defun fn-tlsr-request-decode (octets)
  ; :reload, :status, or nil for any other frame.
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-tlsr-request-kind*)))
    (if (not (fn-frame-result-okp opened))
        nil
      (let ((payload (fn-frame-result-payload opened)))
        (if (not (fn-cbor-octet-listp payload))
            nil
          (let ((fields (fn-frame-fields-parse *fn-tlsr-request-spec* payload)))
            (if (not (fn-frame-parse-okp fields))
                nil
              (let ((values (fn-frame-parse-value fields)))
                (cond ((not (consp values)) nil)
                      ((equal (car values) *fn-tlsr-reload-word*) :reload)
                      ((equal (car values) *fn-tlsr-status-word*) :status)
                      (t nil))))))))))

; The line the owner answers for SERVED (nil: no TLS context), within the
; reply's bound: a list of names longer than the bound is answered as its
; count, never cut.
(defun fn-tlsr-reply-line (served)
  (declare (xargs :guard t))
  (if (null served)
      *fn-tlsr-none-line*
    (let ((line (fn-tlsr-served-line served)))
      (if (and (fn-cbor-octet-listp line) (<= (len line) *fn-tlsr-max-line*))
          line
        (append (fn-record-string-octets "tls names-count=")
                (fn-tlsr-decimal (len (fn-tlsr-served-names served)) 10)
                (fn-record-string-octets " not-after=")
                (fn-tlsr-time-octets (fn-tlsr-not-after served)))))))

(defun fn-tlsr-reply-encode (status reason line)
  (declare (xargs :guard t))
  (let ((values (list status (fn-nctrl-reason-word reason) line)))
    (if (not (and (member-equal status *fn-nctrl-statuses*)
                  (fn-frame-values-okp *fn-tlsr-reply-spec* values)))
        :bad
      (fn-nctrl-seal *fn-tlsr-reply-kind*
                     (fn-frame-fields-octets *fn-tlsr-reply-spec* values)))))

; What the client reads: (STATUS WORD LINE) from a kind-20 reply; an owner
; that predates kind 19 answers the plain kind 2 status, read as that status
; with the word owner-lacks-tls-reload and no line; else :bad.
(defun fn-tlsr-reply-read (octets)
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-tlsr-reply-kind*)))
    (if (fn-frame-result-okp opened)
        (let ((payload (fn-frame-result-payload opened)))
          (if (not (fn-cbor-octet-listp payload))
              :bad
            (let ((fields (fn-frame-fields-parse *fn-tlsr-reply-spec* payload)))
              (if (not (fn-frame-parse-okp fields))
                  :bad
                (let ((values (fn-frame-parse-value fields)))
                  (if (and (true-listp values) (equal (len values) 3))
                      values
                    :bad))))))
      (let ((plain (fn-native-control-reply-decode octets)))
        (if (member-equal plain *fn-nctrl-statuses*)
            (list plain (fn-record-string-octets "owner-lacks-tls-reload") nil)
          :bad)))))

; The line `status' prints for what it read: the served line, or `tls
; unknown REASON' when the owner did not answer with one.
(defun fn-tlsr-status-client-line (read)
  (declare (xargs :guard t))
  (if (and (true-listp read) (equal (len read) 3)
           (equal (car read) :accepted)
           (fn-cbor-octet-listp (caddr read)) (consp (caddr read)))
      (caddr read)
    (append (fn-record-string-octets "tls unknown ")
            (if (and (true-listp read) (equal (len read) 3)
                     (fn-cbor-octet-listp (cadr read)))
                (cadr read)
              (fn-record-string-octets "no-reply")))))
