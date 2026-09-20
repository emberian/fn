; fn: the Path header field content (RFC 5536 section 3.1.6, RFC 5537
; section 3.2) as a bounded reader, and the relaying-agent loop test of
; RFC 5537 section 3.6.
;
; Path content is a "!"-separated list of entries read left to right.  An
; entry is a <path-identity> (1*( ALPHA / DIGIT / "-" / "_" / "." ), no
; leading or trailing "."), the empty <diag-match> that two consecutive "!"
; produce, or a <diag-other> beginning with "." (".POSTED", ".SEEN.<x>",
; ".MISMATCH.<x>").  The rightmost entry is the <tail-entry>.  The loop test
; (RFC 5537 section 3.6, paragraph 3) asks whether an identity "appears as a
; <path-identity> (excluding within the <tail-entry> or following a "POSTED"
; <diag-keyword>)".  Nothing here rewrites a Path: the outbound rendering is
; the feed lane's (specs/peering.md section 2.3), and the stored source bytes
; are never altered (D01).
;
; Every reader is total and structural; no octet is interpreted through the
; Lisp reader.  The field value arrives already unfolded from
; books/article.lisp, so a folded Path is one octet list here.

(in-package "ACL2")
(include-book "article-fields")

(defconst *fn-path-name* '(112 97 116 104))                     ; "path"
(defconst *fn-path-date-name* '(100 97 116 101))                ; "date"
(defconst *fn-path-injection-date-name*
  '(105 110 106 101 99 116 105 111 110 45 100 97 116 101))      ; "injection-date"
(defconst *fn-path-posted-diag* '(46 80 79 83 84 69 68))        ; ".POSTED"
(defconst *fn-path-bang* 33)

; -----------------------------------------------------------------------------
; Total list vocabulary

(defun fn-path-rev-onto (xs acc)
  (declare (xargs :guard t))
  (if (consp xs) (fn-path-rev-onto (cdr xs) (cons (car xs) acc)) acc))

(defun fn-path-reverse (xs)
  (declare (xargs :guard t))
  (fn-path-rev-onto xs nil))

(defun fn-path-wspp (b)
  (declare (xargs :guard t))
  (or (equal b 32) (equal b 9)))

(defun fn-path-trim-leading (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (fn-path-wspp (car xs)))
      (fn-path-trim-leading (cdr xs))
    xs))

; Both ends: RFC 5536 permits FWS after "!" and the unfolding leaves WSP.
(defun fn-path-trim (xs)
  (declare (xargs :guard t))
  (fn-path-reverse (fn-path-trim-leading (fn-path-reverse (fn-path-trim-leading xs)))))

(defun fn-path-last-octet (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs)) (fn-path-last-octet (cdr xs)) (car xs))
    nil))

(defun fn-path-butlast (xs)
  ; Every entry but the <tail-entry>.
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)))
      (cons (car xs) (fn-path-butlast (cdr xs)))
    nil))

(defun fn-path-strip-prefix (prefix xs)
  ; (:ok rest) when prefix is a prefix of xs, else nil.
  (declare (xargs :guard t))
  (if (consp prefix)
      (if (and (consp xs) (equal (car xs) (car prefix)))
          (fn-path-strip-prefix (cdr prefix) (cdr xs))
        nil)
    (list :ok xs)))

; -----------------------------------------------------------------------------
; <path-identity>

(defun fn-path-identity-charp (b)
  (declare (xargs :guard t))
  (and (integerp b)
       (or (and (<= 48 b) (<= b 57))
           (and (<= 65 b) (<= b 90))
           (and (<= 97 b) (<= b 122))
           (equal b 45) (equal b 95) (equal b 46))))

(defun fn-path-identity-charsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-path-identity-charp (car xs)) (fn-path-identity-charsp (cdr xs)))
    (null xs)))

(defun fn-path-identityp (octets)
  (declare (xargs :guard t))
  (and (consp octets)
       (fn-path-identity-charsp octets)
       (not (equal (car octets) 46))
       (not (equal (fn-path-last-octet octets) 46))))

; -----------------------------------------------------------------------------
; Entries

(defun fn-path-split-aux (octets entry-rev entries-rev)
  (declare (xargs :guard t))
  (if (consp octets)
      (if (equal (car octets) *fn-path-bang*)
          (fn-path-split-aux (cdr octets) nil
                             (cons (fn-path-trim (fn-path-reverse entry-rev))
                                   entries-rev))
        (fn-path-split-aux (cdr octets) (cons (car octets) entry-rev)
                           entries-rev))
    (fn-path-reverse (cons (fn-path-trim (fn-path-reverse entry-rev))
                           entries-rev))))

(defun fn-path-entries (octets)
  ; Left to right; the last element is the <tail-entry>.
  (declare (xargs :guard t))
  (fn-path-split-aux octets nil nil))

(defun fn-path-leftmost (octets)
  (declare (xargs :guard t))
  (car (fn-path-entries octets)))

; ".POSTED" exactly, or ".POSTED." followed by the source (RFC 5537 3.2.1
; step 2).  The keyword is compared exactly: diag-keyword is 1*ALPHA and the
; RFC spells this one in upper case.
(defun fn-path-posted-diagp (entry)
  (declare (xargs :guard t))
  (let ((r (fn-path-strip-prefix *fn-path-posted-diag* entry)))
    (and (consp r) (consp (cdr r))
         (let ((rest (car (cdr r))))
           (or (null rest) (and (consp rest) (equal (car rest) 46)))))))

(defun fn-path-names-in-p (entries identity)
  ; identity appears as an entry, stopping at a POSTED diagnostic: everything
  ; to its right was added before injection and is not a relaying identity.
  (declare (xargs :guard t))
  (if (consp entries)
      (if (fn-path-posted-diagp (car entries))
          nil
        (or (equal (car entries) identity)
            (fn-path-names-in-p (cdr entries) identity)))
    nil))

; The loop test.  A non-identity (empty or diagnostic) never names anything,
; so an unset local identity (the empty policy slot) never matches.
(defun fn-path-names-p (path-octets identity)
  (declare (xargs :guard t))
  (and (fn-path-identityp identity)
       (fn-path-names-in-p (fn-path-butlast (fn-path-entries path-octets))
                           identity)))

; RFC 5537 section 3.2.1 step 3, decided from the peer record's expected
; identity, never from the article: (:match) or (:mismatch expected).
(defun fn-path-diagnostic (expected-identity path-octets)
  (declare (xargs :guard t))
  (if (equal (fn-path-leftmost path-octets) expected-identity)
      (list :match)
    (list :mismatch expected-identity)))

; -----------------------------------------------------------------------------
; The fields a transit decision reads

(defun fn-path-single-field-value (article name)
  ; The trimmed unfolded value of the one field named name; nil if absent,
  ; repeated, or not a field.
  (declare (xargs :guard (fn-article-syntax-p article)))
  (let ((fields (fn-article-get-headers article name)))
    (if (and (consp fields) (null (cdr fields))
             (fn-article-fieldp (car fields)))
        (fn-path-trim (fn-article-field-unfolded-value (car fields)))
      nil)))

(defun fn-af-path-field-value (article)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (fn-path-single-field-value article *fn-path-name*))

; RFC 5537 section 3.6 step 1 / 3.7 step 2: Injection-Date or, if absent, Date.
(defun fn-path-date-presentp (article)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (or (consp (fn-article-get-headers article *fn-path-injection-date-name*))
      (consp (fn-article-get-headers article *fn-path-date-name*))))

; The loop test's three exclusions (tail-entry, after POSTED, not a substring)
; are witnessed on concrete Paths in tests/acl2/peer-inbound-tests.lisp; a
; general theorem over an arbitrary identity is recorded open in
; specs/peering.md (status).

; -----------------------------------------------------------------------------
; Export theory: the readers are proof vocabulary; only the two field
; projections and the loop test stay enabled as glue predicates.

(deftheory fn-path-vocabulary
  '((:d fn-path-rev-onto) (:d fn-path-reverse) (:d fn-path-wspp)
    (:d fn-path-trim-leading) (:d fn-path-trim) (:d fn-path-last-octet)
    (:d fn-path-butlast) (:d fn-path-strip-prefix)
    (:d fn-path-identity-charp) (:d fn-path-identity-charsp)
    (:d fn-path-identityp) (:d fn-path-split-aux) (:d fn-path-entries)
    (:d fn-path-leftmost) (:d fn-path-posted-diagp) (:d fn-path-names-in-p)
    (:d fn-path-names-p) (:d fn-path-diagnostic)
    (:d fn-path-single-field-value) (:d fn-af-path-field-value)
    (:d fn-path-date-presentp)))

(in-theory (disable fn-path-vocabulary))
