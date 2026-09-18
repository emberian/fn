; fn: bounded semantic fields over the syntax-preserving article view.
;
; This book consumes successful `fn-article-parse` views; it does not scan a
; source a second time or reconstruct/normalize an article.  Message-ID values
; follow RFC 5536 section 3.1.3 (and retain RFC 3977's exact-octet identity),
; while Newsgroups follows RFC 5536 section 3.1.4.  The small proto-article
; gate implements only RFC 5537 section 3.4.1's relevant Message-ID,
; Newsgroups, Injection-Info, and Xref conditions.  It is not complete article
; validation or injection.

(in-package "ACL2")
(include-book "article")

(defconst *fn-af-max-message-id-octets* 250)
(defconst *fn-af-max-field-value-octets* 8192)

(defconst *fn-af-message-id-name* '(109 101 115 115 97 103 101 45 105 100))
(defconst *fn-af-newsgroups-name* '(110 101 119 115 103 114 111 117 112 115))
(defconst *fn-af-injection-info-name*
  '(105 110 106 101 99 116 105 111 110 45 105 110 102 111))
(defconst *fn-af-xref-name* '(120 114 101 102))

; -----------------------------------------------------------------------------
; Bounded octet grammars

(defun fn-af-wspp (byte)
  (or (equal byte 32) (equal byte 9)))

(defun fn-af-skip-wsp (bytes)
  (if (and (consp bytes) (fn-af-wspp (car bytes)))
      (fn-af-skip-wsp (cdr bytes))
    bytes))

(defun fn-af-trim-trailing-wsp-rev (rev-bytes)
  (if (and (consp rev-bytes) (fn-af-wspp (car rev-bytes)))
      (fn-af-trim-trailing-wsp-rev (cdr rev-bytes))
    rev-bytes))

(defun fn-af-trim-wsp (bytes)
  (declare (xargs :guard (true-listp bytes) :verify-guards nil))
  (reverse (fn-af-trim-trailing-wsp-rev
            (reverse (fn-af-skip-wsp bytes)))))

(defthm fn-af-guard-skip-wsp-true-listp
  (implies (true-listp bytes)
           (true-listp (fn-af-skip-wsp bytes)))
  :hints (("Goal" :induct (fn-af-skip-wsp bytes)
           :in-theory (enable fn-af-skip-wsp))))

(defthm fn-af-guard-trim-trailing-wsp-rev-true-listp
  (implies (true-listp bytes)
           (true-listp (fn-af-trim-trailing-wsp-rev bytes)))
  :hints (("Goal" :induct (fn-af-trim-trailing-wsp-rev bytes)
           :in-theory (enable fn-af-trim-trailing-wsp-rev))))

; RFC 5322 atext, imported by RFC 5536 section 3.1.3's dot-atom-text.
(defun fn-af-atextp (byte)
  (or (and (integerp byte) (<= 65 byte) (<= byte 90))
      (and (integerp byte) (<= 97 byte) (<= byte 122))
      (and (integerp byte) (<= 48 byte) (<= byte 57))
      (member-equal byte '(33 35 36 37 38 39 42 43 45 47 61 63 94 95
                            96 123 124 125 126))))

; 1*atext *('.' 1*atext).  The state says whether the next byte must be
; atext, which rejects both empty atoms and leading/trailing/doubled dots.
(defun fn-af-dot-atom-text-aux (bytes want-atext)
  (if (consp bytes)
      (if want-atext
          (and (fn-af-atextp (car bytes))
               (fn-af-dot-atom-text-aux (cdr bytes) nil))
        (if (equal (car bytes) 46)
            (fn-af-dot-atom-text-aux (cdr bytes) t)
          (and (fn-af-atextp (car bytes))
               (fn-af-dot-atom-text-aux (cdr bytes) nil))))
    (not want-atext)))

(defun fn-af-dot-atom-textp (bytes)
  (fn-af-dot-atom-text-aux bytes t))

; RFC 5536's mdtext excludes >, [, ], and backslash, while allowing an empty
; domain literal and preserving every permitted octet.
(defun fn-af-mdtextp (byte)
  (or (and (integerp byte) (<= 33 byte) (<= byte 61))
      (and (integerp byte) (<= 63 byte) (<= byte 90))
      (and (integerp byte) (<= 94 byte) (<= byte 126))))

(defun fn-af-no-fold-literal-restp (bytes)
  (if (consp bytes)
      (if (equal (car bytes) 93)
          (null (cdr bytes))
        (and (fn-af-mdtextp (car bytes))
             (fn-af-no-fold-literal-restp (cdr bytes))))
    nil))

(defun fn-af-id-rightp (bytes)
  (or (fn-af-dot-atom-textp bytes)
      (and (consp bytes) (equal (car bytes) 91)
           (fn-af-no-fold-literal-restp (cdr bytes)))))

; Split only the id-left at the required at-sign.  An at-sign within a legal
; bracketed id-right is consequently preserved rather than mistaken for a
; separator.
(defun fn-af-msg-id-core-aux (bytes left-rev)
  (declare (xargs :guard (true-listp left-rev) :verify-guards nil))
  (if (consp bytes)
      (if (equal (car bytes) 64)
          (and (fn-af-dot-atom-textp (reverse left-rev))
               (fn-af-id-rightp (cdr bytes)))
        (fn-af-msg-id-core-aux (cdr bytes) (cons (car bytes) left-rev)))
    nil))

(defun fn-af-msg-id-corep (bytes)
  (fn-af-msg-id-core-aux bytes nil))

(defun fn-af-msg-id-closep (bytes core-rev)
  (declare (xargs :guard (true-listp core-rev) :verify-guards nil))
  (if (consp bytes)
      (if (equal (car bytes) 62)
          (and (null (cdr bytes))
               (fn-af-msg-id-corep (reverse core-rev)))
        (fn-af-msg-id-closep (cdr bytes) (cons (car bytes) core-rev)))
    nil))

(defun fn-af-message-idp (octets)
  ; RFC 5536 section 3.1.3's 250 includes the angle brackets.  This preflight
  ; precedes octet traversal for callers not reached through article parsing.
  (and (fn-cbor-at-mostp octets *fn-af-max-message-id-octets*)
       (fn-cbor-octet-listp octets)
       (consp octets)
       (equal (car octets) 60)
       (fn-af-msg-id-closep (cdr octets) nil)))

(defun fn-af-message-id-equalp (left right)
  ; RFC 3977 appendix A.2 and OBJ-002: comparison is exact octet equality.
  (and (fn-af-message-idp left)
       (fn-af-message-idp right)
       (equal left right)))

; RFC 5536 section 3.1.4 newsgroup component characters.
(defun fn-af-newsgroup-component-charp (byte)
  (or (and (integerp byte) (<= 65 byte) (<= byte 90))
      (and (integerp byte) (<= 97 byte) (<= byte 122))
      (and (integerp byte) (<= 48 byte) (<= byte 57))
      (member-equal byte '(43 45 95))))

(defun fn-af-newsgroup-name-aux (bytes want-component-char)
  (if (consp bytes)
      (if want-component-char
          (and (fn-af-newsgroup-component-charp (car bytes))
               (fn-af-newsgroup-name-aux (cdr bytes) nil))
        (if (equal (car bytes) 46)
            (fn-af-newsgroup-name-aux (cdr bytes) t)
          (and (fn-af-newsgroup-component-charp (car bytes))
               (fn-af-newsgroup-name-aux (cdr bytes) nil))))
    (not want-component-char)))

(defun fn-af-newsgroup-namep (bytes)
  (fn-af-newsgroup-name-aux bytes t))

(defun fn-af-newsgroup-token-charp (byte)
  (or (fn-af-newsgroup-component-charp byte) (equal byte 46)))

(defun fn-af-take-newsgroup-token (bytes rev-token)
  (declare (xargs :guard (true-listp rev-token) :verify-guards nil))
  ; (:ok name rest), with no allocation before the caller's bounded field
  ; preflight.  A delimiter is retained in rest for the list grammar.
  (if (and (consp bytes) (fn-af-newsgroup-token-charp (car bytes)))
      (fn-af-take-newsgroup-token (cdr bytes) (cons (car bytes) rev-token))
    (list :ok (reverse rev-token) bytes)))

(defthm fn-af-guard-take-newsgroup-token-rest-true-listp
  (implies (true-listp bytes)
           (true-listp
            (car (cdr (cdr (fn-af-take-newsgroup-token bytes rev-token))))))
  :hints (("Goal" :induct (fn-af-take-newsgroup-token bytes rev-token)
           :in-theory (enable fn-af-take-newsgroup-token))))

(defun fn-af-newsgroup-list-parse-aux (bytes names-rev need-name fuel)
  ; One fuel unit is spent for every name/separator decision.  The 8,192-octet
  ; preflight supplies enough fuel while making termination independent of a
  ; caller's list shape.
  (declare (xargs :measure (nfix fuel)
                  :guard (and (true-listp bytes)
                              (true-listp names-rev)
                              (natp fuel))
                  :verify-guards nil))
  (if (zp fuel)
      (list :error :limit)
    (if need-name
        (let* ((token-result (fn-af-take-newsgroup-token bytes nil))
               (name (car (cdr token-result)))
               (rest (car (cdr (cdr token-result)))))
          (if (fn-af-newsgroup-namep name)
              (fn-af-newsgroup-list-parse-aux rest (cons name names-rev)
                                               nil (1- fuel))
            (list :error :invalid-newsgroups)))
      (let ((after-wsp (fn-af-skip-wsp bytes)))
        (if (null after-wsp)
            (list :ok (reverse names-rev))
          (if (equal (car after-wsp) 44)
              (fn-af-newsgroup-list-parse-aux
               (fn-af-skip-wsp (cdr after-wsp)) names-rev t (1- fuel))
            (list :error :invalid-newsgroups)))))))

(defun fn-af-newsgroup-list-parse (value)
  ; The article parser bounds an unfolded value by its 8,192-octet header cap;
  ; retaining this preflight makes the octet parser safe as a standalone call.
  (if (or (not (fn-cbor-at-mostp value *fn-af-max-field-value-octets*))
          (not (fn-cbor-octet-listp value)))
      (list :error :limit)
    (fn-af-newsgroup-list-parse-aux (fn-af-skip-wsp value) nil t
                                     *fn-af-max-field-value-octets*)))

; -----------------------------------------------------------------------------
; Semantic views of fields from a successful fn-article-parse result.
;
; These entry points require `article` to be fn-article-result-article of a
; successful fn-article-parse.  That parser's source/header/field bounds are
; the external-input preflight; this book intentionally does not become a
; second article parser.  The returned field object remains the parsed view,
; keeping raw lines and source provenance available to the injector.

(defun fn-af-message-id-field-value (field)
  (declare (xargs :guard (fn-article-fieldp field) :verify-guards nil))
  ; message-id = "Message-ID:" SP *WSP msg-id *WSP CRLF.  Its specific grammar
  ; has WSP, not FWS, so a folded field is not a valid Message-ID field here.
  (let ((raw-lines (fn-article-field-raw-lines field))
        (value (fn-article-field-unfolded-value field)))
    (if (and (consp raw-lines) (null (cdr raw-lines))
             (consp value) (equal (car value) 32))
        (let ((id (fn-af-trim-wsp (cdr value))))
          (if (fn-af-message-idp id) id nil))
      nil)))

(defun fn-af-newsgroups-field-value (field)
  (declare (xargs :guard (fn-article-fieldp field) :verify-guards nil))
  ; newsgroups = "Newsgroups:" SP newsgroup-list CRLF.  Newsgroup-list allows
  ; FWS around commas; the syntax parser has already unfolded it to WSP.
  (let ((value (fn-article-field-unfolded-value field)))
    (if (and (consp value) (equal (car value) 32))
        (fn-af-newsgroup-list-parse (cdr value))
      (list :error :invalid-newsgroups))))

(defun fn-af-message-id-status (article)
  (declare (xargs :guard (fn-article-syntax-p article) :verify-guards nil))
  ; (:missing) | (:duplicate fields) | (:invalid field) | (:single id field)
  (let ((fields (fn-article-get-headers article *fn-af-message-id-name*)))
    (if (null fields)
        '(:missing)
      (if (consp (cdr fields))
          (list :duplicate fields)
        (let ((id (fn-af-message-id-field-value (car fields))))
          (if id
              (list :single id (car fields))
            (list :invalid (car fields))))))))

(defun fn-af-newsgroups-status (article)
  (declare (xargs :guard (fn-article-syntax-p article) :verify-guards nil))
  ; (:missing) | (:duplicate fields) | (:invalid field) | (:single names field)
  (let ((fields (fn-article-get-headers article *fn-af-newsgroups-name*)))
    (if (null fields)
        '(:missing)
      (if (consp (cdr fields))
          (list :duplicate fields)
        (let ((parsed (fn-af-newsgroups-field-value (car fields))))
          (if (and (consp parsed) (equal (car parsed) :ok))
              (list :single (car (cdr parsed)) (car fields))
            (list :invalid (car fields))))))))

(defun fn-af-status-kind (status)
  (declare (xargs :guard (true-listp status) :verify-guards nil))
  (car status))
(defun fn-af-status-value (status)
  (declare (xargs :guard (true-listp status) :verify-guards nil))
  (car (cdr status)))
(defun fn-af-status-field (status)
  (declare (xargs :guard (true-listp status) :verify-guards nil))
  (car (cdr (cdr status))))

(defun fn-af-proto-article-check (article)
  (declare (xargs :guard (fn-article-syntax-p article) :verify-guards nil))
  ; RFC 5537 section 3.4.1 subset.  A valid supplied Message-ID is retained
  ; exactly; absence is accepted for a later injector to generate.  Neither
  ; generated fields nor configuration/admission decisions occur here.
  (if (consp (fn-article-get-headers article *fn-af-injection-info-name*))
      '(:error :injection-info)
    (if (consp (fn-article-get-headers article *fn-af-xref-name*))
        '(:error :xref)
      (let ((groups (fn-af-newsgroups-status article))
            (identity (fn-af-message-id-status article)))
        (if (equal (fn-af-status-kind groups) :missing)
            '(:error :newsgroups-missing)
          (if (equal (fn-af-status-kind groups) :duplicate)
              '(:error :newsgroups-duplicate)
            (if (equal (fn-af-status-kind groups) :invalid)
                '(:error :newsgroups-invalid)
              (if (equal (fn-af-status-kind identity) :duplicate)
                  '(:error :message-id-duplicate)
                (if (equal (fn-af-status-kind identity) :invalid)
                    '(:error :message-id-invalid)
                  (list :ok
                        (if (equal (fn-af-status-kind identity) :single)
                            (fn-af-status-value identity)
                          nil)
                        (fn-af-status-value groups)
                        (if (equal (fn-af-status-kind identity) :single)
                            (fn-af-status-field identity)
                          nil)
                        (fn-af-status-field groups)))))))))))

(defthm fn-af-message-id-equalp-is-exact
  (implies (and (fn-af-message-idp left) (fn-af-message-idp right))
           (iff (fn-af-message-id-equalp left right)
                (equal left right))))

(defthm fn-af-guard-get-headers-aux-car-fieldp
  (implies (and (fn-article-field-listp fields)
                (consp (fn-article-get-headers-aux fields name)))
           (fn-article-fieldp
            (car (fn-article-get-headers-aux fields name))))
  :hints (("Goal" :induct (fn-article-get-headers-aux fields name)
           :in-theory (enable fn-article-get-headers-aux))))

; Isolated complete guard graph.
(verify-guards fn-af-wspp)
(verify-guards fn-af-skip-wsp)
(verify-guards fn-af-trim-trailing-wsp-rev)
(verify-guards fn-af-trim-wsp)
(verify-guards fn-af-atextp)
(verify-guards fn-af-dot-atom-text-aux)
(verify-guards fn-af-dot-atom-textp)
(verify-guards fn-af-mdtextp)
(verify-guards fn-af-no-fold-literal-restp)
(verify-guards fn-af-id-rightp)
(verify-guards fn-af-msg-id-core-aux)
(verify-guards fn-af-msg-id-corep)
(verify-guards fn-af-msg-id-closep)
(verify-guards fn-af-message-idp)
(verify-guards fn-af-message-id-equalp)
(verify-guards fn-af-newsgroup-component-charp)
(verify-guards fn-af-newsgroup-name-aux)
(verify-guards fn-af-newsgroup-namep)
(verify-guards fn-af-newsgroup-token-charp)
(verify-guards fn-af-take-newsgroup-token)
(verify-guards fn-af-newsgroup-list-parse-aux)
(verify-guards fn-af-newsgroup-list-parse)
(verify-guards fn-af-message-id-field-value)
(verify-guards fn-af-newsgroups-field-value)
(verify-guards fn-af-message-id-status)
(verify-guards fn-af-newsgroups-status)
(verify-guards fn-af-status-kind)
(verify-guards fn-af-status-value)
(verify-guards fn-af-status-field)
(verify-guards fn-af-proto-article-check)
