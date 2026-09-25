; fn: bounded, syntax-preserving received-article parser.
;
; This local executable profile parses CRLF-framed US-ASCII header syntax and
; leaves body octets opaque.  It is intentionally not an RFC 5536 article
; validator or RFC 5537 injection agent: required fields, duplicate policies,
; Message-ID/Date/address/Newsgroups grammars, MIME semantics, and provenance
; are separate work.  See specs/article-parser.md for the exact local bounds and
; grammar.  Input is always octets; no Lisp reader, symbol interning, or host
; text decoding is used.

(in-package "ACL2")
(include-book "cbor")
(include-book "std/lists/rev" :dir :system)

; Bounds (D27, planning/decisions.md; design 2026-09-25-bounds §2.3).
;
; Codec ceiling, not policy: the widest article a record can carry, equal to
; the record codec's payload ceiling `*fn-record-max-payload*'
; (books/records-shape.lisp; the equality is
; `fn-nctrl-article-ceiling-is-the-record-payload-ceiling',
; books/native-control, the first book that sees both).
; The operator's article bound is the store profile's, and every served path
; hands the parser at most that many octets first (the injection
; configuration's max-octets, `fn-inj-decide').
(defconst *fn-article-max-octets* 4261412864)
; Work bounds.  The header parse's certified work bound
; (`fn-article-parse-work-profile-bound', books/article-public-bound) is
; fuel-per-header-line times input length, so these three are what keep a
; header's parse linear in the article: removing them needs a work theorem
; linear in the header, not a larger constant.  They bound the work of one
; parse, not what a store holds.
(defconst *fn-article-max-header-octets* 16384)
(defconst *fn-article-max-header-lines* 256)
(defconst *fn-article-max-fields* 64)
; RFC 5322 §2.1.1: a line is at most 998 octets.
(defconst *fn-article-max-line-octets* 998)

; -----------------------------------------------------------------------------
; Octet grammar helpers

(defun fn-article-wspp (byte)
  (declare (xargs :guard t))
  (or (equal byte 32) (equal byte 9)))

(defun fn-article-vcharp (byte)
  (declare (xargs :guard t))
  (and (integerp byte) (<= 33 byte) (<= byte 126)))

; RFC 5322 ftext, used by RFC 5536 header field names.
(defun fn-article-ftextp (byte)
  (declare (xargs :guard t))
  (or (and (integerp byte) (<= 33 byte) (<= byte 57))
      (and (integerp byte) (<= 59 byte) (<= byte 126))))

(defun fn-article-header-bytep (byte)
  (declare (xargs :guard t))
  (or (fn-article-wspp byte) (fn-article-vcharp byte)))

(defun fn-article-header-bytes-p (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (fn-article-header-bytep (car bytes))
           (fn-article-header-bytes-p (cdr bytes)))
    (null bytes)))

(defun fn-article-has-vcharp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (or (fn-article-vcharp (car bytes))
          (fn-article-has-vcharp (cdr bytes)))
    nil))

(defun fn-article-ascii-downcase-byte (byte)
  (declare (xargs :guard t))
  (if (and (integerp byte) (<= 65 byte) (<= byte 90))
      (+ byte 32)
    byte))

(defun fn-article-ascii-downcase (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (cons (fn-article-ascii-downcase-byte (car bytes))
            (fn-article-ascii-downcase (cdr bytes)))
    nil))

(defun fn-article-ftext-listp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (fn-article-ftextp (car bytes))
           (fn-article-ftext-listp (cdr bytes)))
    (null bytes)))

(defun fn-article-namep (name)
  (declare (xargs :guard t))
  (and (consp name) (fn-article-ftext-listp name)))

(defun fn-article-lower-namep (name)
  (declare (xargs :guard t))
  (and (fn-article-namep name)
       (equal name (fn-article-ascii-downcase name))))

; -----------------------------------------------------------------------------
; Parsed article and field views

; Article: (raw-header body fields).  `fn-article-source` reconstructs the
; exact received source as header ++ CRLF ++ body; raw field lines preserve
; field order and folding independently of the parsed lookup view.
(defun fn-article-header (article)
  (declare (xargs :guard (true-listp article)))
  (car article))
(defun fn-article-body (article)
  (declare (xargs :guard (true-listp article)))
  (car (cdr article)))
(defun fn-article-fields (article)
  (declare (xargs :guard (true-listp article)))
  (car (cdr (cdr article))))

(defun fn-article-make (header body fields)
  (declare (xargs :guard t))
  (list header body fields))

(defun fn-article-source (article)
  (declare (xargs :guard (and (true-listp article)
                              (true-listp (fn-article-header article)))))
  (append (fn-article-header article) '(13 10) (fn-article-body article)))

; Field: (raw-lines lower-name unfolded-value).  Raw lines exclude their CRLF;
; unfolded-value removes only folding CRLF and retains continuation WSP.
(defun fn-article-field-raw-lines (field)
  (declare (xargs :guard (true-listp field)))
  (car field))
(defun fn-article-field-name (field)
  (declare (xargs :guard (true-listp field)))
  (car (cdr field)))
(defun fn-article-field-unfolded-value (field)
  (declare (xargs :guard (true-listp field)))
  (car (cdr (cdr field))))

(defun fn-article-make-field (raw-lines lower-name unfolded-value)
  (declare (xargs :guard t))
  (list raw-lines lower-name unfolded-value))

(defun fn-article-fieldp (field)
  (declare (xargs :guard t))
  (and (true-listp field)
       (equal (len field) 3)
       (true-listp (fn-article-field-raw-lines field))
       (fn-article-lower-namep (fn-article-field-name field))
       (fn-article-header-bytes-p (fn-article-field-unfolded-value field))))

(defun fn-article-field-listp (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (fn-article-fieldp (car fields))
           (fn-article-field-listp (cdr fields)))
    (null fields)))

(defun fn-article-syntax-p (article)
  (declare (xargs :guard t))
  (and (true-listp article)
       (equal (len article) 3)
       (fn-cbor-octet-listp (fn-article-header article))
       (fn-cbor-octet-listp (fn-article-body article))
       (fn-article-field-listp (fn-article-fields article))))

(defun fn-article-result-okp (result)
  (declare (xargs :guard t))
  (and (consp result) (equal (car result) :ok)))

(defun fn-article-result-article (result)
  (declare (xargs :guard (true-listp result)))
  (car (cdr result)))

(defun fn-article-error (code)
  (declare (xargs :guard t))
  (list :error code))
(defun fn-article-ok (article)
  (declare (xargs :guard t))
  (list :ok article))

; -----------------------------------------------------------------------------
; Line and field syntax

; Result: (:ok line remaining) | (:error code).  A line is its octets without
; CRLF.  The fixed `left` fuel bounds both line allocation and scanning.
(defun fn-article-next-line-aux (octets line-rev left)
  (declare (xargs :measure (acl2-count octets)
                  :guard (and (true-listp line-rev) (natp left))))
  (if (consp octets)
      (if (equal (car octets) 13)
          (if (and (consp (cdr octets)) (equal (car (cdr octets)) 10))
              (list :ok (reverse line-rev) (cdr (cdr octets)))
            (fn-article-error :invalid-header))
        (if (equal (car octets) 10)
            (fn-article-error :invalid-header)
          (if (zp left)
              (fn-article-error :limit)
            (fn-article-next-line-aux (cdr octets) (cons (car octets) line-rev)
                                      (1- left)))))
    (fn-article-error :missing-separator)))

(defun fn-article-next-line (octets)
  (declare (xargs :guard t))
  (fn-article-next-line-aux octets nil *fn-article-max-line-octets*))

(defun fn-article-line-okp (result)
  (declare (xargs :guard t))
  (and (consp result) (equal (car result) :ok)))

(defun fn-article-line-value (result)
  (declare (xargs :guard (true-listp result)))
  (car (cdr result)))
(defun fn-article-line-rest (result)
  (declare (xargs :guard (true-listp result)))
  (car (cdr (cdr result))))

; Find the first colon.  Header values may contain later colons unchanged.
(defun fn-article-split-colon-aux (line name-rev)
  (declare (xargs :guard (true-listp name-rev)))
  (if (consp line)
      (if (equal (car line) 58)
          (list :ok (reverse name-rev) (cdr line))
        (fn-article-split-colon-aux (cdr line) (cons (car line) name-rev)))
    (fn-article-error :invalid-header)))

(defun fn-article-new-field (line)
  (declare (xargs :guard t))
  (let ((split (fn-article-split-colon-aux line nil)))
    (if (not (fn-article-line-okp split))
        split
      (let ((name (fn-article-line-value split))
            (value (fn-article-line-rest split)))
        (if (and (fn-article-namep name)
                 (consp value)
                 (fn-article-wspp (car value))
                 (fn-article-header-bytes-p value)
                 (fn-article-has-vcharp value))
            (list :ok (fn-article-make-field
                       (list line) (fn-article-ascii-downcase name) value))
          (fn-article-error :invalid-header))))))

(defun fn-article-fold-linep (line)
  (declare (xargs :guard t))
  (and (consp line)
       (fn-article-wspp (car line))
       (fn-article-header-bytes-p line)
       (fn-article-has-vcharp line)))

(defun fn-article-add-fold (field line)
  (declare (xargs :guard (and (fn-article-fieldp field)
                              (true-listp line))))
  (fn-article-make-field
   (append (fn-article-field-raw-lines field) (list line))
   (fn-article-field-name field)
   (append (fn-article-field-unfolded-value field) line)))

(defun fn-article-header-rev-add-line (header-rev line)
  (declare (xargs :guard (and (true-listp header-rev)
                              (true-listp line))))
  (append '(10 13) (reverse line) header-rev))

; Each accepted physical header line contributes exactly itself and its CRLF to
; the forward header view.  This is the induction step behind source splitting.
(defthm fn-article-header-rev-add-line-recomposes
  (implies (and (true-listp header-rev) (true-listp line))
           (equal (rev (fn-article-header-rev-add-line header-rev line))
                  (append (rev header-rev) line '(13 10)))))

(defun fn-article-finish-fields (fields-rev current)
  (declare (xargs :guard (true-listp fields-rev)))
  (if current
      (reverse (cons current fields-rev))
    (reverse fields-rev)))

; Body framing is intentionally the only body syntax checked here: binary
; non-CR/LF octets are opaque, while CR and LF must occur only as CRLF pairs.
(defun fn-article-body-crlfp (body)
  (declare (xargs :measure (acl2-count body) :guard t))
  (if (consp body)
      (if (equal (car body) 13)
          (and (consp (cdr body)) (equal (car (cdr body)) 10)
               (fn-article-body-crlfp (cdr (cdr body))))
        (and (not (equal (car body) 10))
             (fn-article-body-crlfp (cdr body))))
    t))

; Parse until the first blank line.  `lines-left` is a local allocation/work
; limit, so recursive termination and hostile-input work do not depend on an
; untrusted header count.  The public entry gives it one extra step: 128
; nonblank physical header lines are permitted, followed by their separator.
(defun fn-article-parse-lines (octets lines-left header-bytes fields-rev current
                                      header-rev)
  (declare (xargs :measure (nfix lines-left)
                  :guard (and (true-listp octets)
                              (natp lines-left)
                              (natp header-bytes)
                              (true-listp fields-rev)
                              (or (null current)
                                  (fn-article-fieldp current))
                              (true-listp header-rev))
                  :verify-guards nil))
  (if (zp lines-left)
      (fn-article-error :limit)
    (let ((next (fn-article-next-line octets)))
      (if (not (fn-article-line-okp next))
          next
        (let ((line (fn-article-line-value next))
              (rest (fn-article-line-rest next)))
          (if (null line)
              (if (not (fn-article-body-crlfp rest))
                  (fn-article-error :invalid-header)
                (fn-article-ok
                 (fn-article-make
                  (reverse header-rev) rest
                  (fn-article-finish-fields fields-rev current))))
            (if (< *fn-article-max-header-octets*
                   (+ header-bytes (len line) 2))
                (fn-article-error :limit)
              (if (fn-article-wspp (car line))
                  (if (not current)
                      (fn-article-error :invalid-header)
                    (if (not (fn-article-fold-linep line))
                        (fn-article-error :invalid-header)
                      (fn-article-parse-lines
                       rest (1- lines-left) (+ header-bytes (len line) 2)
                       fields-rev (fn-article-add-fold current line)
                       (fn-article-header-rev-add-line header-rev line))))
                (let ((field-result (fn-article-new-field line)))
                  (if (not (fn-article-line-okp field-result))
                      field-result
                    (if (and current
                             (<= (1- *fn-article-max-fields*)
                                 (len fields-rev)))
                        (fn-article-error :limit)
                      (fn-article-parse-lines
                       rest (1- lines-left) (+ header-bytes (len line) 2)
                       (if current (cons current fields-rev) fields-rev)
                       (fn-article-line-value field-result)
                       (fn-article-header-rev-add-line header-rev line)))))))))))))

(defun fn-article-parse (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-at-mostp octets *fn-article-max-octets*))
      (fn-article-error :limit)
    (if (not (fn-cbor-octet-listp octets))
      (fn-article-error :invalid-header)
      (fn-article-parse-lines octets (1+ *fn-article-max-header-lines*)
                              0 nil nil nil))))

; -----------------------------------------------------------------------------
; Lookup helpers.  Names are lowercased ftext octet lists; callers retain the
; raw field lines/source for all semantic interpretation and future policy.

(defun fn-article-field-name-equalp (field name)
  (declare (xargs :guard (true-listp field)))
  (equal (fn-article-field-name field) (fn-article-ascii-downcase name)))

(defun fn-article-get-headers-aux (fields name)
  (declare (xargs :guard (fn-article-field-listp fields)))
  (if (consp fields)
      (let ((field (car fields)))
        (if (fn-article-field-name-equalp field name)
            (cons field (fn-article-get-headers-aux (cdr fields) name))
          (fn-article-get-headers-aux (cdr fields) name)))
    nil))

(defun fn-article-get-headers (article name)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (fn-article-get-headers-aux (fn-article-fields article) name))

(defun fn-article-get-header (article name)
  (declare (xargs :guard (fn-article-syntax-p article)))
  (let ((headers (fn-article-get-headers article name)))
    (if (consp headers) (car headers) nil)))

; -----------------------------------------------------------------------------
; Guard domains and typed intermediate results.

(defthm fn-article-header-bytes-true-listp
  (implies (fn-article-header-bytes-p bytes)
           (true-listp bytes))
  :hints (("Goal" :induct (fn-article-header-bytes-p bytes))))

(defthm fn-article-field-list-true-listp
  (implies (fn-article-field-listp fields)
           (true-listp fields))
  :hints (("Goal" :induct (fn-article-field-listp fields))))

(defthm fn-article-octet-list-true-listp
  (implies (fn-cbor-octet-listp octets)
           (true-listp octets))
  :hints (("Goal" :induct (fn-cbor-octet-listp octets))))

(defthm fn-article-next-line-aux-result-listp
  (implies (true-listp line-rev)
           (true-listp (fn-article-next-line-aux octets line-rev left)))
  :hints (("Goal"
           :induct (fn-article-next-line-aux octets line-rev left))))

(defthm fn-article-next-line-aux-value-listp
  (implies (and (true-listp line-rev)
                (fn-article-line-okp
                 (fn-article-next-line-aux octets line-rev left)))
           (true-listp
            (fn-article-line-value
             (fn-article-next-line-aux octets line-rev left))))
  :hints (("Goal"
           :induct (fn-article-next-line-aux octets line-rev left))))

(defthm fn-article-next-line-aux-rest-listp
  (implies (and (true-listp octets)
                (fn-article-line-okp
                 (fn-article-next-line-aux octets line-rev left)))
           (true-listp
            (fn-article-line-rest
             (fn-article-next-line-aux octets line-rev left))))
  :hints (("Goal"
           :induct (fn-article-next-line-aux octets line-rev left))))

(defthm fn-article-next-line-value-listp
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (true-listp
            (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal"
           :use ((:instance fn-article-next-line-aux-value-listp
                  (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (e/d (fn-article-next-line)
                           (fn-article-next-line-aux)))))

(defthm fn-article-next-line-rest-listp
  (implies (and (true-listp octets)
                (fn-article-line-okp (fn-article-next-line octets)))
           (true-listp
            (fn-article-line-rest (fn-article-next-line octets))))
  :hints (("Goal"
           :use ((:instance fn-article-next-line-aux-rest-listp
                  (line-rev nil) (left *fn-article-max-line-octets*)))
           :in-theory (e/d (fn-article-next-line)
                           (fn-article-next-line-aux)))))

(defthm fn-article-split-colon-result-listp
  (implies (true-listp name-rev)
           (true-listp (fn-article-split-colon-aux line name-rev)))
  :hints (("Goal"
           :induct (fn-article-split-colon-aux line name-rev))))

(defthm fn-article-new-field-result-listp
  (true-listp (fn-article-new-field line))
  :hints (("Goal"
           :use ((:instance fn-article-split-colon-result-listp
                  (name-rev nil)))
           :in-theory (enable fn-article-new-field))))

(defthm fn-article-ascii-downcase-idempotent
  (equal (fn-article-ascii-downcase (fn-article-ascii-downcase bytes))
         (fn-article-ascii-downcase bytes))
  :hints (("Goal" :induct (fn-article-ascii-downcase bytes))))

(defthm fn-article-ascii-downcase-preserves-ftext
  (implies (fn-article-ftext-listp bytes)
           (fn-article-ftext-listp (fn-article-ascii-downcase bytes)))
  :hints (("Goal" :induct (fn-article-ftext-listp bytes))))

(defthm fn-article-ascii-downcase-preserves-consp
  (implies (consp bytes)
           (consp (fn-article-ascii-downcase bytes))))

(defthm fn-article-new-field-success-fieldp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (fn-article-fieldp
            (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal"
           :in-theory (enable fn-article-new-field
                              fn-article-line-okp
                              fn-article-line-value
                              fn-article-fieldp))))

(defthm fn-article-header-bytes-append
  (implies (true-listp left)
           (equal (fn-article-header-bytes-p (append left right))
                  (and (fn-article-header-bytes-p left)
                       (fn-article-header-bytes-p right))))
  :hints (("Goal" :induct (fn-article-header-bytes-p left))))

(defthm fn-article-add-fold-fieldp
  (implies (and (fn-article-fieldp field)
                (fn-article-fold-linep line))
           (fn-article-fieldp (fn-article-add-fold field line)))
  :hints (("Goal"
           :in-theory (enable fn-article-fieldp fn-article-add-fold
                              fn-article-fold-linep))))

(defthm fn-article-header-rev-add-line-listp
  (implies (and (true-listp header-rev) (true-listp line))
           (true-listp
            (fn-article-header-rev-add-line header-rev line)))
  :hints (("Goal"
           :in-theory (enable fn-article-header-rev-add-line))))

(defthm fn-article-nonempty-true-list-is-consp
  (implies (and (true-listp xs) xs)
           (consp xs)))

(defthm fn-article-natp-one-less
  (implies (and (natp n) (not (zp n)))
           (natp (1- n))))

(verify-guards fn-article-wspp)
(verify-guards fn-article-vcharp)
(verify-guards fn-article-ftextp)
(verify-guards fn-article-header-bytep)
(verify-guards fn-article-header-bytes-p)
(verify-guards fn-article-has-vcharp)
(verify-guards fn-article-ascii-downcase-byte)
(verify-guards fn-article-ascii-downcase)
(verify-guards fn-article-ftext-listp)
(verify-guards fn-article-namep)
(verify-guards fn-article-lower-namep)
(verify-guards fn-article-header)
(verify-guards fn-article-body)
(verify-guards fn-article-fields)
(verify-guards fn-article-make)
(verify-guards fn-article-source)
(verify-guards fn-article-field-raw-lines)
(verify-guards fn-article-field-name)
(verify-guards fn-article-field-unfolded-value)
(verify-guards fn-article-make-field)
(verify-guards fn-article-fieldp)
(verify-guards fn-article-field-listp)
(verify-guards fn-article-syntax-p)
(verify-guards fn-article-result-okp)
(verify-guards fn-article-result-article)
(verify-guards fn-article-error)
(verify-guards fn-article-ok)
(verify-guards fn-article-next-line-aux)
(verify-guards fn-article-next-line)
(verify-guards fn-article-line-okp)
(verify-guards fn-article-line-value)
(verify-guards fn-article-line-rest)
(verify-guards fn-article-split-colon-aux)
(verify-guards fn-article-new-field)
(verify-guards fn-article-fold-linep)
(verify-guards fn-article-add-fold)
(verify-guards fn-article-header-rev-add-line)
(verify-guards fn-article-finish-fields)
(verify-guards fn-article-body-crlfp)
(verify-guards fn-article-parse-lines
  :hints (("Goal"
           :in-theory
           (disable fn-article-next-line fn-article-next-line-aux
                    fn-article-new-field fn-article-split-colon-aux
                    fn-article-line-value fn-article-line-rest
                    fn-article-add-fold fn-article-header-rev-add-line
                    fn-article-finish-fields fn-article-body-crlfp))))
(verify-guards fn-article-parse)
(verify-guards fn-article-field-name-equalp)
(verify-guards fn-article-get-headers-aux)
(verify-guards fn-article-get-headers)
(verify-guards fn-article-get-header)

; General recomposition property of the article-view representation.  This is
; deliberately not the stronger parser-input preservation theorem, which needs
; a separate induction over `fn-article-parse-lines`.
(defthm fn-article-source-recomposes
  (equal (fn-article-source (fn-article-make header body fields))
         (append header '(13 10) body)))

; -----------------------------------------------------------------------------
; Export theory.
;
; The three recognizer-to-`true-listp` rules above and
; `fn-article-nonempty-true-list-is-consp` are guard vocabulary: as enabled
; rewrite rules they backchain from any `(consp X)` or `(true-listp X)` goal
; into a recursive recognizer on a bare variable.  Measured in
; `books/nntp-invariants.lisp`, 921k of 921k frames of
; `fn-nntp-article-response-keeps-projection` sat under that fan-out, and two
; books withdrew the four by name to certify at all.  They are withdrawn here
; instead, under one name, and the type-reasoning role they served for an
; includer is exported back as `:forward-chaining` shape facts
; (`docs/proof-style.md` section 1: the fact lands in the context when the
; recognizer is mentioned, and no `consp`/`true-listp` rewrite rule leaves the
; book).

(defthm fn-article-header-bytes-p-forward-shape
  (implies (fn-article-header-bytes-p bytes)
           (true-listp bytes))
  :rule-classes :forward-chaining
  :hints (("Goal" :by fn-article-header-bytes-true-listp)))

(defthm fn-article-field-listp-forward-shape
  (implies (fn-article-field-listp fields)
           (true-listp fields))
  :rule-classes :forward-chaining
  :hints (("Goal" :by fn-article-field-list-true-listp)))

(defthm fn-article-octet-listp-forward-shape
  (implies (fn-cbor-octet-listp octets)
           (true-listp octets))
  :rule-classes :forward-chaining
  :hints (("Goal" :by fn-article-octet-list-true-listp)))

(deftheory fn-article-guard-backchaining
  '(fn-article-header-bytes-true-listp
    fn-article-field-list-true-listp
    fn-article-octet-list-true-listp
    fn-article-nonempty-true-list-is-consp))

(in-theory (disable fn-article-guard-backchaining))
