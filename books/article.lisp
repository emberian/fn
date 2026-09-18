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

(defconst *fn-article-max-octets* 32768)
(defconst *fn-article-max-header-octets* 8192)
(defconst *fn-article-max-line-octets* 998)
(defconst *fn-article-max-header-lines* 128)
(defconst *fn-article-max-fields* 64)

; -----------------------------------------------------------------------------
; Octet grammar helpers

(defun fn-article-wspp (byte)
  (or (equal byte 32) (equal byte 9)))

(defun fn-article-vcharp (byte)
  (and (integerp byte) (<= 33 byte) (<= byte 126)))

; RFC 5322 ftext, used by RFC 5536 header field names.
(defun fn-article-ftextp (byte)
  (or (and (integerp byte) (<= 33 byte) (<= byte 57))
      (and (integerp byte) (<= 59 byte) (<= byte 126))))

(defun fn-article-header-bytep (byte)
  (or (fn-article-wspp byte) (fn-article-vcharp byte)))

(defun fn-article-header-bytes-p (bytes)
  (if (consp bytes)
      (and (fn-article-header-bytep (car bytes))
           (fn-article-header-bytes-p (cdr bytes)))
    (null bytes)))

(defun fn-article-has-vcharp (bytes)
  (if (consp bytes)
      (or (fn-article-vcharp (car bytes))
          (fn-article-has-vcharp (cdr bytes)))
    nil))

(defun fn-article-ascii-downcase-byte (byte)
  (if (and (integerp byte) (<= 65 byte) (<= byte 90))
      (+ byte 32)
    byte))

(defun fn-article-ascii-downcase (bytes)
  (if (consp bytes)
      (cons (fn-article-ascii-downcase-byte (car bytes))
            (fn-article-ascii-downcase (cdr bytes)))
    nil))

(defun fn-article-ftext-listp (bytes)
  (if (consp bytes)
      (and (fn-article-ftextp (car bytes))
           (fn-article-ftext-listp (cdr bytes)))
    (null bytes)))

(defun fn-article-namep (name)
  (and (consp name) (fn-article-ftext-listp name)))

(defun fn-article-lower-namep (name)
  (and (fn-article-namep name)
       (equal name (fn-article-ascii-downcase name))))

; -----------------------------------------------------------------------------
; Parsed article and field views

; Article: (raw-header body fields).  `fn-article-source` reconstructs the
; exact received source as header ++ CRLF ++ body; raw field lines preserve
; field order and folding independently of the parsed lookup view.
(defun fn-article-header (article) (car article))
(defun fn-article-body (article) (car (cdr article)))
(defun fn-article-fields (article) (car (cdr (cdr article))))

(defun fn-article-make (header body fields)
  (list header body fields))

(defun fn-article-source (article)
  (append (fn-article-header article) '(13 10) (fn-article-body article)))

; Field: (raw-lines lower-name unfolded-value).  Raw lines exclude their CRLF;
; unfolded-value removes only folding CRLF and retains continuation WSP.
(defun fn-article-field-raw-lines (field) (car field))
(defun fn-article-field-name (field) (car (cdr field)))
(defun fn-article-field-unfolded-value (field) (car (cdr (cdr field))))

(defun fn-article-make-field (raw-lines lower-name unfolded-value)
  (list raw-lines lower-name unfolded-value))

(defun fn-article-fieldp (field)
  (and (true-listp field)
       (equal (len field) 3)
       (true-listp (fn-article-field-raw-lines field))
       (fn-article-lower-namep (fn-article-field-name field))
       (fn-article-header-bytes-p (fn-article-field-unfolded-value field))))

(defun fn-article-field-listp (fields)
  (if (consp fields)
      (and (fn-article-fieldp (car fields))
           (fn-article-field-listp (cdr fields)))
    (null fields)))

(defun fn-article-syntax-p (article)
  (and (true-listp article)
       (equal (len article) 3)
       (fn-cbor-octet-listp (fn-article-header article))
       (fn-cbor-octet-listp (fn-article-body article))
       (fn-article-field-listp (fn-article-fields article))))

(defun fn-article-result-okp (result)
  (and (consp result) (equal (car result) :ok)))

(defun fn-article-result-article (result)
  (car (cdr result)))

(defun fn-article-error (code) (list :error code))
(defun fn-article-ok (article) (list :ok article))

; -----------------------------------------------------------------------------
; Line and field syntax

; Result: (:ok line remaining) | (:error code).  A line is its octets without
; CRLF.  The fixed `left` fuel bounds both line allocation and scanning.
(defun fn-article-next-line-aux (octets line-rev left)
  (declare (xargs :measure (acl2-count octets)))
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
  (fn-article-next-line-aux octets nil *fn-article-max-line-octets*))

(defun fn-article-line-okp (result)
  (and (consp result) (equal (car result) :ok)))

(defun fn-article-line-value (result) (car (cdr result)))
(defun fn-article-line-rest (result) (car (cdr (cdr result))))

; Find the first colon.  Header values may contain later colons unchanged.
(defun fn-article-split-colon-aux (line name-rev)
  (if (consp line)
      (if (equal (car line) 58)
          (list :ok (reverse name-rev) (cdr line))
        (fn-article-split-colon-aux (cdr line) (cons (car line) name-rev)))
    (fn-article-error :invalid-header)))

(defun fn-article-new-field (line)
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
  (and (consp line)
       (fn-article-wspp (car line))
       (fn-article-header-bytes-p line)
       (fn-article-has-vcharp line)))

(defun fn-article-add-fold (field line)
  (fn-article-make-field
   (append (fn-article-field-raw-lines field) (list line))
   (fn-article-field-name field)
   (append (fn-article-field-unfolded-value field) line)))

(defun fn-article-header-rev-add-line (header-rev line)
  (append '(10 13) (reverse line) header-rev))

; Each accepted physical header line contributes exactly itself and its CRLF to
; the forward header view.  This is the induction step behind source splitting.
(defthm fn-article-header-rev-add-line-recomposes
  (implies (and (true-listp header-rev) (true-listp line))
           (equal (rev (fn-article-header-rev-add-line header-rev line))
                  (append (rev header-rev) line '(13 10)))))

(defun fn-article-finish-fields (fields-rev current)
  (if current
      (reverse (cons current fields-rev))
    (reverse fields-rev)))

; Body framing is intentionally the only body syntax checked here: binary
; non-CR/LF octets are opaque, while CR and LF must occur only as CRLF pairs.
(defun fn-article-body-crlfp (body)
  (declare (xargs :measure (acl2-count body)))
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
  (declare (xargs :measure (nfix lines-left)))
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
  (equal (fn-article-field-name field) (fn-article-ascii-downcase name)))

(defun fn-article-get-headers-aux (fields name)
  (if (consp fields)
      (let ((field (car fields)))
        (if (fn-article-field-name-equalp field name)
            (cons field (fn-article-get-headers-aux (cdr fields) name))
          (fn-article-get-headers-aux (cdr fields) name)))
    nil))

(defun fn-article-get-headers (article name)
  (fn-article-get-headers-aux (fn-article-fields article) name))

(defun fn-article-get-header (article name)
  (let ((headers (fn-article-get-headers article name)))
    (if (consp headers) (car headers) nil)))

; General recomposition property of the article-view representation.  This is
; deliberately not the stronger parser-input preservation theorem, which needs
; a separate induction over `fn-article-parse-lines`.
(defthm fn-article-source-recomposes
  (equal (fn-article-source (fn-article-make header body fields))
         (append header '(13 10) body)))
