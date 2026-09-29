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
; The header limits (D27; lane header-limits-profile, PRF-230, STO-030).
; They bound the data one article's header holds, so they are the
; operator's: store profile fields 15 `max-header-fields', 16
; `max-header-lines' and 17 `max-header-octets' (books/byte-store-frame),
; handed to `fn-article-parse-under' as LIMITS = (FIELDS LINES OCTETS) by
; every admission (the injection configuration, `fn-inj-config-header-
; limits').  The three constants below are the defaults: every profile's
; value unless the operator writes another, so a store under the default
; profile admits exactly what it admitted before.
; The parse's work stays bounded per header line whatever the limits: each
; step reads one line (at most 998 octets, the RFC's MUST), and the field
; count is carried, never recounted.
(defconst *fn-article-max-header-octets* 16384)
(defconst *fn-article-max-header-lines* 256)
(defconst *fn-article-max-fields* 64)
(defconst *fn-article-default-limits*
  (list *fn-article-max-fields* *fn-article-max-header-lines*
        *fn-article-max-header-octets*))

; LIMITS accessors: total, a missing or non-natural entry reads as 0 (which
; refuses the first line, never admits more).
(defun fn-article-limit-fields (limits)
  (declare (xargs :guard t))
  (nfix (if (consp limits) (car limits) 0)))
(defun fn-article-limit-lines (limits)
  (declare (xargs :guard t))
  (nfix (if (and (consp limits) (consp (cdr limits))) (cadr limits) 0)))
(defun fn-article-limit-octets (limits)
  (declare (xargs :guard t))
  (nfix (if (and (consp limits) (consp (cdr limits)) (consp (cddr limits)))
            (caddr limits)
          0)))
(defun fn-article-limits (fields lines octets)
  (declare (xargs :guard t))
  (list (nfix fields) (nfix lines) (nfix octets)))
(defun fn-article-limitsp (limits)
  (declare (xargs :guard t))
  (and (true-listp limits) (equal (len limits) 3)
       (posp (car limits)) (posp (cadr limits)) (posp (caddr limits))))
; LIMITS is at most WIDER in every entry.
(defun fn-article-limits-within (limits wider)
  (declare (xargs :guard t))
  (and (<= (fn-article-limit-fields limits) (fn-article-limit-fields wider))
       (<= (fn-article-limit-lines limits) (fn-article-limit-lines wider))
       (<= (fn-article-limit-octets limits) (fn-article-limit-octets wider))))
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
        ;; RFC 5322 section 2.2.3: a field body may begin on a continuation
        ;; line (`References:' CRLF ` <id>'), so an EMPTY first-line value is
        ;; a field still open; `fn-article-field-closedp' refuses it if no
        ;; fold line follows (RFC 5536 section 2.2: no empty header field).
        (if (and (fn-article-namep name)
                 (or (null value)
                     (and (consp value)
                          (fn-article-wspp (car value))
                          (fn-article-header-bytes-p value)
                          (fn-article-has-vcharp value))))
            (list :ok (fn-article-make-field
                       (list line) (fn-article-ascii-downcase name) value))
          (fn-article-error :invalid-header))))))

; A field may be closed (by the next field or the header's end) once its
; unfolded value is non-empty: a first line's value either has a visible
; character or is empty, and every fold line has one (fn-article-fold-linep),
; so a non-empty value has one.  One test, no walk.
(defun fn-article-field-closedp (current)
  (declare (xargs :guard (or (null current) (fn-article-fieldp current))))
  (or (null current)
      (consp (fn-article-field-unfolded-value current))))

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

; Parse until the first blank line.  `lines-left` is the header-line limit
; plus one (the separator's step) and the recursion's measure, so
; termination and hostile-input work do not depend on an untrusted header
; count.  NFIELDS is the number of completed fields (the length of
; FIELDS-REV), carried so that starting a field is constant work.  Each limit
; is refused by its own name.
(defun fn-article-parse-lines (octets limits lines-left header-bytes nfields
                                      fields-rev current header-rev)
  (declare (xargs :measure (nfix lines-left)
                  :guard (and (true-listp octets)
                              (natp lines-left)
                              (natp header-bytes)
                              (natp nfields)
                              (true-listp fields-rev)
                              (or (null current)
                                  (fn-article-fieldp current))
                              (true-listp header-rev))
                  :verify-guards nil))
  (if (zp lines-left)
      (fn-article-error :header-lines-limit)
    (let ((next (fn-article-next-line octets)))
      (if (not (fn-article-line-okp next))
          next
        (let ((line (fn-article-line-value next))
              (rest (fn-article-line-rest next)))
          (if (null line)
              (if (or (not (fn-article-body-crlfp rest))
                      (not (fn-article-field-closedp current)))
                  (fn-article-error :invalid-header)
                (fn-article-ok
                 (fn-article-make
                  (reverse header-rev) rest
                  (fn-article-finish-fields fields-rev current))))
            (if (< (fn-article-limit-octets limits)
                   (+ header-bytes (len line) 2))
                (fn-article-error :header-octets-limit)
              (if (fn-article-wspp (car line))
                  (if (not current)
                      (fn-article-error :invalid-header)
                    (if (not (fn-article-fold-linep line))
                        (fn-article-error :invalid-header)
                      (fn-article-parse-lines
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       nfields fields-rev (fn-article-add-fold current line)
                       (fn-article-header-rev-add-line header-rev line))))
                (let ((field-result (fn-article-new-field line)))
                  (if (not (fn-article-line-okp field-result))
                      field-result
                   (if (not (fn-article-field-closedp current))
                       (fn-article-error :invalid-header)
                    (if (<= (fn-article-limit-fields limits)
                            (+ (if current 1 0) (nfix nfields)))
                        (fn-article-error :header-fields-limit)
                      (fn-article-parse-lines
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       (if current (+ 1 (nfix nfields)) nfields)
                       (if current (cons current fields-rev) fields-rev)
                       (fn-article-line-value field-result)
                       (fn-article-header-rev-add-line header-rev line))))))))))))))

; The field under construction, carried reversed: (raw-lines-rev lower-name
; unfolded-value-rev).  A continuation line then costs its own length, not the
; field's accumulated length (PKT-552/770).
(defun fn-article-open-fieldp (cur)
  (declare (xargs :guard t))
  (and (true-listp cur)
       (equal (len cur) 3)
       (true-listp (car cur))
       (true-listp (car (cdr (cdr cur))))))

(defun fn-article-close-field (cur)
  (declare (xargs :guard (fn-article-open-fieldp cur)))
  (fn-article-make-field (reverse (car cur)) (car (cdr cur))
                         (reverse (car (cdr (cdr cur))))))

(defun fn-article-open-field (field)
  (declare (xargs :guard (fn-article-fieldp field)))
  (list (reverse (fn-article-field-raw-lines field))
        (fn-article-field-name field)
        (reverse (fn-article-field-unfolded-value field))))

(defun fn-article-add-fold-open (cur line)
  (declare (xargs :guard (and (fn-article-open-fieldp cur)
                              (true-listp line))))
  (list (cons line (car cur))
        (car (cdr cur))
        (revappend line (car (cdr (cdr cur))))))

; fn-article-field-closedp on the carried field: the reversed value is a cons
; exactly when the value is.  One test, no walk.
(defun fn-article-open-field-closedp (cur)
  (declare (xargs :guard (or (null cur) (fn-article-open-fieldp cur))))
  (or (null cur)
      (consp (car (cdr (cdr cur))))))

(defun fn-article-parse-lines-acc (octets limits lines-left header-bytes nfields
                                          fields-rev cur header-rev)
  (declare (xargs :measure (nfix lines-left)
                  :guard (and (true-listp octets)
                              (natp lines-left)
                              (natp header-bytes)
                              (natp nfields)
                              (true-listp fields-rev)
                              (or (null cur)
                                  (fn-article-open-fieldp cur))
                              (true-listp header-rev))
                  :verify-guards nil))
  (if (zp lines-left)
      (fn-article-error :header-lines-limit)
    (let ((next (fn-article-next-line octets)))
      (if (not (fn-article-line-okp next))
          next
        (let ((line (fn-article-line-value next))
              (rest (fn-article-line-rest next)))
          (if (null line)
              (if (or (not (fn-article-body-crlfp rest))
                      (not (fn-article-open-field-closedp cur)))
                  (fn-article-error :invalid-header)
                (fn-article-ok
                 (fn-article-make
                  (reverse header-rev) rest
                  (fn-article-finish-fields
                   fields-rev (and cur (fn-article-close-field cur))))))
            (if (< (fn-article-limit-octets limits)
                   (+ header-bytes (len line) 2))
                (fn-article-error :header-octets-limit)
              (if (fn-article-wspp (car line))
                  (if (not cur)
                      (fn-article-error :invalid-header)
                    (if (not (fn-article-fold-linep line))
                        (fn-article-error :invalid-header)
                      (fn-article-parse-lines-acc
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       nfields fields-rev (fn-article-add-fold-open cur line)
                       (fn-article-header-rev-add-line header-rev line))))
                (let ((field-result (fn-article-new-field line)))
                  (if (not (fn-article-line-okp field-result))
                      field-result
                   (if (not (fn-article-open-field-closedp cur))
                       (fn-article-error :invalid-header)
                    (if (<= (fn-article-limit-fields limits)
                            (+ (if cur 1 0) (nfix nfields)))
                        (fn-article-error :header-fields-limit)
                      (fn-article-parse-lines-acc
                       rest limits (1- lines-left) (+ header-bytes (len line) 2)
                       (if cur (+ 1 (nfix nfields)) nfields)
                       (if cur (cons (fn-article-close-field cur) fields-rev)
                         fields-rev)
                       (fn-article-open-field (fn-article-line-value field-result))
                       (fn-article-header-rev-add-line header-rev line))))))))))))))

; The admission parser: OCTETS under the header LIMITS of the profile the
; store runs under.  The article-octet preflight is the codec ceiling; the
; operator's article bound is applied before this by every admission.
(defun fn-article-parse-under (octets limits)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-at-mostp octets *fn-article-max-octets*))
      (fn-article-error :limit)
    (if (not (fn-cbor-octet-listp octets))
      (fn-article-error :invalid-header)
      (mbe :logic (fn-article-parse-lines octets limits
                                          (1+ (fn-article-limit-lines limits))
                                          0 0 nil nil nil)
           :exec (fn-article-parse-lines-acc octets limits
                                             (1+ (fn-article-limit-lines limits))
                                             0 0 nil nil nil)))))

; The parser every reader of a stored or received article uses: the widest
; limits any profile can write (each the article codec's ceiling, the
; relation of books/byte-store-frame's fields 15 to 17), so it never refuses
; an article some profile admitted: an article parses here exactly as under
; the limits it was admitted by (`fn-article-parse-under-raised-limits-
; agree', books/article-header-limits).  Admission applies the profile's
; limits (books/injection `fn-inj-decide').  Its work is bounded by the
; input: every step consumes one line of at most 998 octets and its CRLF.
(defconst *fn-article-ceiling-limits*
  (list *fn-article-max-octets* *fn-article-max-octets* *fn-article-max-octets*))

(defun fn-article-parse (octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-article-parse-under octets *fn-article-ceiling-limits*))

; A limit refusal, by name.
(defun fn-article-limit-reasonp (code)
  (declare (xargs :guard t))
  (member-eq code '(:header-fields-limit :header-lines-limit
                    :header-octets-limit)))

; -----------------------------------------------------------------------------
; Lookup helpers.  Names are lowercased ftext octet lists; callers retain the
; raw field lines/source for all semantic interpretation and future policy.

(defun fn-article-field-name-equalp (field name)
  (declare (xargs :guard (true-listp field)))
  (equal (fn-article-field-name field) (fn-article-ascii-downcase name)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-article-get-headers-aux-loop (fields name acc)
  (declare (xargs :guard (and (fn-article-field-listp fields) (true-listp acc)) :verify-guards nil))
  (if (consp fields)
      (let ((field (car fields)))
        (if (fn-article-field-name-equalp field name)
            (fn-article-get-headers-aux-loop (cdr fields) name (cons field acc))
          (fn-article-get-headers-aux-loop (cdr fields) name acc)))
    (revappend acc nil)))

(defun fn-article-get-headers-aux (fields name)
  (declare (xargs :verify-guards nil :guard (fn-article-field-listp fields)))
  (mbe :logic
       (if (consp fields)
           (let ((field (car fields)))
             (if (fn-article-field-name-equalp field name)
                 (cons field (fn-article-get-headers-aux (cdr fields) name))
               (fn-article-get-headers-aux (cdr fields) name)))
         nil)
       :exec (fn-article-get-headers-aux-loop fields name nil)))

(local
 (defthm fn-article-get-headers-aux-loop-is-revappend
   (equal (fn-article-get-headers-aux-loop fields name acc)
          (revappend acc (fn-article-get-headers-aux fields name)))
   :hints (("Goal" :induct (fn-article-get-headers-aux-loop fields name acc)
                   :in-theory (union-theories '(fn-article-get-headers-aux-loop fn-article-get-headers-aux revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-article-get-headers-aux-loop)

(verify-guards fn-article-get-headers-aux
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-article-get-headers-aux)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-article-get-headers-aux-loop-is-revappend (acc nil))))))


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
(verify-guards fn-article-field-closedp)
(verify-guards fn-article-open-field-closedp)
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
                    fn-article-finish-fields fn-article-body-crlfp
                    fn-article-field-closedp))))
; The executed parse is the accumulator loop; the logical one is unchanged.
(local
 (defthm fn-article-three-list-recomposes
   (implies (and (true-listp x) (equal (len x) 3))
            (equal (list (car x) (cadr x) (caddr x)) x))
   :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x))
                            (len (cdddr x)) (true-listp (cdddr x)))))))

(defthm fn-article-close-add-fold-open
  (implies (and (fn-article-open-fieldp cur) (true-listp line))
           (equal (fn-article-close-field (fn-article-add-fold-open cur line))
                  (fn-article-add-fold (fn-article-close-field cur) line)))
  :hints (("Goal" :in-theory (enable fn-article-add-fold))))

(defthm fn-article-close-open-field
  (implies (fn-article-fieldp field)
           (equal (fn-article-close-field (fn-article-open-field field))
                  field))
  :hints (("Goal" :in-theory (enable fn-article-fieldp))))

(defthm fn-article-add-fold-open-fieldp
  (implies (and (fn-article-open-fieldp cur) (true-listp line))
           (fn-article-open-fieldp (fn-article-add-fold-open cur line))))

(defthm fn-article-open-field-open-fieldp
  (implies (fn-article-fieldp field)
           (fn-article-open-fieldp (fn-article-open-field field)))
  :hints (("Goal" :in-theory (enable fn-article-fieldp))))

(defthm fn-article-close-field-nonnil
  (fn-article-close-field cur)
  :rule-classes :type-prescription)

(defthm fn-article-field-closedp-of-close-field
  (implies (fn-article-open-fieldp cur)
           (equal (fn-article-field-closedp (fn-article-close-field cur))
                  (consp (car (cdr (cdr cur))))))
  :hints (("Goal" :in-theory (enable fn-article-field-closedp))))

; PKT-552/770: the host-called parse (fn-article-parse-under, through mbe)
; runs this loop, in which a continuation line costs its own length; it
; returns exactly what the reference loop returns on every input.
(defthm fn-article-parse-lines-acc-is-parse-lines
  (implies (or (null cur) (fn-article-open-fieldp cur))
           (equal (fn-article-parse-lines-acc octets limits lines-left
                                              header-bytes nfields
                                              fields-rev cur header-rev)
                  (fn-article-parse-lines octets limits lines-left
                                          header-bytes nfields fields-rev
                                          (and cur (fn-article-close-field cur))
                                          header-rev)))
  :hints (("Goal" :induct (fn-article-parse-lines-acc octets limits lines-left
                                                       header-bytes nfields
                                                       fields-rev cur header-rev)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (disable fn-article-close-field fn-article-add-fold-open
                               fn-article-open-field fn-article-open-fieldp
                               fn-article-add-fold fn-article-new-field
                               fn-article-next-line fn-article-header-rev-add-line
                               fn-article-finish-fields fn-article-body-crlfp
                               fn-article-line-okp fn-article-line-value
                               fn-article-line-rest fn-article-fold-linep
                               fn-article-make fn-article-ok fn-article-error
                               fn-article-wspp fn-article-limit-octets
                               fn-article-limit-fields
                               fn-article-field-closedp))))

(verify-guards fn-article-parse-lines-acc
  :hints (("Goal"
           :in-theory
           (disable fn-article-next-line fn-article-next-line-aux
                    fn-article-new-field fn-article-split-colon-aux
                    fn-article-line-value fn-article-line-rest
                    fn-article-add-fold-open fn-article-close-field
                    fn-article-open-field fn-article-open-fieldp
                    fn-article-open-field-closedp
                    fn-article-header-rev-add-line
                    fn-article-finish-fields fn-article-body-crlfp))))
(verify-guards fn-article-parse-under)
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

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-article-header-bytes-p)
                    (:definition fn-article-header-rev-add-line)
                    (:definition fn-article-new-field)
                    (:definition fn-article-next-line-aux)
                    (:definition fn-article-parse-lines)
                    (:rewrite fn-article-header-rev-add-line-recomposes)))
