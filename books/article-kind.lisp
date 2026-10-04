; fn: the application article kind `opaque', version 1 (D50; M6 of
; MINI-FN-660-REQUIREMENTS-20261004, planning/design/zmq-surface-2026-10-04.md).
;
; An application that keeps its own payload format (Mini's block bundles,
; receipts, deal messages; any zmq-pattern frame) posts it to fn as ONE kind
; of article: a fixed header sequence, a version word, and the payload as
; canonical padded base64 (RFC 4648 section 4) in CRLF lines of 76.  fn
; never interprets the payload; it owns the grammar of the AUTHORED SOURCE
; around it, so both sides render and read it from one definition.
;
; "Kind", not "profile": in fn a profile is the D27 store profile of
; operator bounds.  This book adds no profile field and no bound: the payload
; has no ceiling here (D27); the operator's article bound applies at
; admission (fn-inj-decide's max-octets), as for every article.
;
; The subject is the authored source, the bytes D01 signs.  A served article
; is Xref, Path, Injection-Info and the FN-Authorship carrier lines, then the
; authored source; the reader's extraction is fn-hc-authored-source
; (books/hybrid-carrier.lisp), and this book's recognizer reads what that
; returns.
;
; THE GRAMMAR (version 1), octet for octet:
;
;   source  = row-1 ... row-8 CRLF body
;   row-k   = NAME-k ":" SP VALUE-k CRLF          ; one physical line, no fold
;   body    = *(76b64 CRLF) [1*76b64 CRLF]        ; frame of the base64 text
;   VALUE   = VCHAR *(SP / VCHAR), and NAME ": " VALUE is at most 998 octets
;
;   k  NAME                       VALUE
;   1  From                       an RFC 5322 mailbox-list fn's injection
;                                 accepts (fn-mbx-mailbox-listp of SP VALUE)
;   2  Date                       VALUE (fn has no date-time parser; the
;                                 author's Date is kept, never checked)
;   3  Newsgroups                 a newsgroup-list (fn-af-newsgroup-list-parse)
;   4  Subject                    VALUE
;   5  Message-ID                 a msg-id (fn-af-message-idp), no WSP
;   6  FN-Kind                    exactly "opaque 1": the version word
;   7  Content-Type               VALUE: the application's media type; fn
;                                 does not read it
;   8  Content-Transfer-Encoding  exactly "base64"
;
; The rows are the constant *fn-ak-v1-rows*.  The CODEC is the wire-grammar
; interpreter (books/wire-grammar.lisp, lane mini-contract: fn-wg-encode and
; fn-wg-decode at *fn-ak-grammar*, with the generic round trips
; fn-wg-decode-of-encode and fn-wg-encode-of-decode); there is no second
; encoder or decoder of this kind.  *fn-ak-grammar* is computed from the rows,
; so the exported grammar and the rows below cannot drift.
;
; What this book adds to the grammar:
;   fn-ak-row-valuep / fn-ak-rows-valuesp  the kind's values: a grammar value
;       whose header values open with a VCHAR and pass fn's own injection
;       checks (the mailbox-list, the newsgroup-list, the msg-id), so that
;       every value of the kind is accepted, unconditionally on its content;
;   fn-ak-layout  the octets spelled out (rows, blank line, the 76-column
;       frame of fn-ot-b64-encode), the proof-side meaning of the encoding.
; The acceptance keystones (fn-article-parse accepts every layout with its
; eight fields; fn-inj-decide answers :injected with the source as a
; suffix) are in books/article-kind-acceptance.lisp, which includes the
; injecting agent; this book stays light.

(in-package "ACL2")
(include-book "mailbox")
(include-book "octet-text")

; -----------------------------------------------------------------------------
; The table.  A row is (NAME KIND ARG STEM): NAME the field name as written,
; KIND one of :from :text :groups :msgid :version :fixed, ARG the exact value
; of a :version or :fixed row, STEM the octets that open any version of a
; :version row (its refusal names :kind-version when they open the value).

(defconst *fn-ak-version* 1)

(defconst *fn-ak-v1-rows*
  '(((70 114 111 109) :from)                                  ; From
    ((68 97 116 101) :text)                                   ; Date
    ((78 101 119 115 103 114 111 117 112 115) :groups)        ; Newsgroups
    ((83 117 98 106 101 99 116) :text)                        ; Subject
    ((77 101 115 115 97 103 101 45 73 68) :msgid)             ; Message-ID
    ((70 78 45 75 105 110 100) :version                       ; FN-Kind
     (111 112 97 113 117 101 32 49)                           ;   "opaque 1"
     (111 112 97 113 117 101 32))                             ;   "opaque "
    ((67 111 110 116 101 110 116 45 84 121 112 101) :text)    ; Content-Type
    ((67 111 110 116 101 110 116 45 84 114 97 110 115 102 101 114 45 69 110
      99 111 100 105 110 103) :fixed                          ; Content-Transfer-Encoding
     (98 97 115 101 54 52))))                                 ;   "base64"

; RFC 5322 section 2.1.1: a line is at most 998 octets without its CRLF.
(defconst *fn-ak-max-line-octets* 998)
; The body's line width (RFC 2045 section 6.8's 76).
(defconst *fn-ak-body-line-octets* 76)

(defun fn-ak-row-name (row) (declare (xargs :guard t)) (if (consp row) (car row) nil))
(defun fn-ak-row-kind (row)
  (declare (xargs :guard t))
  (if (and (consp row) (consp (cdr row))) (cadr row) nil))
(defun fn-ak-row-arg (row)
  (declare (xargs :guard t))
  (if (and (consp row) (consp (cdr row)) (consp (cddr row))) (caddr row) nil))
(defun fn-ak-row-stem (row)
  (declare (xargs :guard t))
  (if (and (consp row) (consp (cdr row)) (consp (cddr row)) (consp (cdddr row)))
      (cadddr row)
    nil))

; NAME ": "
(defun fn-ak-row-prefix (row)
  (declare (xargs :guard t))
  (append (true-list-fix (fn-ak-row-name row)) '(58 32)))

; The longest VALUE the row's line holds.
(defun fn-ak-row-fuel (row)
  (declare (xargs :guard t))
  (nfix (- *fn-ak-max-line-octets* (len (fn-ak-row-prefix row)))))

; -----------------------------------------------------------------------------
; Values

(defun fn-ak-vcharp (x)
  (declare (xargs :guard t))
  (and (integerp x) (<= 33 x) (<= x 126)))

(defun fn-ak-sp-vchar-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (or (equal (car xs) 32) (fn-ak-vcharp (car xs)))
           (fn-ak-sp-vchar-listp (cdr xs)))
    (null xs)))

(defun fn-ak-text-valuep (v)
  (declare (xargs :guard t))
  (and (consp v) (fn-ak-vcharp (car v)) (fn-ak-sp-vchar-listp v)))

(defthm fn-ak-sp-vchar-listp-is-true-listp
  (implies (fn-ak-sp-vchar-listp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defthm fn-ak-sp-vchar-listp-is-octets
  (implies (fn-ak-sp-vchar-listp xs) (fn-cbor-octet-listp xs))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp))))

(defun fn-ak-row-valuep (row v)
  (declare (xargs :guard t))
  (and (fn-ak-text-valuep v)
       (<= (len v) (fn-ak-row-fuel row))
       (case (fn-ak-row-kind row)
         (:from (fn-mbx-mailbox-listp (cons 32 v)))
         (:groups (let ((g (fn-af-newsgroup-list-parse v)))
                    (and (equal (car g) :ok) (consp (cadr g)))))
         (:msgid (and (fn-af-message-idp v) (equal (fn-af-trim-wsp v) v)))
         ((:version :fixed) (equal v (fn-ak-row-arg row)))
         (otherwise t))))

(defun fn-ak-rows-valuesp (rows vals)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (consp vals)
           (fn-ak-row-valuep (car rows) (car vals))
           (fn-ak-rows-valuesp (cdr rows) (cdr vals)))
    (null vals)))

; -----------------------------------------------------------------------------
; The header rows

(defun fn-ak-no-crlfp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (not (equal (car xs) 13)) (not (equal (car xs) 10))
           (fn-ak-no-crlfp (cdr xs)))
    t))


(defun fn-ak-render-rows (rows vals)
  (declare (xargs :guard t))
  (if (consp rows)
      (append (fn-ak-row-prefix (car rows))
              (true-list-fix (if (consp vals) (car vals) nil))
              '(13 10)
              (fn-ak-render-rows (cdr rows) (if (consp vals) (cdr vals) nil)))
    nil))

; -----------------------------------------------------------------------------
; The body: the base64 text in lines of 76, the last 1 to 76, each CRLF.

(defun fn-ak-take (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom xs)) nil
    (cons (car xs) (fn-ak-take (1- n) (cdr xs)))))

(defun fn-ak-drop (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom xs)) xs
    (fn-ak-drop (1- n) (cdr xs))))

(defthm fn-ak-drop-is-shorter
  (implies (and (posp n) (consp xs))
           (< (len (fn-ak-drop n xs)) (len xs)))
  :rule-classes :linear)

(defun fn-ak-frame (text)
  (declare (xargs :guard t :measure (len text)))
  (if (consp text)
      (append (fn-ak-take *fn-ak-body-line-octets* text) '(13 10)
              (fn-ak-frame (fn-ak-drop *fn-ak-body-line-octets* text)))
    nil))

; -----------------------------------------------------------------------------
; The kind

; The octets of the kind at VALS (the eight row values in table order) and
; PAYLOAD; nil when VALS is not a value of the kind or PAYLOAD is not octets.
(defun fn-ak-layout (vals payload)
  (declare (xargs :guard t))
  (if (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
           (fn-cbor-octet-listp payload))
      (append (fn-ak-render-rows *fn-ak-v1-rows* vals)
              '(13 10)
              (fn-ak-frame (fn-ot-b64-encode payload)))
    nil))

; The six author-chosen values, in table order, with the two fixed rows
; filled in: the form an application calls.
(defun fn-ak-values (from date groups subject msgid media-type)
  (declare (xargs :guard t))
  (list from date groups subject msgid
        '(111 112 97 113 117 101 32 49)
        media-type
        '(98 97 115 101 54 52)))

; -----------------------------------------------------------------------------
; The grammar, in the fn-wire-grammar v1 language (planning/design/
; wire-grammar-2026-10-04.md): a row is (:const NAME ": ") then a header
; (:line 1 FUEL :header); a :version or :fixed row is one (:const) of its
; whole line; then the blank line and the base64 lines.  The base64 node's
; ceiling is the article codec's (*fn-article-max-octets*); the operator's
; article bound applies at admission (D27).

(defun fn-ak-grammar-rows (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((row (car rows)))
        (if (member-eq (fn-ak-row-kind row) '(:version :fixed))
            (cons (cons :const (append (fn-ak-row-prefix row)
                                       (true-list-fix (fn-ak-row-arg row))
                                       '(13 10)))
                  (fn-ak-grammar-rows (cdr rows)))
          (list* (cons :const (fn-ak-row-prefix row))
                 (list :line 1 (fn-ak-row-fuel row) :header)
                 (fn-ak-grammar-rows (cdr rows)))))
    nil))

(defconst *fn-ak-grammar*
  (cons :seq (append (fn-ak-grammar-rows *fn-ak-v1-rows*)
                     (list (list :const 13 10)
                           (list :base64-lines *fn-ak-body-line-octets*
                                 0 *fn-article-max-octets*)))))

; Example values for the exported vectors (fn-wire-grammar `vectors'):
; the empty payload, a short one, exactly two full lines (114 octets), and
; a third short line (115 octets).
(defun fn-ak-octets-of-chars (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs) (cons (char-code (car cs)) (fn-ak-octets-of-chars (cdr cs))) nil))

(defun fn-ak-text (s)
  (declare (xargs :guard (stringp s)))
  (fn-ak-octets-of-chars (coerce s 'list)))

(defun fn-ak-iota (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (append (fn-ak-iota (1- n)) (list (1- n)))))

(defun fn-ak-example-values ()
  (declare (xargs :guard t))
  (fn-ak-values (fn-ak-text "Mini <mini@example.invalid>")
                (fn-ak-text "Sun, 04 Oct 2026 12:00:00 +0000")
                (fn-ak-text "mini.blocks")
                (fn-ak-text "block 1")
                (fn-ak-text "<b1.mini@example.invalid>")
                (fn-ak-text "application/vnd.dregg.fn-native-prefix; version=1")))

(defun fn-ak-example-payloads ()
  (declare (xargs :guard t))
  (list nil (fn-ak-text "hello") (fn-ak-iota 114) (fn-ak-iota 115)))

; The kind's values, as an application states them.
(defun fn-ak-valuesp (from date groups subject msgid media-type)
  (declare (xargs :guard t))
  (fn-ak-rows-valuesp *fn-ak-v1-rows*
                      (fn-ak-values from date groups subject msgid media-type)))
