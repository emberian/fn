; fn NNTP reader session core: octet and command syntax.
;
; Split out of books/nntp.lisp (2026-09-19).  This is the bottom of the
; NNTP cluster: octet predicates, the bounded command-line preflight,
; tokenization, ranges and the decimal field renderers.  It owns no session
; state and reads no archive.

(in-package "ACL2")
(include-book "acceptance")
(include-book "wire")
(include-book "wildmat")
; Guard-total execution helpers preserve ACL2's logical behavior on atoms and
; dotted lists while avoiding raw Common Lisp primitive domain errors.
(defun fn-ng-revappend (xs accumulator)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-ng-revappend (fn-ag-cdr xs)
                       (cons (fn-ag-car xs) accumulator))
    accumulator))

(defthm fn-ng-revappend-is-revappend
  (equal (fn-ng-revappend xs accumulator)
         (revappend xs accumulator)))

(defun fn-ng-reverse (xs)
  (declare (xargs :guard t))
  (if (stringp xs)
      (reverse xs)
    (fn-ng-revappend xs nil)))

(defthm fn-ng-reverse-is-reverse
  (equal (fn-ng-reverse xs) (reverse xs))
  :hints (("Goal" :in-theory (enable reverse))))

(defun fn-ng-char-code (x)
  (declare (xargs :guard t))
  (if (characterp x) (char-code x) 0))

(defthm fn-ng-char-code-is-char-code
  (equal (fn-ng-char-code x) (char-code x))
  :hints (("Goal" :use completion-of-char-code)))

(defun fn-ng-code-char (x)
  (declare (xargs :guard t))
  (if (and (integerp x) (<= 0 x) (< x 256))
      (code-char x)
    (code-char 0)))

(defthm fn-ng-code-char-is-code-char
  (equal (fn-ng-code-char x) (code-char x))
  :hints (("Goal" :use completion-of-code-char)))

(defun fn-ng-less-equal (x y)
  (declare (xargs :guard t))
  (not (fn-ag-less y x)))

(defthm fn-ng-less-equal-is-less-equal
  (equal (fn-ng-less-equal x y) (<= x y)))

(defun fn-ng-len (xs)
  (declare (xargs :guard t))
  (if (consp xs) (1+ (fn-ng-len (fn-ag-cdr xs))) 0))

(defthm fn-ng-len-is-len
  (equal (fn-ng-len xs) (len xs)))
; RFC 3977 section 3.1 counts the terminating CRLF in its 512-octet command
; limit.  A fn-wire command event excludes that pair, hence 510 here.  The
; 497-octet argument limit is retained independently at this core boundary.
(defconst *fn-nntp-max-command-octets* 510)

(defconst *fn-nntp-max-argument-octets* 497)
; RFC 3977 section 3.1 bounds the initial line of a response at 512 octets
; including its CRLF, and section 6 bounds a local article number at
; 2,147,483,647.  The widest initial line this profile generates is the
; LISTGROUP 211 line "211 <count> <low> <high> <group> list follows": four
; status octets, three decimal fields of at most ten digits with their three
; separating spaces, the thirteen octets of " list follows", and CRLF, which is
; 52 octets before the group name.  Bounding a projected group name at 460
; octets therefore keeps every generated initial line at or inside 512.
(defconst *fn-nntp-max-response-octets* 512)

(defconst *fn-nntp-max-initial-line-octets* 510)

(defconst *fn-nntp-max-article-number* 2147483647)

(defconst *fn-nntp-max-group-octets* 460)

(defconst *fn-nntp-max-message-id-octets* 250)

(defconst *fn-nntp-max-decimal-octets* 10)
; -----------------------------------------------------------------------------
; Octet and command syntax helpers

(defun fn-nntp-space-or-tabp (byte)
  (or (equal byte 32) (equal byte 9)))

(defun fn-nntp-command-bytep (byte)
  (or (fn-nntp-space-or-tabp byte)
      (and (integerp byte) (<= 33 byte) (<= byte 255))))

(defun fn-nntp-command-linep (line)
  (if (consp line)
      (and (fn-nntp-command-bytep (car line))
           (fn-nntp-command-linep (cdr line)))
    (null line)))
; U+FEFF is prohibited in command lines by RFC 3977 section 3.1 wherever
; non-ASCII is permitted.  This is a command-boundary check; the generic
; wildmat component correctly preserves a BOM when used outside NNTP commands.
(defun fn-nntp-bom-at-startp (bytes)
  (and (consp bytes) (consp (cdr bytes)) (consp (cdr (cdr bytes)))
       (equal (car bytes) 239)
       (equal (car (cdr bytes)) 187)
       (equal (car (cdr (cdr bytes))) 191)))

(defun fn-nntp-contains-bomp (bytes)
  (if (consp bytes)
      (or (fn-nntp-bom-at-startp bytes)
          (fn-nntp-contains-bomp (cdr bytes)))
    nil))
; This bounded shape/byte preflight happens before tokenization.  The later
; command-specific checks decide which positions may contain validated UTF-8:
; only LIST ACTIVE/NEWSGROUPS wildmats in this profile.  Keywords, group names,
; ranges, Message-IDs, and all legacy arguments remain printable US-ASCII.
(defun fn-nntp-command-inputp (line)
  (and (fn-cbor-at-mostp line *fn-nntp-max-command-octets*)
       (fn-nntp-command-linep line)
       (not (fn-nntp-contains-bomp line))))

(defun fn-nntp-last (xs)
  (mbe :logic
       (if (consp (cdr xs))
           (fn-nntp-last (cdr xs))
         (car xs))
       :exec
       (if (consp (fn-ag-cdr xs))
           (fn-nntp-last (fn-ag-cdr xs))
         (fn-ag-car xs))))

(defun fn-nntp-tokenize-aux (xs word-rev words-rev)
  (mbe :logic
       (if (consp xs)
           (if (fn-nntp-space-or-tabp (car xs))
               (if (consp word-rev)
                   (fn-nntp-tokenize-aux (cdr xs) nil
                                         (cons (reverse word-rev) words-rev))
                 (fn-nntp-tokenize-aux (cdr xs) nil words-rev))
             (fn-nntp-tokenize-aux (cdr xs) (cons (car xs) word-rev) words-rev))
         (if (consp word-rev)
             (reverse (cons (reverse word-rev) words-rev))
           nil))
       :exec
       (if (consp xs)
           (if (fn-nntp-space-or-tabp (fn-ag-car xs))
               (if (consp word-rev)
                   (fn-nntp-tokenize-aux (fn-ag-cdr xs) nil
                                         (cons (fn-ng-reverse word-rev) words-rev))
                 (fn-nntp-tokenize-aux (fn-ag-cdr xs) nil words-rev))
             (fn-nntp-tokenize-aux (fn-ag-cdr xs)
                                   (cons (fn-ag-car xs) word-rev) words-rev))
         (if (consp word-rev)
             (fn-ng-reverse (cons (fn-ng-reverse word-rev) words-rev))
           nil))))
; Leading or trailing white space is rejected.  Interior runs of SP/TAB are
; separators, as RFC 3977 section 3.1 permits.
(defun fn-nntp-tokenize (line)
  (if (and (consp line)
           (fn-nntp-command-linep line)
           (not (fn-nntp-space-or-tabp (car line)))
           (not (fn-nntp-space-or-tabp (fn-nntp-last line))))
      (fn-nntp-tokenize-aux line nil nil)
    nil))

(defun fn-nntp-upcase-byte (byte)
  (if (and (integerp byte) (<= 97 byte) (<= byte 122))
      (- byte 32)
    byte))

(defun fn-nntp-upcase-keyword (bytes)
  (if (consp bytes)
      (cons (fn-nntp-upcase-byte (car bytes))
            (fn-nntp-upcase-keyword (cdr bytes)))
    nil))

(defun fn-nntp-string-octets-aux (chars)
  (mbe :logic
       (if (consp chars)
           (cons (char-code (car chars))
                 (fn-nntp-string-octets-aux (cdr chars)))
         nil)
       :exec
       (if (consp chars)
           (cons (fn-ng-char-code (fn-ag-car chars))
                 (fn-nntp-string-octets-aux (fn-ag-cdr chars)))
         nil)))

(defun fn-nntp-string-octets (text)
  (if (stringp text)
      (fn-nntp-string-octets-aux (coerce text 'list))
    nil))

(defun fn-nntp-octets-chars (bytes)
  (mbe :logic
       (if (consp bytes)
           (cons (code-char (car bytes)) (fn-nntp-octets-chars (cdr bytes)))
         nil)
       :exec
       (if (consp bytes)
           (cons (fn-ng-code-char (fn-ag-car bytes))
                 (fn-nntp-octets-chars (fn-ag-cdr bytes)))
         nil)))

(defun fn-nntp-token-string (token)
  (if (fn-octet-listp token)
      (coerce (fn-nntp-octets-chars token) 'string)
    ""))

(defun fn-nntp-keywordp (token text)
  (equal (fn-nntp-upcase-keyword token) (fn-nntp-string-octets text)))

(defun fn-nntp-keyword-first-bytep (byte)
  (or (and (integerp byte) (<= 65 byte) (<= byte 90))
      (and (integerp byte) (<= 97 byte) (<= byte 122))))

(defun fn-nntp-keyword-rest-bytep (byte)
  (or (fn-nntp-keyword-first-bytep byte)
      (and (integerp byte) (<= 48 byte) (<= byte 57))
      (equal byte 46) (equal byte 45)))

(defun fn-nntp-keyword-tailp (token)
  (if (consp token)
      (and (fn-nntp-keyword-rest-bytep (car token))
           (fn-nntp-keyword-tailp (cdr token)))
    t))

(defun fn-nntp-keyword-tokenp (token)
  ; RFC 3977 section 9.8: keyword = ALPHA 2*(ALPHA / DIGIT / "." / "-").
  (and (consp token)
       (consp (cdr token))
       (consp (cdr (cdr token)))
       (fn-nntp-keyword-first-bytep (car token))
       (fn-nntp-keyword-tailp (cdr token))))

(defun fn-nntp-argument-tokens (tokens)
  ; LIST and MODE have a second command keyword (RFC 3977 section 3.1), not a
  ; first argument.  MODE is unimplemented but the common boundary rule still
  ; keeps a future MODE variant from accidentally consuming its keyword budget.
  (mbe :logic
       (if (and (consp tokens)
                (or (fn-nntp-keywordp (car tokens) "LIST")
                    (fn-nntp-keywordp (car tokens) "MODE")))
           (cdr (cdr tokens))
         (cdr tokens))
       :exec
       (if (and (consp tokens)
                (or (fn-nntp-keywordp (fn-ag-car tokens) "LIST")
                    (fn-nntp-keywordp (fn-ag-car tokens) "MODE")))
           (fn-ag-cdr (fn-ag-cdr tokens))
         (fn-ag-cdr tokens))))

(defun fn-nntp-each-token-at-mostp (tokens bound)
  (mbe :logic
       (if (consp tokens)
           (and (<= (len (car tokens)) bound)
                (fn-nntp-each-token-at-mostp (cdr tokens) bound))
         (null tokens))
       :exec
       (if (consp tokens)
           (and (fn-ng-less-equal (fn-ng-len (fn-ag-car tokens)) bound)
                (fn-nntp-each-token-at-mostp (fn-ag-cdr tokens) bound))
         (null tokens))))

(defun fn-nntp-command-arguments-at-mostp (tokens)
  ; The 510-octet command preflight independently bounds the complete line.
  ; This applies the 497-octet §3.1 limit to each actual argument token, after
  ; excluding the LIST/MODE variant keyword rather than counting separators.
  (fn-nntp-each-token-at-mostp (fn-nntp-argument-tokens tokens)
                               *fn-nntp-max-argument-octets*))

(defun fn-nntp-printable-tokenp (token)
  (if (consp token)
      (and (integerp (car token)) (<= 33 (car token)) (<= (car token) 126)
           (fn-nntp-printable-tokenp (cdr token)))
    t))

(defun fn-nntp-decimal-digitp (byte)
  (and (integerp byte) (<= 48 byte) (<= byte 57)))

(defun fn-nntp-decimal-tokenp (token)
  (if (consp token)
      (and (fn-nntp-decimal-digitp (car token))
           (fn-nntp-decimal-tokenp (cdr token)))
    t))

(defun fn-nntp-decimal-value-aux (token accumulator)
  (mbe :logic
       (if (consp token)
           (fn-nntp-decimal-value-aux
            (cdr token) (+ (* 10 accumulator) (- (car token) 48)))
         accumulator)
       :exec
       (if (consp token)
           (fn-nntp-decimal-value-aux
            (fn-ag-cdr token)
            (+ (* 10 (fix accumulator)) (- (fix (fn-ag-car token)) 48)))
         accumulator)))

(defun fn-nntp-decimal-value (token)
  (fn-nntp-decimal-value-aux token 0))

(defun fn-nntp-number-tokenp (token)
  (mbe :logic
       (and (consp token)
            (<= (len token) 16)
            (fn-nntp-decimal-tokenp token)
            (let ((number (fn-nntp-decimal-value token)))
              (and (<= 1 number) (<= number 2147483647))))
       :exec
       (and (consp token)
            (fn-ng-less-equal (fn-ng-len token) 16)
            (fn-nntp-decimal-tokenp token)
            (let ((number (fn-nntp-decimal-value token)))
              (and (fn-ng-less-equal 1 number)
                   (fn-ng-less-equal number 2147483647))))))
; RFC 3977 section 9.2 defines range as article-number ["-"
; [article-number]].  The parser returns (:ok low high), where an open end is
; represented by the RFC's maximum article number; a reversed closed range is
; syntactically valid and filters to no articles.
(defun fn-nntp-range-parse-aux (token prefix-rev)
  (mbe :logic
       (if (consp token)
           (if (equal (car token) 45)
               (let ((low-token (reverse prefix-rev))
                     (high-token (cdr token)))
                 (if (and (fn-nntp-number-tokenp low-token)
                          (or (null high-token)
                              (fn-nntp-number-tokenp high-token)))
                     (list :ok (fn-nntp-decimal-value low-token)
                           (if (null high-token) 2147483647
                             (fn-nntp-decimal-value high-token)))
                   (list :error)))
             (fn-nntp-range-parse-aux (cdr token) (cons (car token) prefix-rev)))
         (let ((number-token (reverse prefix-rev)))
           (if (fn-nntp-number-tokenp number-token)
               (list :ok (fn-nntp-decimal-value number-token)
                     (fn-nntp-decimal-value number-token))
             (list :error))))
       :exec
       (if (consp token)
           (if (equal (fn-ag-car token) 45)
               (let ((low-token (fn-ng-reverse prefix-rev))
                     (high-token (fn-ag-cdr token)))
                 (if (and (fn-nntp-number-tokenp low-token)
                          (or (null high-token)
                              (fn-nntp-number-tokenp high-token)))
                     (list :ok (fn-nntp-decimal-value low-token)
                           (if (null high-token) 2147483647
                             (fn-nntp-decimal-value high-token)))
                   (list :error)))
             (fn-nntp-range-parse-aux (fn-ag-cdr token)
                                      (cons (fn-ag-car token) prefix-rev)))
         (let ((number-token (fn-ng-reverse prefix-rev)))
           (if (fn-nntp-number-tokenp number-token)
               (list :ok (fn-nntp-decimal-value number-token)
                     (fn-nntp-decimal-value number-token))
             (list :error))))))

(defun fn-nntp-parse-range (token)
  (if (fn-nntp-printable-tokenp token)
      (fn-nntp-range-parse-aux token nil)
    (list :error)))

(defun fn-nntp-range-okp (range)
  (mbe :logic (equal (car range) :ok) :exec (equal (fn-ag-car range) :ok)))

(defun fn-nntp-range-low (range)
  (mbe :logic (car (cdr range)) :exec (fn-ag-car (fn-ag-cdr range))))

(defun fn-nntp-range-high (range)
  (mbe :logic (car (cdr (cdr range)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr range)))))

(defun fn-nntp-message-id-tailp (tail)
  (if (consp tail)
      (if (null (cdr tail))
          (equal (car tail) 62)
        (and (not (equal (car tail) 62))
             (fn-nntp-message-id-tailp (cdr tail))))
    nil))

(defun fn-nntp-message-id-tokenp (token)
  (and (fn-nntp-printable-tokenp token)
       (<= 3 (len token))
       (<= (len token) 250)
       (equal (car token) 60)
       (fn-nntp-message-id-tailp (cdr token))))

(defun fn-nntp-decimal-rev (number)
  (if (natp number)
      (fn-nntp-string-octets-aux (explode-nonnegative-integer number 10 nil))
    nil))

(defun fn-nntp-decimal (number)
  (if (natp number)
      (fn-nntp-decimal-rev number)
    nil))
; Every number a response renders passes through this field renderer, so the
; RFC 3977 section 3.1 length argument for an initial line is structural rather
; than conditional: a rendered field is always a nonempty run of at most ten
; decimal digits.  Section 6 bounds every number this profile renders, so the
; guard is inactive across the whole legal range; see
; fn-nntp-decimal-field-is-exact-in-range in books/nntp-effects.lisp and the
; boundary transcripts in tests/acl2/nntp-tests.lisp.
(defun fn-nntp-decimal-field (number)
  (let ((octets (fn-nntp-decimal number)))
    (if (and (consp octets)
             (fn-nntp-decimal-tokenp octets)
             (<= (len octets) *fn-nntp-max-decimal-octets*))
        octets
      '(48))))

(verify-guards fn-nntp-space-or-tabp)

(verify-guards fn-nntp-command-bytep)

(verify-guards fn-nntp-command-linep)

(verify-guards fn-nntp-bom-at-startp)

(verify-guards fn-nntp-contains-bomp)

(verify-guards fn-nntp-command-inputp)

(verify-guards fn-nntp-last)

(verify-guards fn-nntp-tokenize-aux)

(verify-guards fn-nntp-tokenize)

(verify-guards fn-nntp-upcase-byte)

(verify-guards fn-nntp-upcase-keyword)

(verify-guards fn-nntp-string-octets-aux)

(verify-guards fn-nntp-string-octets)

(verify-guards fn-nntp-octets-chars)

(verify-guards fn-nntp-token-string)

(verify-guards fn-nntp-keywordp)

(verify-guards fn-nntp-keyword-first-bytep)

(verify-guards fn-nntp-keyword-rest-bytep)

(verify-guards fn-nntp-keyword-tailp)

(verify-guards fn-nntp-keyword-tokenp)

(verify-guards fn-nntp-argument-tokens)

(verify-guards fn-nntp-each-token-at-mostp)

(verify-guards fn-nntp-command-arguments-at-mostp)

(verify-guards fn-nntp-printable-tokenp)

(verify-guards fn-nntp-decimal-digitp)

(verify-guards fn-nntp-decimal-tokenp)

(verify-guards fn-nntp-decimal-value-aux)

(verify-guards fn-nntp-decimal-value)

(verify-guards fn-nntp-number-tokenp)

(verify-guards fn-nntp-range-parse-aux)

(verify-guards fn-nntp-parse-range)

(verify-guards fn-nntp-range-okp)

(verify-guards fn-nntp-range-low)

(verify-guards fn-nntp-range-high)

(verify-guards fn-nntp-message-id-tailp)

(verify-guards fn-nntp-message-id-tokenp)

(verify-guards fn-nntp-decimal-rev)

(verify-guards fn-nntp-decimal)

(verify-guards fn-nntp-decimal-field)

; ---------------------------------------------------------------------------
; Export theory
;
; The definitions this book adds are proof vocabulary for the books above it,
; not rules an includer should inherit.  They are withdrawn under one name so
; a book that reasons about the transitions re-enables exactly them in one
; line (books/nntp-invariants.lisp does).  Ground evaluation is unaffected:
; only the :definition runes are withdrawn.

(deftheory fn-nntp-syntax-vocabulary
  '(fn-ng-revappend fn-ng-reverse fn-ng-char-code fn-ng-code-char 
    fn-ng-less-equal fn-ng-len fn-nntp-space-or-tabp fn-nntp-command-bytep 
    fn-nntp-command-linep fn-nntp-bom-at-startp fn-nntp-contains-bomp 
    fn-nntp-command-inputp fn-nntp-last fn-nntp-tokenize-aux fn-nntp-tokenize 
    fn-nntp-upcase-byte fn-nntp-upcase-keyword fn-nntp-string-octets-aux 
    fn-nntp-string-octets fn-nntp-octets-chars fn-nntp-token-string 
    fn-nntp-keywordp fn-nntp-keyword-first-bytep fn-nntp-keyword-rest-bytep 
    fn-nntp-keyword-tailp fn-nntp-keyword-tokenp fn-nntp-argument-tokens 
    fn-nntp-each-token-at-mostp fn-nntp-command-arguments-at-mostp 
    fn-nntp-printable-tokenp fn-nntp-decimal-digitp fn-nntp-decimal-tokenp 
    fn-nntp-decimal-value-aux fn-nntp-decimal-value fn-nntp-number-tokenp 
    fn-nntp-range-parse-aux fn-nntp-parse-range fn-nntp-range-okp 
    fn-nntp-range-low fn-nntp-range-high fn-nntp-message-id-tailp 
    fn-nntp-message-id-tokenp fn-nntp-decimal-rev fn-nntp-decimal 
    fn-nntp-decimal-field))

(in-theory (disable fn-nntp-syntax-vocabulary))
