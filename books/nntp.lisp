; fn experimental NNTP reader session core.
;
; This is a deliberately small laboratory profile, not an NNTP conformance
; claim.  It reads only articles already committed by books/acceptance.lisp;
; it neither posts nor owns a second article store.  Its caller supplies one
; (:command octet-line) event at a time from fn-wire-next.  In particular, a
; host must not dispatch future POST input with bulk fn-wire-feed before it has
; processed the command that changes framing mode.

(in-package "ACL2")
(include-book "acceptance")
(include-book "article-fields")
(include-book "clock")
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

; -----------------------------------------------------------------------------
; Session, effects, and exact article projection

; Session fields are (openp selected-group current-number projected).  NIL
; selected-group and NIL current-number are the RFC's invalid values.
; `projected` is the archive-configuration verdict, computed once by
; fn-nntp-open-session when the reader opens the connection and carried from
; then on.  No command recomputes it: see
; fn-nntp-step-preserves-carried-projection in books/nntp-invariants.lisp.
(defun fn-nntp-session-openp (x)
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-nntp-session-group (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-session-current (x)
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nntp-session-projected (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(defun fn-nntp-make-session (openp group current projected)
  (list openp group current projected))

(defun fn-nntp-sessionp (x)
  (and (true-listp x)
       (equal (len x) 4)
       (or (equal (fn-nntp-session-openp x) t)
           (null (fn-nntp-session-openp x)))
       (or (stringp (fn-nntp-session-group x))
           (null (fn-nntp-session-group x)))
       (or (posp (fn-nntp-session-current x))
           (null (fn-nntp-session-current x)))
       (or (equal (fn-nntp-session-projected x) t)
           (null (fn-nntp-session-projected x)))))

(defun fn-nntp-set-cursor (session group number)
  (fn-nntp-make-session (fn-nntp-session-openp session) group number
                        (fn-nntp-session-projected session)))

(defthm fn-nntp-set-cursor-preserves-group
  (equal (fn-nntp-session-group (fn-nntp-set-cursor session group number))
         group))

(defun fn-nntp-result-session (x)
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-nntp-result-effects (x)
  (mbe :logic (cdr x) :exec (fn-ag-cdr x)))
(defun fn-nntp-make-result (session effects) (cons session effects))
(defun fn-nntp-reply-effect (octets) (list :reply octets))
(defun fn-nntp-close-effect () (list :close))

(defun fn-nntp-crlf (line)
  (mbe :logic (append line '(13 10))
       :exec (fn-ag-append line '(13 10))))

(defun fn-nntp-stuff-lines (lines)
  (mbe :logic
       (if (consp lines)
           (append (fn-nntp-crlf (fn-wire-stuff-line (car lines)))
                   (fn-nntp-stuff-lines (cdr lines)))
         nil)
       :exec
       (if (consp lines)
           (fn-ag-append (fn-nntp-crlf (fn-wire-stuff-line (fn-ag-car lines)))
                         (fn-nntp-stuff-lines (fn-ag-cdr lines)))
         nil)))

(defun fn-nntp-single (session text)
  (fn-nntp-make-result session
                       (list (fn-nntp-reply-effect
                              (fn-nntp-crlf (fn-nntp-string-octets text))))))

(defun fn-nntp-multi (session initial lines)
  (fn-nntp-make-result
   session
   (list (fn-nntp-reply-effect
          (append (fn-nntp-crlf (fn-nntp-string-octets initial))
                  (fn-nntp-stuff-lines lines)
                  '(46 13 10))))))

(defun fn-nntp-multi-octets (session initial lines)
  (fn-nntp-make-result
   session
   (list (fn-nntp-reply-effect
          (append (fn-nntp-crlf initial)
                  (fn-nntp-stuff-lines lines)
                  '(46 13 10))))))

(defun fn-nntp-append-pieces (pieces)
  (mbe :logic
       (if (consp pieces)
           (append (car pieces) (fn-nntp-append-pieces (cdr pieces)))
         nil)
       :exec
       (if (consp pieces)
           (fn-ag-append (fn-ag-car pieces)
                         (fn-nntp-append-pieces (fn-ag-cdr pieces)))
         nil)))

; Return (:ok lines) only when every stored line is complete CRLF-framed and
; carries none of the octets RFC 3977 section 3.1.1 forbids in a multi-line
; block: NUL, a bare LF, or a CR that does not begin a CRLF pair.
(defun fn-nntp-crlf-lines-aux (bytes line-rev lines-rev)
  (declare (xargs :measure (acl2-count bytes)))
  (mbe :logic
       (if (consp bytes)
           (if (equal (car bytes) 13)
               (if (and (consp (cdr bytes)) (equal (car (cdr bytes)) 10))
                   (fn-nntp-crlf-lines-aux (cdr (cdr bytes)) nil
                                           (cons (reverse line-rev) lines-rev))
                 (list :error))
             (if (or (equal (car bytes) 10) (equal (car bytes) 0))
                 (list :error)
               (fn-nntp-crlf-lines-aux (cdr bytes) (cons (car bytes) line-rev)
                                       lines-rev)))
         (if (consp line-rev)
             (list :error)
           (list :ok (reverse lines-rev))))
       :exec
       (if (consp bytes)
           (if (equal (fn-ag-car bytes) 13)
               (if (and (consp (fn-ag-cdr bytes))
                        (equal (fn-ag-car (fn-ag-cdr bytes)) 10))
                   (fn-nntp-crlf-lines-aux (fn-ag-cdr (fn-ag-cdr bytes)) nil
                                           (cons (fn-ng-reverse line-rev) lines-rev))
                 (list :error))
             (if (or (equal (fn-ag-car bytes) 10) (equal (fn-ag-car bytes) 0))
                 (list :error)
               (fn-nntp-crlf-lines-aux (fn-ag-cdr bytes)
                                       (cons (fn-ag-car bytes) line-rev)
                                       lines-rev)))
         (if (consp line-rev)
             (list :error)
           (list :ok (fn-ng-reverse lines-rev))))))

(defun fn-nntp-crlf-lines (bytes)
  (if (fn-octet-listp bytes)
      (fn-nntp-crlf-lines-aux bytes nil nil)
    (list :error)))

; Split a stored article at its first CRLFCRLF.  The header fragment includes
; its final CRLF; the separator's second CRLF is not part of HEAD or BODY.
(defun fn-nntp-split-article-aux (bytes prefix-rev)
  (declare (xargs :measure (acl2-count bytes)))
  (mbe :logic
       (if (and (consp bytes)
           (consp (cdr bytes))
           (consp (cdr (cdr bytes)))
           (consp (cdr (cdr (cdr bytes))))
           (equal (car bytes) 13)
           (equal (car (cdr bytes)) 10)
           (equal (car (cdr (cdr bytes))) 13)
           (equal (car (cdr (cdr (cdr bytes)))) 10))
           (list :ok (reverse (append '(10 13) prefix-rev))
            (cdr (cdr (cdr (cdr bytes)))))
         (if (consp bytes)
             (fn-nntp-split-article-aux (cdr bytes) (cons (car bytes) prefix-rev))
           (list :error)))
       :exec
       (if (and (consp bytes)
                (consp (fn-ag-cdr bytes))
                (consp (fn-ag-cdr (fn-ag-cdr bytes)))
                (consp (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr bytes))))
                (equal (fn-ag-car bytes) 13)
                (equal (fn-ag-car (fn-ag-cdr bytes)) 10)
                (equal (fn-ag-car (fn-ag-cdr (fn-ag-cdr bytes))) 13)
                (equal (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr bytes)))) 10))
           (list :ok (fn-ng-reverse (fn-ag-append '(10 13) prefix-rev))
                 (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr bytes)))))
         (if (consp bytes)
             (fn-nntp-split-article-aux (fn-ag-cdr bytes)
                                        (cons (fn-ag-car bytes) prefix-rev))
           (list :error)))))

(defun fn-nntp-split-article (bytes)
  (if (fn-octet-listp bytes)
      (fn-nntp-split-article-aux bytes nil)
    (list :error)))

(defun fn-nntp-split-okp (x)
  (mbe :logic (equal (car x) :ok) :exec (equal (fn-ag-car x) :ok)))
(defun fn-nntp-split-head (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-split-body (x)
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-nntp-article-section (article kind)
  (let ((payload (fn-article-payload article)))
    (if (equal kind :article)
        (fn-nntp-crlf-lines payload)
      (let ((split (fn-nntp-split-article payload)))
        (if (fn-nntp-split-okp split)
            (if (equal kind :head)
                (fn-nntp-crlf-lines (fn-nntp-split-head split))
              (fn-nntp-crlf-lines (fn-nntp-split-body split)))
          (list :error))))))

; acceptance.lisp intentionally permits opaque strings and payload octets.  An
; NNTP projection must be stricter before interpolating any stored field into a
; response line.  These checks are local projection guards, not a change to the
; broader durable acceptance domain.
;
; They are split by cost and by blast radius.  The configuration checks are
; whole-archive and run exactly once, in fn-nntp-open-session, when the reader
; opens a connection; the served path reads the carried verdict instead
; (AGENTS.md, "no whole-state revalidation on a served path").  The per-article
; checks run only for the one article a command names, and a stored article
; that fails them degrades only itself.

; A projected group name is interpolated into 211 and 215 lines, so it must be
; a nonempty printable US-ASCII token short enough to keep every generated
; initial line inside RFC 3977 section 3.1's 512 octets.
(defun fn-nntp-safe-group-namep (text)
  (and (stringp text)
       (let ((octets (fn-nntp-string-octets text)))
         (and (consp octets)
              (<= (len octets) *fn-nntp-max-group-octets*)
              (fn-nntp-printable-tokenp octets)))))

(defun fn-nntp-safe-group-listp (texts)
  (if (consp texts)
      (and (fn-nntp-safe-group-namep (car texts))
           (fn-nntp-safe-group-listp (cdr texts)))
    (null texts)))

; Watermarks are rendered as the low and high numbers of an empty group, so
; RFC 3977 section 6's maximum article number bounds their decimal length.
(defun fn-nntp-nexts-boundedp (nexts)
  (if (consp nexts)
      (and (consp (car nexts))
           (natp (cdr (car nexts)))
           (<= (cdr (car nexts)) *fn-nntp-max-article-number*)
           (fn-nntp-nexts-boundedp (cdr nexts)))
    (null nexts)))

; Per-article: the stored identifier.  The string length is checked before the
; octets are built, so this costs at most 251 octets of work for any stored
; article, however large its identifier.  STAT, NEXT, and LAST need only this.
(defun fn-nntp-article-idp (article)
  (let ((text (fn-article-msgid article)))
    (and (stringp text)
         (<= (length text) *fn-nntp-max-message-id-octets*)
         (fn-nntp-message-id-tokenp (fn-nntp-string-octets text)))))

; Per-article: the stored bytes.  Only ARTICLE, HEAD, and BODY need this, and
; they pay for the one article they name.
(defun fn-nntp-article-framedp (article)
  (let ((payload (fn-article-payload article)))
    (and (equal (car (fn-nntp-crlf-lines payload)) :ok)
         (fn-nntp-split-okp (fn-nntp-split-article payload)))))

(defun fn-nntp-projection-articlep (article)
  (and (fn-nntp-article-idp article)
       (fn-nntp-article-framedp article)))

; Configuration-level projection.  This is the whole-archive recognizer.  It
; says nothing about the contents of individual articles: a committed article
; whose stored bytes cannot be projected no longer denies the service.
(defun fn-nntp-projectionp (archive)
  (and (fn-statep archive)
       (fn-nntp-safe-group-listp (fn-state-groups archive))
       (fn-nntp-nexts-boundedp (fn-state-nexts archive))
       (<= (len (fn-state-articles archive)) *fn-nntp-max-article-number*)))

(defun fn-nntp-open-session (archive)
  (fn-nntp-make-session t nil nil
                        (if (fn-nntp-projectionp archive) t nil)))

; -----------------------------------------------------------------------------
; Projection from the committed acceptance state

(defun fn-nntp-membership-number (group memberships)
  (mbe :logic
       (if (consp memberships)
           (if (equal group (car (car memberships)))
               (cdr (car memberships))
             (fn-nntp-membership-number group (cdr memberships)))
         0)
       :exec
       (if (consp memberships)
           (if (equal group (fn-ag-car (fn-ag-car memberships)))
               (fn-ag-cdr (fn-ag-car memberships))
             (fn-nntp-membership-number group (fn-ag-cdr memberships)))
         0)))

; The available local number of `article` in `group`, or 0.  An article is
; available at a number only when the number is a valid RFC 3977 section 6
; article number and the stored identifier can be rendered: STAT, NEXT, and
; LAST answer with that identifier and nothing else.  An article that fails
; this is excluded from group counts, water marks, LISTGROUP ranges, and
; NEXT/LAST, and a command that names its number is answered explicitly.
(defun fn-nntp-article-number (group article)
  (let ((number (fn-nntp-membership-number
                 group (fn-article-memberships article))))
    (if (and (posp number)
             (<= number *fn-nntp-max-article-number*)
             (fn-nntp-article-idp article))
        number
      0)))

(defthm fn-nntp-article-number-natp
  (natp (fn-nntp-article-number group article))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-article-number-bounded
  (<= (fn-nntp-article-number group article) *fn-nntp-max-article-number*)
  :rule-classes (:rewrite :linear))

(defthm fn-nntp-available-number-article-is-projectable
  (implies (posp (fn-nntp-article-number group article))
           (fn-nntp-article-idp article)))

; The article committed at a raw local number, whether or not it is available.
; Retrieval by number uses this so that a request naming an unavailable article
; is answered explicitly rather than silently.
(defun fn-nntp-find-group-number (group number articles)
  (if (consp articles)
      (if (equal (fn-nntp-membership-number
                  group (fn-article-memberships (car articles)))
                 number)
          (car articles)
        (fn-nntp-find-group-number group number (cdr articles)))
    nil))

; The article available at a number.  This is the cursor's referent.
(defun fn-nntp-available-article (group number articles)
  (if (consp articles)
      (if (and (posp number)
               (equal (fn-nntp-article-number group (car articles)) number))
          (car articles)
        (fn-nntp-available-article group number (cdr articles)))
    nil))

(defthm fn-nntp-available-article-is-projectable
  (implies (consp (fn-nntp-available-article group number articles))
           (fn-nntp-article-idp (fn-nntp-available-article group number articles))))

(defun fn-nntp-insert-number (number numbers)
  (mbe :logic
       (if (consp numbers)
           (if (< number (car numbers))
               (cons number numbers)
             (cons (car numbers) (fn-nntp-insert-number number (cdr numbers))))
         (list number))
       :exec
       (if (consp numbers)
           (if (fn-ag-less number (fn-ag-car numbers))
               (cons number numbers)
             (cons (fn-ag-car numbers)
                   (fn-nntp-insert-number number (fn-ag-cdr numbers))))
         (list number))))

(defun fn-nntp-orderedp (numbers)
  (if (consp numbers)
      (if (consp (cdr numbers))
          (and (fn-ng-less-equal (car numbers) (car (cdr numbers)))
               (fn-nntp-orderedp (cdr numbers)))
        t)
    t))

(defthm fn-nntp-insert-number-preserves-ordered
  (implies (and (fn-nntp-orderedp numbers) (rationalp number))
           (fn-nntp-orderedp (fn-nntp-insert-number number numbers)))
  :hints (("Goal" :induct (fn-nntp-orderedp numbers)
           :in-theory (enable fn-nntp-orderedp fn-nntp-insert-number))))

(defthm fn-nntp-insert-number-members
  (iff (member-equal value (fn-nntp-insert-number number numbers))
       (or (equal value number) (member-equal value numbers)))
  :hints (("Goal" :induct (fn-nntp-insert-number number numbers)
           :in-theory (enable fn-nntp-insert-number))))

; One pass over the committed articles.  The count, the water marks, NEXT, and
; LAST never build or sort a number list; only LISTGROUP does, and it sorts
; only the numbers inside the range its own argument names.
(defun fn-nntp-group-count (group articles)
  (if (consp articles)
      (if (posp (fn-nntp-article-number group (car articles)))
          (+ 1 (fn-nntp-group-count group (cdr articles)))
        (fn-nntp-group-count group (cdr articles)))
    0))

(defthm fn-nntp-group-count-natp
  (natp (fn-nntp-group-count group articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-count-at-most-articles
  (<= (fn-nntp-group-count group articles) (len articles))
  :rule-classes (:rewrite :linear))

(defun fn-nntp-group-low (group articles)
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles)))
            (rest (fn-nntp-group-low group (cdr articles))))
        (if (and (posp number)
                 (or (not (posp rest)) (< number rest)))
            number
          rest))
    0))

(defthm fn-nntp-group-low-natp
  (natp (fn-nntp-group-low group articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-low-bounded
  (<= (fn-nntp-group-low group articles) *fn-nntp-max-article-number*)
  :rule-classes (:rewrite :linear))

(defthm fn-nntp-group-low-is-available
  (implies (posp (fn-nntp-group-low group articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-low group articles) articles))))

(defun fn-nntp-group-high (group articles)
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles)))
            (rest (fn-nntp-group-high group (cdr articles))))
        (if (and (posp number) (< rest number)) number rest))
    0))

(defthm fn-nntp-group-high-natp
  (natp (fn-nntp-group-high group articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-high-bounded
  (<= (fn-nntp-group-high group articles) *fn-nntp-max-article-number*)
  :rule-classes (:rewrite :linear))

(defthm fn-nntp-group-high-is-available
  (implies (posp (fn-nntp-group-high group articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-high group articles) articles))))

(defun fn-nntp-group-next-number (group current articles)
  ; The least available number strictly greater than `current`, or 0.
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles)))
            (rest (fn-nntp-group-next-number group current (cdr articles))))
        (if (and (posp number)
                 (fn-ag-less current number)
                 (or (not (posp rest)) (< number rest)))
            number
          rest))
    0))

(defthm fn-nntp-group-next-number-natp
  (natp (fn-nntp-group-next-number group current articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-next-number-is-available
  (implies (posp (fn-nntp-group-next-number group current articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-next-number group current articles)
                   articles))))

(defun fn-nntp-group-last-number (group current articles)
  ; The greatest available number strictly less than `current`, or 0.
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles)))
            (rest (fn-nntp-group-last-number group current (cdr articles))))
        (if (and (posp number)
                 (fn-ag-less number current)
                 (< rest number))
            number
          rest))
    0))

(defthm fn-nntp-group-last-number-natp
  (natp (fn-nntp-group-last-number group current articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-last-number-is-available
  (implies (posp (fn-nntp-group-last-number group current articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-last-number group current articles)
                   articles))))

; LISTGROUP's list.  Only the numbers inside the requested range are inserted,
; so the sort is charged to the command's own range and not to the archive.
(defun fn-nntp-group-range-numbers (group low high articles)
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles))))
        (if (and (posp number)
                 (fn-ng-less-equal low number)
                 (fn-ng-less-equal number high))
            (fn-nntp-insert-number
             number (fn-nntp-group-range-numbers group low high (cdr articles)))
          (fn-nntp-group-range-numbers group low high (cdr articles))))
    nil))

(defthm fn-nntp-group-range-numbers-are-ordered
  (fn-nntp-orderedp (fn-nntp-group-range-numbers group low high articles)))

(defthm fn-nntp-group-range-numbers-are-available
  (implies (member-equal value
                         (fn-nntp-group-range-numbers group low high articles))
           (and (posp value)
                (consp (fn-nntp-available-article group value articles))))
  :rule-classes nil)

(defun fn-nntp-number-lines (numbers)
  (if (consp numbers)
      (cons (fn-nntp-decimal-field (car numbers))
            (fn-nntp-number-lines (cdr numbers)))
    nil))

(defun fn-nntp-group-summary (archive group)
  (let ((low (fn-nntp-group-low group (fn-state-articles archive))))
    (if (posp low)
        (list (fn-nntp-group-count group (fn-state-articles archive))
              low
              (fn-nntp-group-high group (fn-state-articles archive)))
      (let ((watermark (fn-next-number group (fn-state-nexts archive))))
        (list 0 watermark (if (posp watermark) (- watermark 1) 0))))))

(defun fn-nntp-summary-count (x)
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-nntp-summary-low (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-summary-high (x)
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-nntp-group-initial (archive group)
  (let ((summary (fn-nntp-group-summary archive group)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets "211 ")
           (fn-nntp-decimal-field (fn-nntp-summary-count summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-string-octets group)))))

(defun fn-nntp-group-result (session archive group)
  (if (mbe :logic (member-equal group (fn-state-groups archive))
           :exec (fn-ag-member group (fn-state-groups archive)))
      (let* ((low (fn-nntp-group-low group (fn-state-articles archive)))
             (current (if (posp low) low nil))
             (next-session (fn-nntp-set-cursor session group current)))
        (fn-nntp-make-result
         next-session
         (list (fn-nntp-reply-effect
                (fn-nntp-crlf (fn-nntp-group-initial archive group))))))
    (fn-nntp-single session "411 no such newsgroup")))

(defthm fn-nntp-unknown-group-preserves-session
  (implies (not (member-equal group (fn-state-groups archive)))
           (equal (fn-nntp-result-session (fn-nntp-group-result session archive group))
                  session)))

(defun fn-nntp-listgroup-initial (archive group)
  (append (fn-nntp-group-initial archive group)
          (fn-nntp-string-octets " list follows")))

(defun fn-nntp-listgroup-result (session archive group range)
  (if (mbe :logic (member-equal group (fn-state-groups archive))
           :exec (fn-ag-member group (fn-state-groups archive)))
      (let* ((low (fn-nntp-group-low group (fn-state-articles archive)))
             (current (if (posp low) low nil))
             (next-session (fn-nntp-set-cursor session group current))
             (shown (fn-nntp-group-range-numbers group
                                                 (fn-nntp-range-low range)
                                                 (fn-nntp-range-high range)
                                                 (fn-state-articles archive))))
        (fn-nntp-multi-octets next-session
                              (fn-nntp-listgroup-initial archive group)
                              (fn-nntp-number-lines shown)))
    (fn-nntp-single session "411 no such newsgroup")))

(defthm fn-nntp-listgroup-unknown-preserves-session
  (implies (not (member-equal group (fn-state-groups archive)))
           (equal (fn-nntp-result-session
                   (fn-nntp-listgroup-result session archive group range))
                  session)))

(defun fn-nntp-listgroup-command (session archive args)
  (let ((all-range (list :ok 1 2147483647)))
    (if (null args)
        (let ((group (fn-nntp-session-group session)))
          (if (null group)
              (fn-nntp-single session "412 no newsgroup selected")
            (if (mbe :logic (member-equal group (fn-state-groups archive))
                     :exec (fn-ag-member group (fn-state-groups archive)))
                (fn-nntp-listgroup-result session archive group all-range)
              (fn-nntp-single session "412 no newsgroup selected"))))
      (if (and (consp args) (null (cdr args))
               (fn-nntp-printable-tokenp (car args)))
          (fn-nntp-listgroup-result session archive
                                    (fn-nntp-token-string (car args)) all-range)
        (if (and (consp args) (consp (cdr args)) (null (cdr (cdr args)))
                 (fn-nntp-printable-tokenp (car args)))
            (let ((range (fn-nntp-parse-range (car (cdr args)))))
              (if (fn-nntp-range-okp range)
                  (fn-nntp-listgroup-result session archive
                                            (fn-nntp-token-string (car args)) range)
                (fn-nntp-single session "501 syntax error")))
          (fn-nntp-single session "501 syntax error"))))))

; -----------------------------------------------------------------------------
; Command responses

(defun fn-nntp-retrieval-initial (kind number article)
  (fn-nntp-append-pieces
   (list (cond ((equal kind :article) (fn-nntp-string-octets "220 "))
               ((equal kind :head) (fn-nntp-string-octets "221 "))
               ((equal kind :body) (fn-nntp-string-octets "222 "))
               (t (fn-nntp-string-octets "223 ")))
         (fn-nntp-decimal-field number) '(32)
         (fn-nntp-string-octets (fn-article-msgid article))
         (cond ((equal kind :article) (fn-nntp-string-octets " article follows"))
               ((equal kind :head) (fn-nntp-string-octets " headers follow"))
               ((equal kind :body) (fn-nntp-string-octets " body follows"))
               (t (fn-nntp-string-octets " retrieved"))))))

; A stored article that cannot be projected degrades only itself, and it says
; which of the two reasons applies.  RFC 3977 section 3.2.1 assigns 503 to a
; recognized command whose legitimate case the server handles only in part.
; The cursor moves only on a success; every refusal returns `session`.
;
; The first branch is defensive.  fn-nntp-available-article never returns an
; article that fails fn-nntp-article-idp, and a Message-ID retrieval matched the
; stored identifier against a token that is itself at most 250 printable
; octets, so no composed path reaches it; it is not the subject of any theorem.
(defun fn-nntp-article-response (session article number kind updatep group)
  (if (not (fn-nntp-article-idp article))
      (fn-nntp-single session "503 stored article identifier unavailable")
    (let ((next-session (if updatep
                            (fn-nntp-set-cursor session group number)
                          session)))
      (if (equal kind :stat)
          (fn-nntp-make-result
           next-session
           (list (fn-nntp-reply-effect
                  (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article)))))
        (let ((section (fn-nntp-article-section article kind)))
          (if (and (fn-nntp-article-framedp article)
                   (equal (car section) :ok))
              (fn-nntp-make-result
               next-session
               (list (fn-nntp-reply-effect
                      (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                              (fn-nntp-stuff-lines (car (cdr section)))
                              '(46 13 10)))))
            (fn-nntp-single session "503 stored article framing unavailable")))))))

(defun fn-nntp-current-retrieval (session archive kind)
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((article (fn-nntp-available-article group current
                                                  (fn-state-articles archive))))
          (if (consp article)
              (fn-nntp-article-response session article current kind t group)
            (fn-nntp-single session "420 no current article")))))))

(defun fn-nntp-number-retrieval (session archive kind token)
  (if (not (fn-nntp-number-tokenp token))
      (fn-nntp-single session "501 syntax error")
    (let ((group (fn-nntp-session-group session))
          (number (fn-nntp-decimal-value token)))
      (if (null group)
          (fn-nntp-single session "412 no newsgroup selected")
        (let ((article (fn-nntp-find-group-number group number
                                                  (fn-state-articles archive))))
          (if (consp article)
              (fn-nntp-article-response session article number kind t group)
            (fn-nntp-single session "423 no article with that number")))))))

(defun fn-nntp-msgid-retrieval (session archive kind token)
  (if (not (fn-nntp-message-id-tokenp token))
      (fn-nntp-single session "501 syntax error")
    (let ((article (fn-find-article (fn-nntp-token-string token)
                                    (fn-state-articles archive))))
      (if (consp article)
          ; RFC 3977 permits zero for a message-id retrieval.  It deliberately
          ; does not alter either selected group or current article number.
          (fn-nntp-article-response session article 0 kind nil nil)
        (fn-nntp-single session "430 no article with that message-id")))))

(defthm fn-nntp-msgid-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-msgid-retrieval session archive kind token))
         session))

(defun fn-nntp-retrieval (session archive kind args)
  (mbe :logic
       (if (null args)
           (fn-nntp-current-retrieval session archive kind)
         (if (null (cdr args))
             (let ((token (car args)))
               (if (fn-nntp-number-tokenp token)
                   (fn-nntp-number-retrieval session archive kind token)
                 (fn-nntp-msgid-retrieval session archive kind token)))
           (fn-nntp-single session "501 syntax error")))
       :exec
       (if (null args)
           (fn-nntp-current-retrieval session archive kind)
         (if (null (fn-ag-cdr args))
             (let ((token (fn-ag-car args)))
               (if (fn-nntp-number-tokenp token)
                   (fn-nntp-number-retrieval session archive kind token)
                 (fn-nntp-msgid-retrieval session archive kind token)))
           (fn-nntp-single session "501 syntax error")))))

(defun fn-nntp-next-or-last (session archive direction)
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((number (if (equal direction :next)
                          (fn-nntp-group-next-number
                           group current (fn-state-articles archive))
                        (fn-nntp-group-last-number
                         group current (fn-state-articles archive)))))
          (if (posp number)
              (let ((article (fn-nntp-available-article
                              group number (fn-state-articles archive))))
                (fn-nntp-article-response session article number :stat t group))
            (if (equal direction :next)
                (fn-nntp-single session "421 no next article")
              (fn-nntp-single session "422 no previous article"))))))))

(defun fn-nntp-active-line (archive group)
  (let ((summary (fn-nntp-group-summary archive group)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets group) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary))
           (fn-nntp-string-octets " y")))))

(defun fn-nntp-active-lines (archive groups)
  (if (consp groups)
      (cons (fn-nntp-active-line archive (car groups))
            (fn-nntp-active-lines archive (cdr groups)))
    nil))

(defun fn-nntp-newsgroup-lines (groups)
  (if (consp groups)
      (cons (fn-nntp-append-pieces
             (list (fn-nntp-string-octets (car groups))
                   (fn-nntp-string-octets " fn experimental group")))
            (fn-nntp-newsgroup-lines (cdr groups)))
    nil))

; `patterns` is an internal successful `fn-wildmat-parse` result, never an
; externally supplied representation.  Group names are projection-guarded
; printable ASCII and no longer than the local wildmat target cap, so their
; UTF-8 decoding is exact and bounded before the DP match is called.
(defun fn-nntp-group-matches-parsed-wildmatp (patterns group)
  (let ((decoded (fn-wildmat-decode (fn-nntp-string-octets group))))
    (and (fn-wildmat-result-okp decoded)
         (mbe :logic
              (fn-wildmat-match-codepoints patterns
                                           (fn-wildmat-result-value decoded))
              :exec
              (ec-call
               (fn-wildmat-match-codepoints
                patterns (fn-wildmat-result-value decoded)))))))

(defun fn-nntp-filter-groups-by-wildmat (patterns groups)
  (if (consp groups)
      (if (fn-nntp-group-matches-parsed-wildmatp patterns (car groups))
          (cons (car groups)
                (fn-nntp-filter-groups-by-wildmat patterns (cdr groups)))
        (fn-nntp-filter-groups-by-wildmat patterns (cdr groups)))
    nil))

(defun fn-nntp-list-active (session archive groups)
  (fn-nntp-multi session "215 list of active newsgroups follows"
                 (fn-nntp-active-lines archive groups)))

(defun fn-nntp-list-newsgroups (session groups)
  (fn-nntp-multi session "215 list of newsgroups follows"
                 (fn-nntp-newsgroup-lines groups)))

(defun fn-nntp-list-filtered-response (session archive kind wildmat)
  ; Parse once per LIST command, then reuse that parsed value for every group.
  (let ((parsed (fn-wildmat-parse wildmat)))
    (if (fn-wildmat-result-okp parsed)
        (let ((groups (fn-nntp-filter-groups-by-wildmat
                       (fn-wildmat-result-value parsed)
                       (fn-state-groups archive))))
          (if (equal kind :active)
              (fn-nntp-list-active session archive groups)
            (fn-nntp-list-newsgroups session groups)))
      (fn-nntp-single session "501 syntax error"))))

(defun fn-nntp-list-active-or-newsgroups (session archive kind args)
  (if (null args)
      (if (equal kind :active)
          (fn-nntp-list-active session archive (fn-state-groups archive))
        (fn-nntp-list-newsgroups session (fn-state-groups archive)))
    (if (and (consp args) (null (cdr args)))
        (fn-nntp-list-filtered-response session archive kind (car args))
      (fn-nntp-single session "501 syntax error"))))

(defun fn-nntp-list-wildmat-argumentp (args)
  (if (null args)
      t
    (if (and (consp args) (null (cdr args)))
        (fn-wildmat-result-okp (fn-wildmat-parse (car args)))
      nil)))

(defun fn-nntp-list-unmaintained-response (session keyword args)
  ; RFC 3977 sections 7.6.4/7.6.5, 8.4, 8.6, and 9.6 specify these arities.
  ; A syntactically valid request for a recognized but unmaintained item is
  ; 503; an argument forbidden by that item's grammar remains 501.
  (if (fn-nntp-keywordp keyword "ACTIVE.TIMES")
      (if (fn-nntp-list-wildmat-argumentp args)
          (fn-nntp-single session "503 data item not stored")
        (fn-nntp-single session "501 syntax error"))
    (if (fn-nntp-keywordp keyword "DISTRIB.PATS")
        (if (null args)
            (fn-nntp-single session "503 data item not stored")
          (fn-nntp-single session "501 syntax error"))
      (if (fn-nntp-keywordp keyword "OVERVIEW.FMT")
          (if (null args)
              (fn-nntp-list-overview-fmt session)
            (fn-nntp-single session "501 syntax error"))
        (if (fn-nntp-keywordp keyword "HEADERS")
            (if (or (null args)
                    (and (consp args) (null (cdr args))
                         (or (fn-nntp-keywordp (car args) "MSGID")
                             (fn-nntp-keywordp (car args) "RANGE"))))
                (fn-nntp-single session "503 data item not stored")
              (fn-nntp-single session "501 syntax error"))
          (fn-nntp-single session "501 unsupported LIST variant"))))))

(defun fn-nntp-list-response (session archive args)
  (mbe :logic
       (if (null args)
           (fn-nntp-list-active session archive (fn-state-groups archive))
         (let ((keyword (car args)) (arguments (cdr args)))
           (if (not (fn-nntp-keyword-tokenp keyword))
               (fn-nntp-single session "501 syntax error")
             (if (fn-nntp-keywordp keyword "ACTIVE")
                 (fn-nntp-list-active-or-newsgroups session archive :active arguments)
               (if (fn-nntp-keywordp keyword "NEWSGROUPS")
                   (fn-nntp-list-active-or-newsgroups session archive :newsgroups arguments)
                 (fn-nntp-list-unmaintained-response session keyword arguments))))))
       :exec
       (if (null args)
           (fn-nntp-list-active session archive (fn-state-groups archive))
         (let ((keyword (fn-ag-car args)) (arguments (fn-ag-cdr args)))
           (if (not (fn-nntp-keyword-tokenp keyword))
               (fn-nntp-single session "501 syntax error")
             (if (fn-nntp-keywordp keyword "ACTIVE")
                 (fn-nntp-list-active-or-newsgroups session archive :active arguments)
               (if (fn-nntp-keywordp keyword "NEWSGROUPS")
                   (fn-nntp-list-active-or-newsgroups session archive :newsgroups arguments)
                 (fn-nntp-list-unmaintained-response session keyword arguments))))))))

(defun fn-nntp-capability-lines ()
  ; RFC 3977 section 3.3.2 makes a capability label a promise about a whole
  ; bundle, so each label below is advertised only because every command it
  ; indicates in appendix B is implemented with its argument forms:
  ; READER covers ARTICLE, BODY, DATE, GROUP, LAST, LISTGROUP, NEWGROUPS and
  ; NEXT; OVER MSGID covers OVER in all three forms and LIST OVERVIEW.FMT;
  ; LIST names exactly the variants that answer with data.  No POST, IHAVE,
  ; NEWNEWS, HDR, MODE-READER, TLS, authentication or compression capability
  ; is advertised, and this reader is not mode-switching (section 3.4.2).
  (list (fn-nntp-string-octets "VERSION 2")
        (fn-nntp-string-octets "READER")
        (fn-nntp-string-octets "OVER MSGID")
        (fn-nntp-string-octets "LIST ACTIVE NEWSGROUPS OVERVIEW.FMT")
        (fn-nntp-string-octets "IMPLEMENTATION fn-nntp-lab")))

(defun fn-nntp-unadvertised-capability-lines ()
  (list (fn-nntp-string-octets "VERSION 2")
        (fn-nntp-string-octets "IMPLEMENTATION fn-nntp-lab")))

(defun fn-nntp-capabilities (session)
  (fn-nntp-multi session "101 capability list follows"
                 (if *fn-nntp-advertise-readerp*
                     (fn-nntp-capability-lines)
                   (fn-nntp-unadvertised-capability-lines))))

(defun fn-nntp-help (session)
  (fn-nntp-multi session "100 help text follows"
                 (list (fn-nntp-string-octets "CAPABILITIES HEAD HELP QUIT STAT")
                       (fn-nntp-string-octets "GROUP ARTICLE BODY NEXT LAST LIST LISTGROUP")
                       (fn-nntp-string-octets "DATE NEWGROUPS MODE OVER"))))

; -----------------------------------------------------------------------------
; Reader environment: the clock observation and the persisted group-creation
; facts
;
; RFC 3977 section 7.1 requires DATE to report the server's own clock, and
; section 7.3 requires NEWGROUPS to report group creation times.  Neither is
; invented here.  The owner or host supplies one `fn-clock-observationp'
; (books/clock.lisp) and a list of persisted creation facts; the reader reads
; them and refuses when they are absent.  A creation fact is
;   (:fn-nntp-group-fact name created-at-dtn-ms observation)
; where `created-at-dtn-ms' is the DTN time (RFC 9171 section 4.2.6,
; milliseconds since 2000-01-01T00:00:00Z) at which the group was created and
; `observation' is the clock observation under which that time was established.
; The fact carries its own provenance so that a creation time can never be
; back-filled from the reader's current clock.  The mutable-owner lane
; persists these records; this book consumes the shape.

(defun fn-nntp-group-fact (name created-at observation)
  (declare (xargs :guard t))
  (list :fn-nntp-group-fact name created-at observation))

(defun fn-nntp-fact-name (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-fact-created (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nntp-fact-observation (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(defun fn-nntp-group-factp (x)
  (and (true-listp x)
       (equal (len x) 4)
       (equal (car x) :fn-nntp-group-fact)
       (fn-nntp-safe-group-namep (fn-nntp-fact-name x))
       (natp (fn-nntp-fact-created x))
       (<= (fn-nntp-fact-created x) *fn-clock-max*)
       (fn-clock-observationp (fn-nntp-fact-observation x))))

(defun fn-nntp-group-fact-listp (xs)
  (if (consp xs)
      (and (fn-nntp-group-factp (car xs))
           (fn-nntp-group-fact-listp (cdr xs)))
    (null xs)))

(defun fn-nntp-env (observation facts)
  (declare (xargs :guard t))
  (list :fn-nntp-env observation facts))

(defun fn-nntp-env-observation (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-env-facts (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-nntp-envp (x)
  (and (true-listp x)
       (equal (len x) 3)
       (equal (car x) :fn-nntp-env)
       (fn-clock-observationp (fn-nntp-env-observation x))
       (fn-nntp-group-fact-listp (fn-nntp-env-facts x))))

; The environment a host supplies when it holds no clock reading and no
; persisted creation facts.  DATE and NEWGROUPS refuse against it; they never
; fall back to a fabricated timestamp.
(defun fn-nntp-blind-env ()
  (declare (xargs :guard t))
  (fn-nntp-env (fn-clock-observation 0 0 0 nil) nil))

(defthm fn-nntp-blind-env-is-an-env
  (fn-nntp-envp (fn-nntp-blind-env)))

; -----------------------------------------------------------------------------
; Bounded integer and calendar arithmetic
;
; Every division below is guard-total on non-negative integers.  The civil
; conversion is Howard Hinnant's closed-form `civil_from_days'/`days_from_civil'
; pair: no loop over years, so the work is constant whatever the clock reads.
; It is exact for a proleptic Gregorian day count that excludes leap seconds,
; which is what RFC 9171 section 4.2.6's DTN time is.  fn's reader has no
; timezone database, so its local time zone IS Coordinated Universal Time; RFC
; 3977 section 7.3.2 notes that the protocol cannot convey any other choice.

(defun fn-nntp-div (a b)
  (declare (xargs :guard t))
  (if (and (integerp a) (integerp b) (< 0 b)) (floor a b) 0))

(defun fn-nntp-mod (a b)
  (declare (xargs :guard t))
  (if (and (integerp a) (integerp b) (< 0 b)) (mod a b) 0))

; Days from 1970-01-01 to 2000-01-01, the DTN epoch.
(defconst *fn-nntp-dtn-epoch-days* 10957)
(defconst *fn-nntp-max-rendered-year* 9999)

(defun fn-nntp-civil-from-days (z)
  (declare (xargs :guard t))
  (let* ((shifted (+ (nfix z) 719468))
         (era (fn-nntp-div shifted 146097))
         (doe (- shifted (* era 146097)))
         (yoe (fn-nntp-div (- (+ doe (fn-nntp-div doe 36524))
                              (+ (fn-nntp-div doe 1460)
                                 (fn-nntp-div doe 146096)))
                           365))
         (year (+ yoe (* era 400)))
         (doy (- doe (- (+ (* 365 yoe) (fn-nntp-div yoe 4))
                        (fn-nntp-div yoe 100))))
         (mp (fn-nntp-div (+ (* 5 doy) 2) 153))
         (day (+ (- doy (fn-nntp-div (+ (* 153 mp) 2) 5)) 1))
         (month (if (< mp 10) (+ mp 3) (- mp 9))))
    (list (if (<= month 2) (+ year 1) year) month day)))

(defun fn-nntp-days-from-civil (year month day)
  (declare (xargs :guard t))
  (let* ((y (if (<= (ifix month) 2) (- (ifix year) 1) (ifix year)))
         (era (fn-nntp-div y 400))
         (yoe (- y (* era 400)))
         (doy (+ (fn-nntp-div (+ (* 153 (if (< 2 (ifix month))
                                            (- (ifix month) 3)
                                          (+ (ifix month) 9)))
                                 2)
                              5)
                 (- (ifix day) 1)))
         (doe (+ (* yoe 365) (fn-nntp-div yoe 4)
                 (- (fn-nntp-div yoe 100)) doy)))
    (+ (* era 146097) doe -719468)))

; (year month day hour minute second) of a DTN millisecond reading.
(defun fn-nntp-dtn-civil (ms)
  (declare (xargs :guard t))
  (let* ((secs (fn-nntp-div (nfix ms) 1000))
         (days (+ (fn-nntp-div secs 86400) *fn-nntp-dtn-epoch-days*))
         (tod (fn-nntp-mod secs 86400))
         (ymd (fn-nntp-civil-from-days days)))
    (list (car ymd) (car (cdr ymd)) (car (cdr (cdr ymd)))
          (fn-nntp-div tod 3600)
          (fn-nntp-mod (fn-nntp-div tod 60) 60)
          (fn-nntp-mod tod 60))))

(defun fn-nntp-civil-year (x) (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-nntp-civil-month (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-civil-day (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nntp-civil-hour (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-nntp-civil-minute (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-nntp-civil-second (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr x))))))))

; DTN milliseconds for a civil instant, clamped at the DTN epoch.  A requested
; NEWGROUPS instant before 2000-01-01 selects every recorded creation.
(defun fn-nntp-civil-dtn-ms (year month day hour minute second)
  (declare (xargs :guard t))
  (let ((secs (+ (* (- (fn-nntp-days-from-civil year month day)
                       *fn-nntp-dtn-epoch-days*)
                    86400)
                 (* (nfix hour) 3600) (* (nfix minute) 60) (nfix second))))
    (if (< secs 0) 0 (* 1000 secs))))

; The host reads a clock; it does not decide what the reading means.  A POSIX
; millisecond reading reaches the reader unconverted and this function, not the
; adapter, shifts it to RFC 9171 section 4.2.6's DTN epoch.  A reading before
; 2000-01-01 clamps to the epoch rather than becoming a negative time.
(defconst *fn-nntp-unix-dtn-offset-ms* 946684800000)

(defun fn-nntp-unix-dtn-ms (unix-ms)
  (declare (xargs :guard t))
  (nfix (- (nfix unix-ms) *fn-nntp-unix-dtn-offset-ms*)))

(defun fn-nntp-host-observation (monotonic-ms unix-ms error-ms has-wall)
  (declare (xargs :guard t))
  (fn-clock-observation (nfix monotonic-ms) (fn-nntp-unix-dtn-ms unix-ms)
                        (nfix error-ms) (if has-wall t nil)))

(defthm fn-nntp-host-observation-is-an-observation
  (implies (and (<= (nfix monotonic-ms) *fn-clock-max*)
                (<= (fn-nntp-unix-dtn-ms unix-ms) *fn-clock-max*)
                (<= (nfix error-ms) *fn-clock-max*))
           (fn-clock-observationp
            (fn-nntp-host-observation monotonic-ms unix-ms error-ms has-wall))))

; -----------------------------------------------------------------------------
; Zero-padded decimal rendering
;
; A rendered digit is a table lookup, not an arithmetic expression, so every
; octet DATE emits is a response octet by cases and needs no arithmetic book.

(defun fn-nntp-digit-octet (n)
  (declare (xargs :guard t))
  (cond ((equal n 0) 48) ((equal n 1) 49) ((equal n 2) 50) ((equal n 3) 51)
        ((equal n 4) 52) ((equal n 5) 53) ((equal n 6) 54) ((equal n 7) 55)
        ((equal n 8) 56) ((equal n 9) 57) (t 48)))

(defun fn-nntp-pad2 (n)
  (declare (xargs :guard t))
  (list (fn-nntp-digit-octet (fn-nntp-mod (fn-nntp-div (nfix n) 10) 10))
        (fn-nntp-digit-octet (fn-nntp-mod (nfix n) 10))))

(defun fn-nntp-pad4 (n)
  (declare (xargs :guard t))
  (append (fn-nntp-pad2 (fn-nntp-div (nfix n) 100))
          (fn-nntp-pad2 (fn-nntp-mod (nfix n) 100))))

; -----------------------------------------------------------------------------
; DATE (RFC 3977 section 7.1)

(defun fn-nntp-date-octets (civil)
  (fn-nntp-append-pieces
   (list (fn-nntp-string-octets "111 ")
         (fn-nntp-pad4 (fn-nntp-civil-year civil))
         (fn-nntp-pad2 (fn-nntp-civil-month civil))
         (fn-nntp-pad2 (fn-nntp-civil-day civil))
         (fn-nntp-pad2 (fn-nntp-civil-hour civil))
         (fn-nntp-pad2 (fn-nntp-civil-minute civil))
         (fn-nntp-pad2 (fn-nntp-civil-second civil)))))

; RFC 3977 section 7.1 lists only the 111 response, so a reader with no wall
; reading cannot answer it.  Section 3.2.1 assigns 503 to a recognized command
; whose required information the server does not hold; that is the refusal
; here, and it is stated rather than replaced by a fabricated timestamp.
(defun fn-nntp-date-response (session env)
  (let ((obs (fn-nntp-env-observation env)))
    (if (not (fn-clock-observationp obs))
        (fn-nntp-single session "503 no clock observation supplied")
      (if (not (fn-clock-has-wall obs))
          (fn-nntp-single session "503 server holds no wall clock reading")
        (let ((civil (fn-nntp-dtn-civil (fn-clock-wall obs))))
          (if (and (natp (fn-nntp-civil-year civil))
                   (<= (fn-nntp-civil-year civil) *fn-nntp-max-rendered-year*))
              (fn-nntp-make-result
               session
               (list (fn-nntp-reply-effect
                      (fn-nntp-crlf (fn-nntp-date-octets civil)))))
            (fn-nntp-single
             session "503 clock reading outside the representable range")))))))

; -----------------------------------------------------------------------------
; NEWGROUPS (RFC 3977 section 7.3)

(defun fn-ng-take (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (zp n) (not (consp xs)))
      nil
    (cons (fn-ag-car xs) (fn-ng-take (- n 1) (fn-ag-cdr xs)))))

(defun fn-ng-nthcdr (n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (zp n) (not (consp xs)))
      xs
    (fn-ng-nthcdr (- n 1) (fn-ag-cdr xs))))

; RFC 3977 section 7.3.2's field ranges.  The seconds field admits 60 for a
; leap second; the DTN day count that carries it does not, so a requested
; 60 second reads as the following instant.
(defun fn-nntp-ymd-okp (year month day)
  (declare (xargs :guard t))
  (and (integerp year) (<= 1900 year) (<= year *fn-nntp-max-rendered-year*)
       (integerp month) (<= 1 month) (<= month 12)
       (integerp day) (<= 1 day) (<= day 31)))

(defun fn-nntp-hms-okp (hour minute second)
  (declare (xargs :guard t))
  (and (integerp hour) (<= 0 hour) (<= hour 23)
       (integerp minute) (<= 0 minute) (<= minute 59)
       (integerp second) (<= 0 second) (<= second 60)))

; The declarative statement of the two accepted date forms, used as the
; independent side of fn-nntp-newgroups-date-accepts-exactly.
(defun fn-nntp-four-digit-date-formp (token)
  (declare (xargs :guard t))
  (and (fn-nntp-decimal-tokenp token)
       (equal (len token) 8)
       (fn-nntp-ymd-okp (fn-nntp-decimal-value (fn-ng-take 4 token))
                        (fn-nntp-decimal-value
                         (fn-ng-take 2 (fn-ng-nthcdr 4 token)))
                        (fn-nntp-decimal-value (fn-ng-nthcdr 6 token)))))

(defun fn-nntp-two-digit-date-formp (token)
  (declare (xargs :guard t))
  (and (fn-nntp-decimal-tokenp token)
       (equal (len token) 6)))

; The RFC's century rule: with a two-digit year, take the current century when
; yy is at most the current two-digit year, and the previous century
; otherwise.  `current-year' is the four-digit year of the supplied clock
; observation; 0 means the host gave no wall reading, and the two-digit form
; is then refused rather than resolved against a guess.
(defun fn-nntp-apply-century (yy current-year)
  (declare (xargs :guard t))
  (let ((century (* 100 (fn-nntp-div (nfix current-year) 100)))
        (current-yy (fn-nntp-mod (nfix current-year) 100)))
    (if (<= (nfix yy) current-yy)
        (+ century (nfix yy))
      (+ (- century 100) (nfix yy)))))

(defun fn-nntp-newgroups-date-parse (token current-year)
  (declare (xargs :guard t))
  (if (not (fn-nntp-decimal-tokenp token))
      (list :error :syntax)
    (if (equal (len token) 8)
        (let ((year (fn-nntp-decimal-value (fn-ng-take 4 token)))
              (month (fn-nntp-decimal-value
                      (fn-ng-take 2 (fn-ng-nthcdr 4 token))))
              (day (fn-nntp-decimal-value (fn-ng-nthcdr 6 token))))
          (if (fn-nntp-ymd-okp year month day)
              (list :ok year month day)
            (list :error :range)))
      (if (equal (len token) 6)
          (if (not (posp current-year))
              (list :error :no-century)
            (let ((year (fn-nntp-apply-century
                         (fn-nntp-decimal-value (fn-ng-take 2 token))
                         current-year))
                  (month (fn-nntp-decimal-value
                          (fn-ng-take 2 (fn-ng-nthcdr 2 token))))
                  (day (fn-nntp-decimal-value (fn-ng-nthcdr 4 token))))
              (if (fn-nntp-ymd-okp year month day)
                  (list :ok year month day)
                (list :error :range))))
        (list :error :syntax)))))

(defun fn-nntp-newgroups-time-parse (token)
  (declare (xargs :guard t))
  (if (not (and (fn-nntp-decimal-tokenp token) (equal (len token) 6)))
      (list :error :syntax)
    (let ((hour (fn-nntp-decimal-value (fn-ng-take 2 token)))
          (minute (fn-nntp-decimal-value (fn-ng-take 2 (fn-ng-nthcdr 2 token))))
          (second (fn-nntp-decimal-value (fn-ng-nthcdr 4 token))))
      (if (fn-nntp-hms-okp hour minute second)
          (list :ok hour minute second)
        (list :error :range)))))

(defun fn-nntp-parse-okp (x)
  (mbe :logic (equal (car x) :ok) :exec (equal (fn-ag-car x) :ok)))
(defun fn-nntp-parse-1 (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-parse-2 (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nntp-parse-3 (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

; The current four-digit year of a clock observation, or 0 when the host holds
; no wall reading.
(defun fn-nntp-observed-year (obs)
  (declare (xargs :guard t))
  (if (and (fn-clock-observationp obs) (fn-clock-has-wall obs))
      (let ((year (fn-nntp-civil-year (fn-nntp-dtn-civil (fn-clock-wall obs)))))
        (if (posp year) year 0))
    0))

(defun fn-nntp-facts-since (threshold facts)
  (if (consp facts)
      (if (and (fn-nntp-group-factp (car facts))
               (<= threshold (fn-nntp-fact-created (car facts))))
          (cons (car facts) (fn-nntp-facts-since threshold (cdr facts)))
        (fn-nntp-facts-since threshold (cdr facts)))
    nil))

(defun fn-nntp-fact-names (facts)
  (if (consp facts)
      (cons (fn-nntp-fact-name (car facts)) (fn-nntp-fact-names (cdr facts)))
    nil))

(defun fn-nntp-newgroups-response (session archive env args)
  ; NEWGROUPS date time [GMT].  fn's local time zone is UTC, so the GMT token
  ; changes nothing but is accepted exactly where the grammar allows it.
  (if (not (or (and (consp args) (consp (cdr args)) (null (cdr (cdr args))))
               (and (consp args) (consp (cdr args)) (consp (cdr (cdr args)))
                    (null (cdr (cdr (cdr args))))
                    (fn-nntp-keywordp (car (cdr (cdr args))) "GMT"))))
      (fn-nntp-single session "501 syntax error")
    (let* ((obs (fn-nntp-env-observation env))
           (date (fn-nntp-newgroups-date-parse
                  (car args) (fn-nntp-observed-year obs)))
           (time (fn-nntp-newgroups-time-parse (car (cdr args)))))
      (if (and (not (fn-nntp-parse-okp date))
               (equal (car (cdr date)) :no-century))
          (fn-nntp-single
           session "503 two-digit year needs a wall clock reading")
        (if (or (not (fn-nntp-parse-okp date)) (not (fn-nntp-parse-okp time)))
            (fn-nntp-single session "501 syntax error")
          (let ((threshold (fn-nntp-civil-dtn-ms
                            (fn-nntp-parse-1 date) (fn-nntp-parse-2 date)
                            (fn-nntp-parse-3 date) (fn-nntp-parse-1 time)
                            (fn-nntp-parse-2 time) (fn-nntp-parse-3 time))))
            (fn-nntp-multi
             session "231 list of new newsgroups follows"
             (fn-nntp-active-lines
              archive
              (fn-nntp-fact-names
               (fn-nntp-facts-since threshold
                                    (fn-nntp-env-facts env)))))))))))

; -----------------------------------------------------------------------------
; Overview projection (RFC 3977 sections 8.3 and 8.4, RFC 5536 section 3)
;
; Every overview field comes from the proved article view in books/article.lisp
; through books/article-fields.lisp's lookup; this book does not parse a second
; time or reconstruct a header.  The section 8.3.2 transformation is applied
; once, by fn-nov-scrub: CRLF pairs are removed (undoing folding and the
; terminating CRLF) and each remaining TAB, NUL, LF or CR becomes a single
; space.  The resulting field therefore carries none of TAB, CR, LF or NUL, so
; it can neither split a line nor invent a ninth field.

(defconst *fn-nov-subject-name* '(115 117 98 106 101 99 116))
(defconst *fn-nov-from-name* '(102 114 111 109))
(defconst *fn-nov-date-name* '(100 97 116 101))
(defconst *fn-nov-message-id-name* '(109 101 115 115 97 103 101 45 105 100))
(defconst *fn-nov-references-name* '(114 101 102 101 114 101 110 99 101 115))

(defun fn-nov-scrub-byte (byte)
  (declare (xargs :guard t))
  (if (and (integerp byte) (<= 1 byte) (<= byte 255)
           (not (equal byte 9)) (not (equal byte 13)) (not (equal byte 10)))
      byte
    32))

(defun fn-nov-scrub (bytes)
  (declare (xargs :guard t :measure (acl2-count bytes)))
  (if (consp bytes)
      (if (and (equal (fn-ag-car bytes) 13)
               (consp (fn-ag-cdr bytes))
               (equal (fn-ag-car (fn-ag-cdr bytes)) 10))
          (fn-nov-scrub (fn-ag-cdr (fn-ag-cdr bytes)))
        (cons (fn-nov-scrub-byte (fn-ag-car bytes))
              (fn-nov-scrub (fn-ag-cdr bytes))))
    nil))

; RFC 3977 section 8.3.2: the field is the header content, that is, the header
; name and its following colon and space removed.  The parsed view's unfolded
; value begins immediately after the colon.
(defun fn-nov-value-content (value)
  (declare (xargs :guard t))
  (if (and (consp value) (equal (fn-ag-car value) 32))
      (fn-ag-cdr value)
    value))

(defun fn-nov-header-content (view name)
  (declare (xargs :guard (fn-article-syntax-p view)))
  (let ((fields (fn-article-get-headers view name)))
    (if (consp fields)
        (fn-nov-scrub (fn-nov-value-content
                       (fn-article-field-unfolded-value (car fields))))
      nil)))

; The :lines metadata item counts the body lines of the exact retained octets;
; :bytes counts those octets themselves.  Neither is stored beside the article
; and neither is recomputed from a normalized copy.
(defun fn-nov-body-line-count (payload)
  (declare (xargs :guard t))
  (let ((split (fn-nntp-split-article payload)))
    (if (fn-nntp-split-okp split)
        (let ((lines (fn-nntp-crlf-lines (fn-nntp-split-body split))))
          (if (equal (car lines) :ok) (fn-ng-len (car (cdr lines))) 0))
      0)))

(defun fn-nov-overview (article)
  ; (:ok subject from date message-id references bytes lines) | (:error)
  (declare (xargs :guard t))
  (let* ((payload (fn-article-payload article))
         (parsed (fn-article-parse payload)))
    (if (not (and (true-listp parsed)
                  (fn-article-result-okp parsed)
                  (fn-article-syntax-p (fn-article-result-article parsed))))
        (list :error)
      (let ((view (fn-article-result-article parsed)))
        (list :ok
              (fn-nov-header-content view *fn-nov-subject-name*)
              (fn-nov-header-content view *fn-nov-from-name*)
              (fn-nov-header-content view *fn-nov-date-name*)
              (fn-nov-header-content view *fn-nov-message-id-name*)
              (fn-nov-header-content view *fn-nov-references-name*)
              (fn-ng-len payload)
              (fn-nov-body-line-count payload))))))

(defun fn-nov-okp (x)
  (mbe :logic (equal (car x) :ok) :exec (equal (fn-ag-car x) :ok)))
(defun fn-nov-subject (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nov-from (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nov-date (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-nov-msgid (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-nov-references (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr x))))))))
(defun fn-nov-bytes (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr (fn-ag-cdr x)))))))))
(defun fn-nov-lines (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))) 

; The eight mandatory fields of RFC 3977 section 8.3.2, TAB separated, in
; order.  No ninth field is emitted: this profile holds no Xref or other
; overview metadata, and section 8.3.2 makes subsequent fields optional.
(defun fn-nov-line (number over)
  (fn-nntp-append-pieces
   (list (fn-nntp-decimal-field number) '(9)
         (fn-nov-subject over) '(9)
         (fn-nov-from over) '(9)
         (fn-nov-date over) '(9)
         (fn-nov-msgid over) '(9)
         (fn-nov-references over) '(9)
         (fn-nntp-decimal-field (fn-nov-bytes over)) '(9)
         (fn-nntp-decimal-field (fn-nov-lines over)))))

(defun fn-nov-lines-for-numbers (group numbers articles)
  ; An article whose retained octets cannot be parsed produces no line: RFC
  ; 3977 section 8.3.2 says the server SHOULD NOT produce output for articles
  ; it cannot report, and an unprojectable article degrades only itself.
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-nntp-available-article group number articles))
             (over (if (consp article) (fn-nov-overview article) (list :error))))
        (if (fn-nov-okp over)
            (cons (fn-nov-line number over)
                  (fn-nov-lines-for-numbers group (cdr numbers) articles))
          (fn-nov-lines-for-numbers group (cdr numbers) articles)))
    nil))

(defconst *fn-nov-fmt-lines*
  '("Subject:" "From:" "Date:" "Message-ID:" "References:" ":bytes" ":lines"))

(defun fn-nov-fmt-octet-lines (texts)
  (if (consp texts)
      (cons (fn-nntp-string-octets (car texts))
            (fn-nov-fmt-octet-lines (cdr texts)))
    nil))

(defun fn-nntp-list-overview-fmt (session)
  (fn-nntp-multi-octets
   session (fn-nntp-string-octets "215 order of fields in overview database")
   (fn-nov-fmt-octet-lines *fn-nov-fmt-lines*)))

; -----------------------------------------------------------------------------
; OVER (RFC 3977 section 8.3)

(defun fn-nntp-over-current (session archive)
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((article (fn-nntp-available-article
                        group current (fn-state-articles archive))))
          (if (not (consp article))
              (fn-nntp-single session "420 no current article")
            (let ((over (fn-nov-overview article)))
              (if (fn-nov-okp over)
                  (fn-nntp-multi session "224 overview information follows"
                                 (list (fn-nov-line current over)))
                (fn-nntp-single
                 session "503 stored article framing unavailable")))))))))

(defun fn-nntp-over-range (session archive token)
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((numbers (fn-nntp-group-range-numbers
                       group (fn-nntp-range-low range)
                       (fn-nntp-range-high range) (fn-state-articles archive)))
             (lines (fn-nov-lines-for-numbers group numbers
                                              (fn-state-articles archive))))
        (if (consp lines)
            (fn-nntp-multi session "224 overview information follows" lines)
          (fn-nntp-single session "423 no articles in that range"))))))

(defun fn-nntp-over-msgid (session archive token)
  ; RFC 3977 section 8.3.2: the number is zero for the message-id form, and
  ; this form never alters the selected group or the current article.
  (let ((article (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive))))
    (if (not (consp article))
        (fn-nntp-single session "430 no article with that message-id")
      (let ((over (fn-nov-overview article)))
        (if (fn-nov-okp over)
            (fn-nntp-multi session "224 overview information follows"
                           (list (fn-nov-line 0 over)))
          (fn-nntp-single session "503 stored article framing unavailable"))))))

(defun fn-nntp-over-response (session archive args)
  (mbe :logic
       (if (null args)
           (fn-nntp-over-current session archive)
         (if (null (cdr args))
             (let ((token (car args)))
               (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                   (fn-nntp-over-range session archive token)
                 (if (fn-nntp-message-id-tokenp token)
                     (fn-nntp-over-msgid session archive token)
                   (fn-nntp-single session "501 syntax error"))))
           (fn-nntp-single session "501 syntax error")))
       :exec
       (if (null args)
           (fn-nntp-over-current session archive)
         (if (null (fn-ag-cdr args))
             (let ((token (fn-ag-car args)))
               (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                   (fn-nntp-over-range session archive token)
                 (if (fn-nntp-message-id-tokenp token)
                     (fn-nntp-over-msgid session archive token)
                   (fn-nntp-single session "501 syntax error"))))
           (fn-nntp-single session "501 syntax error")))))

; -----------------------------------------------------------------------------
; MODE READER (RFC 3977 section 5.3)
;
; This reader is not mode-switching (RFC 3977 section 3.4.2), so it never
; advertises MODE-READER.  Section 5.3.2's non-mode-switching rules then fix
; both branches exactly: advertising READER means a 200 or 201 response with
; the greeting's meaning and no state change whatsoever; not advertising it
; means 502 followed by an immediate close.  One constant decides both this
; and the capability list, so the two can never disagree.

(defconst *fn-nntp-advertise-readerp* t)

(defun fn-nntp-mode-response (session args)
  (if (and (consp args) (null (cdr args))
           (fn-nntp-keywordp (car args) "READER"))
      (if *fn-nntp-advertise-readerp*
          ; Posting is prohibited on this profile, so the greeting's code is
          ; 201 and section 5.3.2 requires the same meaning here.
          (fn-nntp-single session "201 posting prohibited")
        (fn-nntp-make-result
         session
         (list (fn-nntp-reply-effect
                (fn-nntp-crlf
                 (fn-nntp-string-octets
                  "502 reading service permanently unavailable")))
               (fn-nntp-close-effect))))
    (fn-nntp-single session "501 syntax error")))

; The dispatcher is split by whether a command reads the archive at all.  No
; archive content can deny CAPABILITIES, HELP, QUIT, an unrecognized command,
; or a syntax error: see fn-nntp-archive-free-step-ignores-the-archive in
; books/nntp-invariants.lisp.
(defun fn-nntp-archive-keywordp (keyword)
  (or (fn-nntp-keywordp keyword "GROUP")
      (fn-nntp-keywordp keyword "LISTGROUP")
      (fn-nntp-keywordp keyword "LIST")
      (fn-nntp-keywordp keyword "NEXT")
      (fn-nntp-keywordp keyword "LAST")
      (fn-nntp-keywordp keyword "ARTICLE")
      (fn-nntp-keywordp keyword "HEAD")
      (fn-nntp-keywordp keyword "BODY")
      (fn-nntp-keywordp keyword "STAT")
      (fn-nntp-keywordp keyword "OVER")
      (fn-nntp-keywordp keyword "NEWGROUPS")))

(defun fn-nntp-session-command (session env keyword args)
  (cond
   ((fn-nntp-keywordp keyword "CAPABILITIES")
    (if (or (null args)
            (and (consp args) (null (cdr args))
                 (fn-nntp-keyword-tokenp (car args))))
        (fn-nntp-capabilities session)
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "HELP")
    (if (null args) (fn-nntp-help session)
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "QUIT")
    (if (null args)
        (fn-nntp-make-result (fn-nntp-make-session nil
                                                   (fn-nntp-session-group session)
                                                   (fn-nntp-session-current session)
                                                   (fn-nntp-session-projected session))
                             (list (fn-nntp-reply-effect
                                    (fn-nntp-crlf (fn-nntp-string-octets "205 closing connection")))
                                   (fn-nntp-close-effect)))
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "MODE") (fn-nntp-mode-response session args))
   ((fn-nntp-keywordp keyword "DATE")
    (if (null args) (fn-nntp-date-response session env)
      (fn-nntp-single session "501 syntax error")))
   (t (fn-nntp-single session "500 command not recognized"))))

(defun fn-nntp-archive-command (session archive env keyword args)
  (cond
   ((fn-nntp-keywordp keyword "GROUP")
    (if (and (consp args) (null (cdr args)) (fn-nntp-printable-tokenp (car args)))
        (fn-nntp-group-result session archive (fn-nntp-token-string (car args)))
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "LISTGROUP")
    (fn-nntp-listgroup-command session archive args))
   ((fn-nntp-keywordp keyword "LIST") (fn-nntp-list-response session archive args))
   ((fn-nntp-keywordp keyword "NEXT")
    (if (null args) (fn-nntp-next-or-last session archive :next)
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "LAST")
    (if (null args) (fn-nntp-next-or-last session archive :last)
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "ARTICLE") (fn-nntp-retrieval session archive :article args))
   ((fn-nntp-keywordp keyword "HEAD") (fn-nntp-retrieval session archive :head args))
   ((fn-nntp-keywordp keyword "BODY") (fn-nntp-retrieval session archive :body args))
   ((fn-nntp-keywordp keyword "OVER") (fn-nntp-over-response session archive args))
   ((fn-nntp-keywordp keyword "NEWGROUPS")
    (fn-nntp-newgroups-response session archive env args))
   (t (fn-nntp-retrieval session archive :stat args))))

(defun fn-nntp-command (session archive env tokens)
  (let ((keyword (mbe :logic (car tokens) :exec (fn-ag-car tokens)))
        (args (mbe :logic (cdr tokens) :exec (fn-ag-cdr tokens))))
    (if (not (fn-nntp-keyword-tokenp keyword))
        (fn-nntp-single session "501 syntax error")
      (if (not (fn-nntp-archive-keywordp keyword))
          (fn-nntp-session-command session env keyword args)
        ; RFC 3977 section 3.2.1 assigns 503 to a recognized command the server
        ; cannot carry out because it does not hold the required information.
        (if (fn-nntp-session-projected session)
            (fn-nntp-archive-command session archive env keyword args)
          (fn-nntp-single session "503 archive projection unavailable"))))))

; A single command event is the integration boundary.  Other wire events are
; rejected as syntax, and a closed session produces no further effects.  The
; archive projection is not revalidated here: fn-nntp-open-session decided it
; once and the session carries the verdict.
(defun fn-nntp-step (session archive env wire-event)
  (if (or (not (fn-nntp-sessionp session))
          (not (equal (fn-nntp-session-openp session) t)))
      (fn-nntp-make-result session nil)
    (if (and (consp wire-event)
             (equal (car wire-event) :command)
             (consp (cdr wire-event))
             (null (cdr (cdr wire-event))))
        (let ((line (car (cdr wire-event))))
          (if (not (fn-nntp-command-inputp line))
              (fn-nntp-single session "501 syntax error")
            (let ((tokens (fn-nntp-tokenize line)))
              (if (and (consp tokens)
                       (fn-nntp-command-arguments-at-mostp tokens))
                  (fn-nntp-command session archive env tokens)
                (fn-nntp-single session "501 syntax error")))))
      (fn-nntp-single session "501 syntax error"))))


; The guard for the overview field lookup: a field returned by the proved
; lookup view of a syntactically valid parsed article is a field.
(defthm fn-nov-get-headers-car-is-a-field
  (implies (and (fn-article-syntax-p view)
                (consp (fn-article-get-headers view name)))
           (fn-article-fieldp (car (fn-article-get-headers view name))))
  :hints (("Goal" :in-theory (enable fn-article-get-headers))))

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
(verify-guards fn-nntp-session-openp)
(verify-guards fn-nntp-session-group)
(verify-guards fn-nntp-session-current)
(verify-guards fn-nntp-session-projected)
(verify-guards fn-nntp-make-session)
(verify-guards fn-nntp-sessionp)
(verify-guards fn-nntp-set-cursor)
(verify-guards fn-nntp-result-session)
(verify-guards fn-nntp-result-effects)
(verify-guards fn-nntp-make-result)
(verify-guards fn-nntp-reply-effect)
(verify-guards fn-nntp-close-effect)
(verify-guards fn-nntp-crlf)
(verify-guards fn-nntp-stuff-lines)
(verify-guards fn-nntp-single)
(verify-guards fn-nntp-multi)
(verify-guards fn-nntp-multi-octets)
(verify-guards fn-nntp-append-pieces)
(verify-guards fn-nntp-crlf-lines-aux)
(verify-guards fn-nntp-crlf-lines)
(verify-guards fn-nntp-split-article-aux)
(verify-guards fn-nntp-split-article)
(verify-guards fn-nntp-split-okp)
(verify-guards fn-nntp-split-head)
(verify-guards fn-nntp-split-body)
(verify-guards fn-nntp-article-section)
(verify-guards fn-nntp-safe-group-namep)
(verify-guards fn-nntp-safe-group-listp)
(verify-guards fn-nntp-nexts-boundedp)
(verify-guards fn-nntp-article-idp)
(verify-guards fn-nntp-article-framedp)
(verify-guards fn-nntp-projection-articlep)
(verify-guards fn-nntp-projectionp)
(verify-guards fn-nntp-open-session)
(verify-guards fn-nntp-membership-number)
(verify-guards fn-nntp-article-number)
(verify-guards fn-nntp-find-group-number)
(verify-guards fn-nntp-available-article)
(verify-guards fn-nntp-insert-number)
(verify-guards fn-nntp-orderedp)
(verify-guards fn-nntp-group-count)
(verify-guards fn-nntp-group-low)
(verify-guards fn-nntp-group-high)
(verify-guards fn-nntp-group-next-number)
(verify-guards fn-nntp-group-last-number)
(verify-guards fn-nntp-group-range-numbers)
(verify-guards fn-nntp-number-lines)
(verify-guards fn-nntp-group-summary)
(verify-guards fn-nntp-summary-count)
(verify-guards fn-nntp-summary-low)
(verify-guards fn-nntp-summary-high)
(verify-guards fn-nntp-group-initial)
(verify-guards fn-nntp-group-result)
(verify-guards fn-nntp-listgroup-initial)
(verify-guards fn-nntp-listgroup-result)
(verify-guards fn-nntp-listgroup-command)
(verify-guards fn-nntp-retrieval-initial)
(verify-guards fn-nntp-article-response)
(verify-guards fn-nntp-current-retrieval)
(verify-guards fn-nntp-number-retrieval)
(verify-guards fn-nntp-msgid-retrieval)
(verify-guards fn-nntp-retrieval)
(verify-guards fn-nntp-next-or-last)
(verify-guards fn-nntp-active-line)
(verify-guards fn-nntp-active-lines)
(verify-guards fn-nntp-newsgroup-lines)
(verify-guards fn-nntp-group-matches-parsed-wildmatp)
(verify-guards fn-nntp-filter-groups-by-wildmat)
(verify-guards fn-nntp-list-active)
(verify-guards fn-nntp-list-newsgroups)
(verify-guards fn-nntp-list-filtered-response)
(verify-guards fn-nntp-list-active-or-newsgroups)
(verify-guards fn-nntp-list-wildmat-argumentp)
(verify-guards fn-nntp-list-unmaintained-response)
(verify-guards fn-nntp-list-response)
(verify-guards fn-nntp-group-fact)
(verify-guards fn-nntp-fact-name)
(verify-guards fn-nntp-fact-created)
(verify-guards fn-nntp-fact-observation)
(verify-guards fn-nntp-group-factp)
(verify-guards fn-nntp-group-fact-listp)
(verify-guards fn-nntp-env)
(verify-guards fn-nntp-env-observation)
(verify-guards fn-nntp-env-facts)
(verify-guards fn-nntp-envp)
(verify-guards fn-nntp-blind-env)
(verify-guards fn-nntp-unix-dtn-ms)
(verify-guards fn-nntp-host-observation)
(verify-guards fn-nntp-div)
(verify-guards fn-nntp-mod)
(verify-guards fn-nntp-civil-from-days)
(verify-guards fn-nntp-days-from-civil)
(verify-guards fn-nntp-dtn-civil)
(verify-guards fn-nntp-civil-year)
(verify-guards fn-nntp-civil-month)
(verify-guards fn-nntp-civil-day)
(verify-guards fn-nntp-civil-hour)
(verify-guards fn-nntp-civil-minute)
(verify-guards fn-nntp-civil-second)
(verify-guards fn-nntp-civil-dtn-ms)
(verify-guards fn-nntp-digit-octet)
(verify-guards fn-nntp-pad2)
(verify-guards fn-nntp-pad4)
(verify-guards fn-nntp-date-octets)
(verify-guards fn-nntp-date-response)
(verify-guards fn-ng-take)
(verify-guards fn-ng-nthcdr)
(verify-guards fn-nntp-ymd-okp)
(verify-guards fn-nntp-hms-okp)
(verify-guards fn-nntp-four-digit-date-formp)
(verify-guards fn-nntp-two-digit-date-formp)
(verify-guards fn-nntp-apply-century)
(verify-guards fn-nntp-newgroups-date-parse)
(verify-guards fn-nntp-newgroups-time-parse)
(verify-guards fn-nntp-parse-okp)
(verify-guards fn-nntp-parse-1)
(verify-guards fn-nntp-parse-2)
(verify-guards fn-nntp-parse-3)
(verify-guards fn-nntp-observed-year)
(verify-guards fn-nntp-facts-since)
(verify-guards fn-nntp-fact-names)
(verify-guards fn-nntp-newgroups-response)
(verify-guards fn-nov-scrub-byte)
(verify-guards fn-nov-scrub)
(verify-guards fn-nov-value-content)
(verify-guards fn-nov-header-content)
(verify-guards fn-nov-body-line-count)
(verify-guards fn-nov-overview)
(verify-guards fn-nov-okp)
(verify-guards fn-nov-subject)
(verify-guards fn-nov-from)
(verify-guards fn-nov-date)
(verify-guards fn-nov-msgid)
(verify-guards fn-nov-references)
(verify-guards fn-nov-bytes)
(verify-guards fn-nov-lines)
(verify-guards fn-nov-line)
(verify-guards fn-nov-lines-for-numbers)
(verify-guards fn-nov-fmt-octet-lines)
(verify-guards fn-nntp-list-overview-fmt)
(verify-guards fn-nntp-over-current)
(verify-guards fn-nntp-over-range)
(verify-guards fn-nntp-over-msgid)
(verify-guards fn-nntp-over-response)
(verify-guards fn-nntp-mode-response)
(verify-guards fn-nntp-capability-lines)
(verify-guards fn-nntp-unadvertised-capability-lines)
(verify-guards fn-nntp-capabilities)
(verify-guards fn-nntp-help)
(verify-guards fn-nntp-archive-keywordp)
(verify-guards fn-nntp-session-command)
(verify-guards fn-nntp-archive-command)
(verify-guards fn-nntp-command)
(verify-guards fn-nntp-step)
