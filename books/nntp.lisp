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
(include-book "wire")

; -----------------------------------------------------------------------------
; Octet and command syntax helpers

(defun fn-nntp-space-or-tabp (byte)
  (or (equal byte 32) (equal byte 9)))

(defun fn-nntp-command-bytep (byte)
  (or (fn-nntp-space-or-tabp byte)
      (and (integerp byte) (<= 33 byte) (<= byte 126))))

(defun fn-nntp-command-linep (line)
  (if (consp line)
      (and (fn-nntp-command-bytep (car line))
           (fn-nntp-command-linep (cdr line)))
    (null line)))

(defun fn-nntp-last (xs)
  (if (consp (cdr xs))
      (fn-nntp-last (cdr xs))
    (car xs)))

(defun fn-nntp-tokenize-aux (xs word-rev words-rev)
  (if (consp xs)
      (if (fn-nntp-space-or-tabp (car xs))
          (if (consp word-rev)
              (fn-nntp-tokenize-aux (cdr xs) nil
                                    (cons (reverse word-rev) words-rev))
            (fn-nntp-tokenize-aux (cdr xs) nil words-rev))
        (fn-nntp-tokenize-aux (cdr xs) (cons (car xs) word-rev) words-rev))
    (if (consp word-rev)
        (reverse (cons (reverse word-rev) words-rev))
      nil)))

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
  (if (consp chars)
      (cons (char-code (car chars))
            (fn-nntp-string-octets-aux (cdr chars)))
    nil))

(defun fn-nntp-string-octets (text)
  (if (stringp text)
      (fn-nntp-string-octets-aux (coerce text 'list))
    nil))

(defun fn-nntp-octets-chars (bytes)
  (if (consp bytes)
      (cons (code-char (car bytes)) (fn-nntp-octets-chars (cdr bytes)))
    nil))

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
  (and (consp token)
       (fn-nntp-keyword-first-bytep (car token))
       (fn-nntp-keyword-tailp (cdr token))))

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
  (if (consp token)
      (fn-nntp-decimal-value-aux
       (cdr token) (+ (* 10 accumulator) (- (car token) 48)))
    accumulator))

(defun fn-nntp-decimal-value (token)
  (fn-nntp-decimal-value-aux token 0))

(defun fn-nntp-number-tokenp (token)
  (and (consp token)
       (<= (len token) 16)
       (fn-nntp-decimal-tokenp token)
       (let ((number (fn-nntp-decimal-value token)))
         (and (<= 1 number) (<= number 2147483647)))))

; RFC 3977 section 9.2 defines range as article-number ["-"
; [article-number]].  The parser returns (:ok low high), where an open end is
; represented by the RFC's maximum article number; a reversed closed range is
; syntactically valid and filters to no articles.
(defun fn-nntp-range-parse-aux (token prefix-rev)
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
        (list :error)))))

(defun fn-nntp-parse-range (token)
  (if (fn-nntp-printable-tokenp token)
      (fn-nntp-range-parse-aux token nil)
    (list :error)))

(defun fn-nntp-range-okp (range) (equal (car range) :ok))
(defun fn-nntp-range-low (range) (car (cdr range)))
(defun fn-nntp-range-high (range) (car (cdr (cdr range))))

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

; -----------------------------------------------------------------------------
; Session, effects, and exact article projection

; Session fields are (openp selected-group current-number).  NIL selected-group
; and NIL current-number are the RFC's invalid values.
(defun fn-nntp-session-openp (x) (car x))
(defun fn-nntp-session-group (x) (car (cdr x)))
(defun fn-nntp-session-current (x) (car (cdr (cdr x))))

(defun fn-nntp-make-session (openp group current)
  (list openp group current))

(defun fn-nntp-sessionp (x)
  (and (true-listp x)
       (equal (len x) 3)
       (or (equal (fn-nntp-session-openp x) t)
           (null (fn-nntp-session-openp x)))
       (or (stringp (fn-nntp-session-group x))
           (null (fn-nntp-session-group x)))
       (or (posp (fn-nntp-session-current x))
           (null (fn-nntp-session-current x)))))

(defun fn-nntp-initial-session ()
  (fn-nntp-make-session t nil nil))

(defun fn-nntp-set-cursor (session group number)
  (fn-nntp-make-session (fn-nntp-session-openp session) group number))

(defthm fn-nntp-set-cursor-preserves-group
  (equal (fn-nntp-session-group (fn-nntp-set-cursor session group number))
         group))

(defun fn-nntp-result-session (x) (car x))
(defun fn-nntp-result-effects (x) (cdr x))
(defun fn-nntp-make-result (session effects) (cons session effects))
(defun fn-nntp-reply-effect (octets) (list :reply octets))
(defun fn-nntp-close-effect () (list :close))

(defun fn-nntp-crlf (line) (append line '(13 10)))

(defun fn-nntp-stuff-lines (lines)
  (if (consp lines)
      (append (fn-nntp-crlf (fn-wire-stuff-line (car lines)))
              (fn-nntp-stuff-lines (cdr lines)))
    nil))

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
  (if (consp pieces)
      (append (car pieces) (fn-nntp-append-pieces (cdr pieces)))
    nil))

; Return (:ok lines) only when every stored line is complete CRLF-framed.
(defun fn-nntp-crlf-lines-aux (bytes line-rev lines-rev)
  (declare (xargs :measure (acl2-count bytes)))
  (if (consp bytes)
      (if (equal (car bytes) 13)
          (if (and (consp (cdr bytes)) (equal (car (cdr bytes)) 10))
              (fn-nntp-crlf-lines-aux (cdr (cdr bytes)) nil
                                      (cons (reverse line-rev) lines-rev))
            (list :error))
        (if (equal (car bytes) 10)
            (list :error)
          (fn-nntp-crlf-lines-aux (cdr bytes) (cons (car bytes) line-rev)
                                  lines-rev)))
    (if (consp line-rev)
        (list :error)
      (list :ok (reverse lines-rev)))))

(defun fn-nntp-crlf-lines (bytes)
  (if (fn-octet-listp bytes)
      (fn-nntp-crlf-lines-aux bytes nil nil)
    (list :error)))

; Split a stored article at its first CRLFCRLF.  The header fragment includes
; its final CRLF; the separator's second CRLF is not part of HEAD or BODY.
(defun fn-nntp-split-article-aux (bytes prefix-rev)
  (declare (xargs :measure (acl2-count bytes)))
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
      (list :error))))

(defun fn-nntp-split-article (bytes)
  (if (fn-octet-listp bytes)
      (fn-nntp-split-article-aux bytes nil)
    (list :error)))

(defun fn-nntp-split-okp (x) (equal (car x) :ok))
(defun fn-nntp-split-head (x) (car (cdr x)))
(defun fn-nntp-split-body (x) (car (cdr (cdr x))))

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
(defun fn-nntp-safe-string-tokenp (text)
  (and (stringp text)
       (fn-nntp-printable-tokenp (fn-nntp-string-octets text))))

(defun fn-nntp-safe-string-listp (texts)
  (if (consp texts)
      (and (fn-nntp-safe-string-tokenp (car texts))
           (fn-nntp-safe-string-listp (cdr texts)))
    (null texts)))

(defun fn-nntp-projection-articlep (article)
  (let ((payload (fn-article-payload article)))
    (and (fn-nntp-message-id-tokenp
          (fn-nntp-string-octets (fn-article-msgid article)))
         (fn-nntp-safe-string-listp (fn-article-groups article))
         (equal (car (fn-nntp-crlf-lines payload)) :ok)
         (fn-nntp-split-okp (fn-nntp-split-article payload)))))

(defun fn-nntp-projection-articlesp (articles)
  (if (consp articles)
      (and (fn-nntp-projection-articlep (car articles))
           (fn-nntp-projection-articlesp (cdr articles)))
    (null articles)))

(defun fn-nntp-projectionp (archive)
  (and (fn-statep archive)
       (fn-nntp-safe-string-listp (fn-state-groups archive))
       (fn-nntp-projection-articlesp (fn-state-articles archive))))

; -----------------------------------------------------------------------------
; Projection from the committed acceptance state

(defun fn-nntp-membership-number (group memberships)
  (if (consp memberships)
      (if (equal group (car (car memberships)))
          (cdr (car memberships))
        (fn-nntp-membership-number group (cdr memberships)))
    0))

(defun fn-nntp-find-group-number (group number articles)
  (if (consp articles)
      (if (equal (fn-nntp-membership-number group
                                            (fn-article-memberships (car articles)))
                 number)
          (car articles)
        (fn-nntp-find-group-number group number (cdr articles)))
    nil))

(defun fn-nntp-insert-number (number numbers)
  (if (consp numbers)
      (if (< number (car numbers))
          (cons number numbers)
        (cons (car numbers) (fn-nntp-insert-number number (cdr numbers))))
    (list number)))

(defun fn-nntp-group-numbers (group articles)
  (if (consp articles)
      (let ((number (fn-nntp-membership-number group
                                                 (fn-article-memberships (car articles)))))
        (if (posp number)
            (fn-nntp-insert-number number
                                   (fn-nntp-group-numbers group (cdr articles)))
          (fn-nntp-group-numbers group (cdr articles))))
    nil))

(defun fn-nntp-range-numbers (numbers low high)
  (if (consp numbers)
      (if (and (<= low (car numbers)) (<= (car numbers) high))
          (cons (car numbers)
                (fn-nntp-range-numbers (cdr numbers) low high))
        (fn-nntp-range-numbers (cdr numbers) low high))
    nil))

(defun fn-nntp-number-lines (numbers)
  (if (consp numbers)
      (cons (fn-nntp-decimal (car numbers))
            (fn-nntp-number-lines (cdr numbers)))
    nil))

(defun fn-nntp-next-number (current numbers)
  (if (consp numbers)
      (if (< current (car numbers))
          (car numbers)
        (fn-nntp-next-number current (cdr numbers)))
    0))

(defun fn-nntp-last-number (current numbers)
  (if (consp numbers)
      (if (< (car numbers) current)
          (let ((candidate (fn-nntp-last-number current (cdr numbers))))
            (if (posp candidate) candidate (car numbers)))
        0)
    0))

(defun fn-nntp-group-summary (archive group)
  (let ((numbers (fn-nntp-group-numbers group (fn-state-articles archive))))
    (if (consp numbers)
        (list (len numbers) (car numbers) (fn-nntp-last numbers))
      (let ((low (fn-next-number group (fn-state-nexts archive))))
        (list 0 low (if (posp low) (1- low) 0))))))

(defun fn-nntp-summary-count (x) (car x))
(defun fn-nntp-summary-low (x) (car (cdr x)))
(defun fn-nntp-summary-high (x) (car (cdr (cdr x))))

(defun fn-nntp-group-initial (archive group)
  (let ((summary (fn-nntp-group-summary archive group)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets "211 ")
           (fn-nntp-decimal (fn-nntp-summary-count summary)) '(32)
           (fn-nntp-decimal (fn-nntp-summary-low summary)) '(32)
           (fn-nntp-decimal (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-string-octets group)))))

(defun fn-nntp-group-result (session archive group)
  (if (member-equal group (fn-state-groups archive))
      (let* ((numbers (fn-nntp-group-numbers group (fn-state-articles archive)))
             (current (if (consp numbers) (car numbers) nil))
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
  (if (member-equal group (fn-state-groups archive))
      (let* ((numbers (fn-nntp-group-numbers group (fn-state-articles archive)))
             (current (if (consp numbers) (car numbers) nil))
             (next-session (fn-nntp-set-cursor session group current))
             (shown (fn-nntp-range-numbers numbers
                                           (fn-nntp-range-low range)
                                           (fn-nntp-range-high range))))
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
            (if (member-equal group (fn-state-groups archive))
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
         (fn-nntp-decimal number) '(32)
         (fn-nntp-string-octets (fn-article-msgid article))
         (cond ((equal kind :article) (fn-nntp-string-octets " article follows"))
               ((equal kind :head) (fn-nntp-string-octets " headers follow"))
               ((equal kind :body) (fn-nntp-string-octets " body follows"))
               (t (fn-nntp-string-octets " retrieved"))))))

(defun fn-nntp-article-response (session article number kind updatep group)
  (let ((section (fn-nntp-article-section article kind))
        (next-session (if updatep
                          (fn-nntp-set-cursor session group number)
                        session)))
    (if (equal kind :stat)
        (fn-nntp-make-result
         next-session
         (list (fn-nntp-reply-effect
                (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article)))))
      (if (equal (car section) :ok)
          (fn-nntp-make-result
           next-session
           (list (fn-nntp-reply-effect
                  (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                          (fn-nntp-stuff-lines (car (cdr section)))
                          '(46 13 10)))))
        (fn-nntp-single session "503 stored article framing unavailable")))))

(defun fn-nntp-current-retrieval (session archive kind)
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((article (fn-nntp-find-group-number group current
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
  (if (null args)
      (fn-nntp-current-retrieval session archive kind)
    (if (null (cdr args))
        (let ((token (car args)))
          (if (fn-nntp-number-tokenp token)
              (fn-nntp-number-retrieval session archive kind token)
            (fn-nntp-msgid-retrieval session archive kind token)))
      (fn-nntp-single session "501 syntax error"))))

(defun fn-nntp-next-or-last (session archive direction)
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let* ((numbers (fn-nntp-group-numbers group (fn-state-articles archive)))
               (number (if (equal direction :next)
                           (fn-nntp-next-number current numbers)
                         (fn-nntp-last-number current numbers))))
          (if (posp number)
              (let ((article (fn-nntp-find-group-number group number
                                                         (fn-state-articles archive))))
                (fn-nntp-article-response session article number :stat t group))
            (if (equal direction :next)
                (fn-nntp-single session "421 no next article")
              (fn-nntp-single session "422 no previous article"))))))))

(defun fn-nntp-active-line (archive group)
  (let ((summary (fn-nntp-group-summary archive group)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets group) '(32)
           (fn-nntp-decimal (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-decimal (fn-nntp-summary-low summary))
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

(defun fn-nntp-list-response (session archive args)
  (if (null args)
      (fn-nntp-multi session "215 list of active newsgroups follows"
                     (fn-nntp-active-lines archive (fn-state-groups archive)))
    (if (null (cdr args))
        (if (fn-nntp-keywordp (car args) "ACTIVE")
            (fn-nntp-multi session "215 list of active newsgroups follows"
                           (fn-nntp-active-lines archive (fn-state-groups archive)))
          (if (fn-nntp-keywordp (car args) "NEWSGROUPS")
              (fn-nntp-multi session "215 list of newsgroups follows"
                             (fn-nntp-newsgroup-lines (fn-state-groups archive)))
            (fn-nntp-single session "501 unsupported LIST variant")))
      (fn-nntp-single session "501 syntax error"))))

(defun fn-nntp-capabilities (session)
  ; No READER, POST, TLS, authentication, compression, or cryptographic
  ; capability is advertised: this laboratory implements only selected commands.
  (fn-nntp-multi session "101 capability list follows"
                 (list (fn-nntp-string-octets "VERSION 2")
                       (fn-nntp-string-octets "IMPLEMENTATION fn-nntp-lab"))))

(defun fn-nntp-help (session)
  (fn-nntp-multi session "100 help text follows"
                 (list (fn-nntp-string-octets "CAPABILITIES HEAD HELP QUIT STAT")
                       (fn-nntp-string-octets "GROUP ARTICLE BODY NEXT LAST LIST"))))

(defun fn-nntp-command (session archive tokens)
  (let ((keyword (car tokens)) (args (cdr tokens)))
    (cond
     ((fn-nntp-keywordp keyword "CAPABILITIES")
      (if (or (null args)
              (and (consp args) (null (cdr args))
                   (fn-nntp-keyword-tokenp (car args))))
          (fn-nntp-capabilities session)
        (fn-nntp-single session "501 syntax error")))
     ((fn-nntp-keywordp keyword "HELP")
      (if (null args) (fn-nntp-help session) (fn-nntp-single session "501 syntax error")))
     ((fn-nntp-keywordp keyword "QUIT")
      (if (null args)
          (fn-nntp-make-result (fn-nntp-make-session nil
                                                       (fn-nntp-session-group session)
                                                       (fn-nntp-session-current session))
                               (list (fn-nntp-reply-effect
                                      (fn-nntp-crlf (fn-nntp-string-octets "205 closing connection")))
                                     (fn-nntp-close-effect)))
        (fn-nntp-single session "501 syntax error")))
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
     ((fn-nntp-keywordp keyword "STAT") (fn-nntp-retrieval session archive :stat args))
     (t (fn-nntp-single session "500 command not recognized")))))

; A single command event is the integration boundary.  Other wire events are
; rejected as syntax, and a closed session produces no further effects.
(defun fn-nntp-step (session archive wire-event)
  (if (or (not (fn-nntp-sessionp session))
          (not (equal (fn-nntp-session-openp session) t)))
      (fn-nntp-make-result session nil)
    (if (not (fn-nntp-projectionp archive))
        (fn-nntp-single session "503 archive projection unavailable")
      (if (and (consp wire-event)
               (equal (car wire-event) :command)
               (consp (cdr wire-event))
               (null (cdr (cdr wire-event))))
          (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
            (if (consp tokens)
                (fn-nntp-command session archive tokens)
              (fn-nntp-single session "501 syntax error")))
        (fn-nntp-single session "501 syntax error")))))
