; fn NNTP reader session core: the session record, effects and the exact
; article projection.
;
; Split out of books/nntp.lisp (2026-09-19).

(in-package "ACL2")
(include-book "nntp-syntax")
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

; ---------------------------------------------------------------------------
; Export theory
;
; The definitions this book adds are proof vocabulary for the books above it,
; not rules an includer should inherit.  They are withdrawn under one name so
; a book that reasons about the transitions re-enables exactly them in one
; line (books/nntp-invariants.lisp does).  Ground evaluation is unaffected:
; only the :definition runes are withdrawn.

(deftheory fn-nntp-session-vocabulary
  '(fn-nntp-session-openp fn-nntp-session-group fn-nntp-session-current 
    fn-nntp-session-projected fn-nntp-make-session fn-nntp-sessionp 
    fn-nntp-set-cursor fn-nntp-result-session fn-nntp-result-effects 
    fn-nntp-make-result fn-nntp-reply-effect fn-nntp-close-effect 
    fn-nntp-crlf fn-nntp-stuff-lines fn-nntp-single fn-nntp-multi 
    fn-nntp-multi-octets fn-nntp-append-pieces fn-nntp-crlf-lines-aux 
    fn-nntp-crlf-lines fn-nntp-split-article-aux fn-nntp-split-article 
    fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body 
    fn-nntp-article-section fn-nntp-safe-group-namep fn-nntp-safe-group-listp 
    fn-nntp-nexts-boundedp fn-nntp-article-idp fn-nntp-article-framedp 
    fn-nntp-projection-articlep fn-nntp-projectionp fn-nntp-open-session))

(in-theory (disable fn-nntp-session-vocabulary))
