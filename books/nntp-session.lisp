; fn NNTP reader session core: the session record, effects and the exact
; article projection.
;
; Split out of books/nntp.lisp (2026-09-19).

(in-package "ACL2")
(include-book "nntp-syntax")
(include-book "payload-arena")

; The books below this one withdraw their definitions at their export events
; (2026-09-19 split of books/nntp.lisp).  This book is the continuation of
; that single file, so it re-enables exactly them, locally: within the
; chain the theory is the one the original file had at this point.
(local (in-theory (enable fn-nntp-syntax-vocabulary)))
;; -----------------------------------------------------------------------------
;; The article's bytes (records flip, 2026-09-27: F2, lane served-readers).
;;
;; A stored article's payload is a HANDLE into the payload arena
;; (books/acceptance.lisp, books/payload-arena.lisp): the served readers
;; read the octets it denotes through the arena, and the served machine
;; carries the arena stobj for that.  A payload that is not a handle is the
;; octet-list model's (a derived article the readers build and answer from:
;; fn-rcompat-served-article's served octets, the catalog view's rows); it
;; reads as itself.  A handle outside the arena reads as no octets, as
;; books/store-intern.lisp fn-handle-bytes.  This is the one place a served
;; reader reaches the bytes of an article.
(defun fn-nntp-payload-bytes (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (natp p)
      (if (< p (fn-arena-count fn-arena))
          (fn-arena-payload p fn-arena)
        nil)
    p))

(defun fn-nntp-article-bytes (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-nntp-payload-bytes (fn-article-payload article) fn-arena))

;; ALPHA of one article: its handle replaced by the octets it denotes (the
;; octet-list model's article; store-intern's fn-articles-wire-of per element).
(defun fn-nntp-article-alpha (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-make-article (fn-article-msgid article)
                   (fn-nntp-article-bytes article fn-arena)
                   (fn-article-groups article) (fn-article-memberships article)
                   (fn-article-pin article) (fn-article-stamp article)))

;; KEYSTONE (the representation boundary of every served reader): the bytes
;; a reader sees of an article are the bytes of its alpha, over ANY arena:
;; the octet-list model's article needs no arena, so a reader over a stored
;; article and the arena answers as the same reader over the model article.
(local
 (defthm fn-nntp-payload-list-element-not-natp
   (implies (and (fn-arn-payload-listp xs) (natp h) (< h (len xs)))
            (not (natp (nth h xs))))))

(defthm fn-nntp-article-bytes-of-alpha
  (implies (fn-arena-p fn-arena)
           (equal (fn-nntp-article-bytes (fn-nntp-article-alpha article fn-arena) any-arena)
                  (fn-nntp-article-bytes article fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-p-is-payload-listp fn-nntp-article-alpha))))

;; The handle case, through the arena's logical view: a handle below the
;; count reads the payload sealed at it.
(defthm fn-nntp-article-bytes-of-handle
  (implies (and (natp (fn-article-payload article))
                (< (fn-article-payload article) (len fn-arena)))
           (equal (fn-nntp-article-bytes article fn-arena)
                  (nth (fn-article-payload article) fn-arena))))

;; Alpha keeps everything but the payload.
(defthm fn-nntp-article-alpha-fields
  (let ((b (fn-nntp-article-alpha article fn-arena)))
    (and (equal (fn-article-msgid b) (fn-article-msgid article))
         (equal (fn-article-groups b) (fn-article-groups article))
         (equal (fn-article-memberships b) (fn-article-memberships article))
         (equal (fn-article-pin b) (fn-article-pin article))
         (equal (fn-article-stamp b) (fn-article-stamp article))
         (equal (fn-article-payload b) (fn-nntp-article-bytes article fn-arena)))))

; A payload that is not a handle reads as itself (a model article's octets,
; or NIL: a payload a reader erased, fn-nntp-newnews-without-payload's).
(defthm fn-nntp-payload-bytes-of-non-handle
  (implies (not (natp p))
           (equal (fn-nntp-payload-bytes p fn-arena) p)))

; Readers treat the bytes as opaque, as they treated the payload field.
(in-theory (disable fn-nntp-article-alpha fn-nntp-payload-bytes))

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

;; The multi-line block of a reply (ARTICLE, HEAD, BODY, OVER, HDR, LIST):
;; each line dot-stuffed and CRLF-terminated, RFC 3977 section 3.1.1.
;; The executable is a loop (PKT-481's class, D27): the reverse of the block
;; is built line by line onto an accumulator and turned round once, so the
;; control stack a served reply uses is the same for one line and for eight
;; million.  The recursion it replaced took one frame per line, and an
;; article of about two million lines exhausted a 64 MiB stack and stopped
;; the owner (planning/evidence/served-line-iterative-2026-09-26.md).
(defun fn-nntp-stuff-lines-onto (lines acc)
  (declare (xargs :guard t))
  (if (consp lines)
      (fn-nntp-stuff-lines-onto
       (cdr lines)
       (cons 10 (cons 13 (fn-ag-rev-onto (fn-wire-stuff-line (car lines)) acc))))
    acc))

(defun fn-nntp-stuff-lines-iter (lines)
  (declare (xargs :guard t))
  (fn-ag-rev-onto (fn-nntp-stuff-lines-onto lines nil) nil))

(defun fn-nntp-stuff-lines (lines)
  (declare (xargs :verify-guards nil))
  (mbe :logic
       (if (consp lines)
           (append (fn-nntp-crlf (fn-wire-stuff-line (car lines)))
                   (fn-nntp-stuff-lines (cdr lines)))
         nil)
       :exec (fn-nntp-stuff-lines-iter lines)))

(local (defthm fn-nntp-rev-onto-is-revappend
         (equal (fn-ag-rev-onto x acc) (revappend x acc))))

(local (defthm fn-nntp-revappend-of-append
         (equal (revappend (append a b) acc)
                (revappend b (revappend a acc)))))

(local (defthm fn-nntp-revappend-revappend
         (implies (true-listp x)
                  (equal (revappend (revappend x acc) nil)
                         (revappend acc x)))))

(local (defthm fn-nntp-stuff-lines-onto-is-revappend
         (equal (fn-nntp-stuff-lines-onto lines acc)
                (revappend (fn-nntp-stuff-lines lines) acc))))

;  KEYSTONE (D27, constant stack on the served reply).  The loop the host
; runs is the block the specification defines, on every argument; with it
; the guard proof of fn-nntp-stuff-lines is what makes the loop the
; executable.
(defthm fn-nntp-stuff-lines-iter-is-stuff-lines
  (equal (fn-nntp-stuff-lines-iter lines)
         (fn-nntp-stuff-lines lines)))

(local (in-theory (disable fn-nntp-rev-onto-is-revappend fn-nntp-revappend-of-append
                           fn-nntp-revappend-revappend
                           fn-nntp-stuff-lines-onto-is-revappend)))

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

(defun fn-nntp-article-section (article kind fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((payload (fn-nntp-article-bytes article fn-arena)))
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
(defun fn-nntp-article-framedp (article fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((payload (fn-nntp-article-bytes article fn-arena)))
    (and (equal (car (fn-nntp-crlf-lines payload)) :ok)
         (fn-nntp-split-okp (fn-nntp-split-article payload)))))

(defun fn-nntp-projection-articlep (article fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (fn-nntp-article-idp article)
       (fn-nntp-article-framedp article fn-arena)))
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
    fn-nntp-crlf fn-nntp-stuff-lines-onto fn-nntp-stuff-lines-iter
    fn-nntp-stuff-lines fn-nntp-single fn-nntp-multi 
    fn-nntp-multi-octets fn-nntp-append-pieces fn-nntp-crlf-lines-aux 
    fn-nntp-crlf-lines fn-nntp-split-article-aux fn-nntp-split-article 
    fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body 
    fn-nntp-article-section fn-nntp-safe-group-namep fn-nntp-safe-group-listp 
    fn-nntp-nexts-boundedp fn-nntp-article-idp fn-nntp-article-framedp 
    fn-nntp-projection-articlep fn-nntp-projectionp fn-nntp-open-session))

(in-theory (disable fn-nntp-session-vocabulary))
