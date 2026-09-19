; Trusted experimental adapter helpers for the 9P2000 projection view.
;
; This file adds no news semantics.  Every served value is computed by the
; projection functions in books/nntp.lisp over the archive that
; host/reader-host.lisp already selected from the committed store, so the 9P
; view and the NNTP reader answer from one definition.  What is new here is
; only addressing: a mount names things by position in a listing, so each
; entry point takes an index rather than a client-supplied token, and the
; results reach the host as octet lists through one global.
(in-package "ACL2")
(include-book "../books/nntp")

; Listings are joined with LF so the host can split what ACL2 built without
; deriving any value of its own.  Group names are printable US-ASCII tokens
; (fn-nntp-safe-group-namep) and decimal fields are digits, so LF cannot occur
; inside an element of a listing this adapter builds.
(defun fn9p-join (pieces)
  (if (consp pieces)
      (append (car pieces) '(10) (fn9p-join (cdr pieces)))
    nil))

(defun fn9p-nth (n xs)
  (if (or (zp n) (not (consp xs)))
      (car xs)
    (fn9p-nth (- n 1) (cdr xs))))

(defun fn9p-string-lines (texts)
  (if (consp texts)
      (cons (fn-nntp-string-octets (car texts)) (fn9p-string-lines (cdr texts)))
    nil))

; Lowercase hexadecimal, used only to make a stored Message-ID usable as a
; file name.  It encodes the identifier; it does not derive one.
(defun fn9p-hex-digit (value)
  (if (< value 10) (+ 48 value) (+ 87 value)))

(defun fn9p-hex (octets)
  (if (consp octets)
      (cons (fn9p-hex-digit (floor (car octets) 16))
            (cons (fn9p-hex-digit (mod (car octets) 16))
                  (fn9p-hex (cdr octets))))
    nil))

; /by-id lists exactly the articles ARTICLE can serve by Message-ID: the
; per-article guards are fn-nntp-article-idp and fn-nntp-article-framedp, the
; same two fn-nntp-article-response applies before it emits a block.
(defun fn9p-servable-articles (articles)
  (if (consp articles)
      (if (fn-nntp-projection-articlep (car articles))
          (cons (car articles) (fn9p-servable-articles (cdr articles)))
        (fn9p-servable-articles (cdr articles)))
    nil))

(defun fn9p-id-names (articles)
  (if (consp articles)
      (cons (fn9p-hex (fn-nntp-string-octets (fn-article-msgid (car articles))))
            (fn9p-id-names (cdr articles)))
    nil))

; The whole-archive numbers of one group, in LISTGROUP's order and with
; LISTGROUP's membership rule: fn-nntp-group-range-numbers over the full
; article-number range.  This is the materialization path, which runs once per
; mount before any client is accepted; no served 9P read reaches it.
(defun fn9p-group-numbers (group archive)
  (fn-nntp-group-range-numbers group 1 *fn-nntp-max-article-number*
                               (fn-state-articles archive)))

(defun fn9p-status-octets (archive)
  (fn-nntp-append-pieces
   (list (fn-nntp-string-octets "generation ")
         (fn-nntp-decimal-field (fn-state-next-txid archive)) '(10)
         (fn-nntp-string-octets "articles ")
         (fn-nntp-decimal-field (len (fn-state-articles archive))) '(10)
         (fn-nntp-string-octets "groups ")
         (fn-nntp-decimal-field (len (fn-state-groups archive))) '(10))))

(defun fn9p-archive (state)
  (declare (xargs :stobjs state :mode :program))
  (f-get-global 'fn-reader-archive state))

(defun fn9p-emit (octets state)
  (declare (xargs :stobjs state :mode :program))
  (f-put-global 'fn9p-output octets state))

; Each entry point below leaves its octets in fn9p-output and returns T when
; the named thing is servable.  The host reads the octets with the same
; decimal-list parser the store and reader bridges use.

(defun fn9p-status (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn9p-emit (fn9p-status-octets (fn9p-archive state)) state)))
    (value t)))

(defun fn9p-groups (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn9p-emit
                (fn9p-join (fn9p-string-lines
                            (fn-state-groups (fn9p-archive state))))
                state)))
    (value t)))

(defun fn9p-numbers (group-index state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((archive (fn9p-archive state))
         (group (fn9p-nth group-index (fn-state-groups archive)))
         (state (fn9p-emit
                 (fn9p-join (fn-nntp-number-lines
                             (fn9p-group-numbers group archive)))
                 state)))
    (value t)))

; The article file's bytes are the stored payload, served only when
; fn-nntp-article-framedp holds.  That is the same guard fn-nntp-article-response
; requires before ARTICLE emits its block, and the block's dot-unstuffed content
; is exactly this payload.
(defun fn9p-article (group-index number-index state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((archive (fn9p-archive state))
         (group (fn9p-nth group-index (fn-state-groups archive)))
         (number (fn9p-nth number-index (fn9p-group-numbers group archive)))
         (article (fn-nntp-find-group-number group number
                                             (fn-state-articles archive))))
    (if (and (consp article)
             (fn-nntp-article-idp article)
             (fn-nntp-article-framedp article))
        (let ((state (fn9p-emit (fn-article-payload article) state)))
          (value t))
      (let ((state (fn9p-emit nil state)))
        (value nil)))))

(defun fn9p-ids (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((archive (fn9p-archive state))
         (state (fn9p-emit
                 (fn9p-join (fn9p-id-names
                             (fn9p-servable-articles (fn-state-articles archive))))
                 state)))
    (value t)))

(defun fn9p-id-article (index state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((archive (fn9p-archive state))
         (article (fn9p-nth index (fn9p-servable-articles
                                   (fn-state-articles archive)))))
    (if (consp article)
        (let ((state (fn9p-emit (fn-article-payload article) state)))
          (value t))
      (let ((state (fn9p-emit nil state)))
        (value nil)))))
