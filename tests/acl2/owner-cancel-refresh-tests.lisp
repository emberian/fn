; A cancel withdraws its target on the flipped owner (flip-L8-2, 2026-09-27).
;
; After the records flip an archive article holds a HANDLE, and on dev the
; owner's refresh parsed that natural for a cancel's target: every cancel
; withdrew nothing.  The control facts are now the rows' (decided at intern,
; books/catalog-record.lisp fn-held-facts-of) and the refresh reads them from
; the Store's history (books/control-visible.lisp fn-ctl-article-plan).
; This book drives the real owner transitions of tests/acl2/owner-tests.lisp's
; served POST scenario (:begin, the store's prepare of the interned row, the
; I/O acknowledgements, :complete = fn-own-complete, whose fn-own-refresh
; the host reaches through fn-ccar-own-finish) over interned rows:
;
;   1. T posted with `Cancel-Lock: sha256:L', then C `Control: cancel <T>'
;      with `Cancel-Key: sha256:K', L = Base64(SHA-256(K)) (RFC 8315): after
;      C completes, the committed view no longer serves T; the one record is
;      C's key record resolved to T's lock.
;   2. The same with a key that opens nothing: T stays.
;   3. C first, T after (a cancel relayed ahead of its target): T is never
;      served; the record made before T arrived is resolved when it does.
;   4. The record the owner carries is recovery's: fn-own-start over the
;      same store decides the same records and the same archive.
(in-package "ACL2")
(include-book "owner-tests")
(include-book "must-fail-checked")

(defun ocr-line (text) (append (fn-record-string-octets text) '(13 10)))
(defun ocr-octets (lines)
  (if (consp lines)
      (append (ocr-line (car lines)) (ocr-octets (cdr lines)))
    (append '(13 10) (ocr-line "body"))))

(defconst *ocr-key* "b2NyLWtleS1mb3ItdGhlLXRhcmdldA==")
(defconst *ocr-other-key* "b3RoZXIta2V5LW9wZW5zLW5vdGhpbmc=")
(defconst *ocr-lock*
  (fn-record-octets-string (fn-ctl-lock-of-key (fn-record-string-octets *ocr-key*))))

(defconst *ocr-t-bytes*
  (ocr-octets (list "From: friend <friend@example.invalid>" "Newsgroups: fn.letters"
                    "Subject: mine" "Message-ID: <lt@example>"
                    (concatenate 'string "Cancel-Lock: sha256:" *ocr-lock*))))
(defun ocr-c-bytes (key)
  (ocr-octets (list "From: friend <friend@example.invalid>" "Newsgroups: fn.letters"
                    "Subject: cmsg cancel <lt@example>" "Message-ID: <lc@example>"
                    "Control: cancel <lt@example>"
                    (concatenate 'string "Cancel-Key: sha256:" key))))

; owner-tests' record metadata (own-record-wire) over these bytes, interned
; as the entry interns it (handle = journal sequence).
(defun ocr-row (sequence msgid bytes)
  (fn-hrt-row-at (fn-record-make sequence sequence sequence msgid bytes '("fn.letters")
                                 (concatenate 'string "own-pin:" msgid)
                                 (concatenate 'string "own-content:" msgid)
                                 (concatenate 'string "own-release:" msgid)
                                 2 841000000)
                 sequence))

(defun ocr-post (o row fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-own-run (fn-own-step o '(:begin 1) fn-arena) (own-post-events row) fn-arena))

(defun ocr-archive (o)
  (fn-article-msgids (fn-state-articles (fn-own-view-archive (fn-own-view o)))))

; The two posts from *own-b* (reader A open at version 0, connection 1 open).
(defun ocr-run (first second fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (ocr-post (ocr-post *own-b* first fn-arena) second fn-arena))

(defconst *ocr-rt0* (ocr-row 0 "<lt@example>" *ocr-t-bytes*))
(defconst *ocr-rc1* (ocr-row 1 "<lc@example>" (ocr-c-bytes *ocr-key*)))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift ocr-post 2)
(bpr-lift ocr-run 2)
(defconst *ocr-t-first* (in-arena-ocr-post *sr-arena* *own-b* *ocr-rt0*))
(defconst *ocr-after* (in-arena-ocr-run *sr-arena* *ocr-rt0* *ocr-rc1*))

; The rows carry the control facts of their bytes.
(assert-event
 (and (equal (fn-hf-control (fn-held-facts *ocr-rt0*))
             (fn-hf-control-with-nov (fn-ctl-control-of *ocr-t-bytes*)
                                     (fn-hnov-of *ocr-t-bytes*)))
      (equal (fn-ctl-control-locks (fn-hf-control (fn-held-facts *ocr-rt0*)))
             (list (fn-ctl-lock-of-key (fn-record-string-octets *ocr-key*))))
      (equal (fn-ctl-control-target (fn-hf-control (fn-held-facts *ocr-rc1*)))
             "<lt@example>")
      (equal (fn-ctl-control-keys (fn-hf-control (fn-held-facts *ocr-rc1*)))
             (list (fn-record-string-octets *ocr-key*)))))

; 1. T is served after its own post; after C, the committed view serves C
;    and not T, and the owner's relation holds throughout.
(assert-event
 (and (fn-own-relation *ocr-t-first*)
      (equal (ocr-archive *ocr-t-first*) (list "<lt@example>"))
      (fn-own-relation *ocr-after*)
      (equal (len (fn-own-ledger *ocr-after*)) 2)
      (equal (fn-article-msgids (fn-state-articles
                                 (fn-node-acceptance (fn-sn-node (fn-own-store *ocr-after*)))))
             (list "<lc@example>" "<lt@example>"))
      (equal (ocr-archive *ocr-after*) (list "<lc@example>"))))
(assert-event
 (let ((ws (fn-own-view-withdrawals (fn-own-view *ocr-after*))))
   (and (equal (len ws) 1)
        (equal (fn-ctl-w-target (car ws)) "<lt@example>")
        (equal (fn-ctl-w-cause (car ws)) "<lc@example>")
        (equal (fn-ctl-w-principal (car ws))
               (cons :cancel-key (list (fn-record-string-octets *ocr-key*))))
        (equal (fn-ctl-w-tlocks (car ws))
               (list (fn-ctl-lock-of-key (fn-record-string-octets *ocr-key*))))
        (equal (fn-ctl-withdrawal-effect (car ws) (list "fn.letters") nil nil) :poster))))

; 2. A key that opens nothing: the record is made, it declines, T stays.
(defconst *ocr-after-other*
  (in-arena-ocr-run *sr-arena* *ocr-rt0* (ocr-row 1 "<lc@example>" (ocr-c-bytes *ocr-other-key*))))
(assert-event
 (and (fn-own-relation *ocr-after-other*)
      (equal (len (fn-own-view-withdrawals (fn-own-view *ocr-after-other*))) 1)
      (equal (ocr-archive *ocr-after-other*) (list "<lc@example>" "<lt@example>"))))
(must-fail-checked
 (assert-event (equal (ocr-archive *ocr-after-other*) (list "<lc@example>"))))

; 3. The cancel first: C's record is made with no target locks (T has no
;    row); when T completes the refresh resolves it, and T is never served.
(defconst *ocr-rc0* (ocr-row 0 "<lc@example>" (ocr-c-bytes *ocr-key*)))
(defconst *ocr-rt1* (ocr-row 1 "<lt@example>" *ocr-t-bytes*))
(defconst *ocr-c-first* (in-arena-ocr-post *sr-arena* *own-b* *ocr-rc0*))
(defconst *ocr-c-then-t* (in-arena-ocr-run *sr-arena* *ocr-rc0* *ocr-rt1*))
(assert-event
 (let ((ws0 (fn-own-view-withdrawals (fn-own-view *ocr-c-first*)))
       (ws1 (fn-own-view-withdrawals (fn-own-view *ocr-c-then-t*))))
   (and (equal (ocr-archive *ocr-c-first*) (list "<lc@example>"))
        (equal (len ws0) 1)
        (null (fn-ctl-w-tlocks (car ws0)))
        (fn-own-relation *ocr-c-then-t*)
        (equal (len ws1) 1)
        (equal (fn-ctl-w-tlocks (car ws1))
               (list (fn-ctl-lock-of-key (fn-record-string-octets *ocr-key*))))
        (equal (ocr-archive *ocr-c-then-t*) (list "<lc@example>")))))

; 4. Live equals recovery at the owner: a fresh owner started over the
;    store the posts left decides the same records and serves the same
;    archive (fn-own-start reaches the refresh's discontinuity arm, the
;    table path).
(assert-event
 (let ((re (fn-own-start (fn-own-store *ocr-after*) 4))
       (re2 (fn-own-start (fn-own-store *ocr-c-then-t*) 4)))
   (and (equal (fn-own-view-withdrawals (fn-own-view re))
               (fn-own-view-withdrawals (fn-own-view *ocr-after*)))
        (equal (ocr-archive re) (ocr-archive *ocr-after*))
        (equal (fn-own-view-withdrawals (fn-own-view re2))
               (fn-own-view-withdrawals (fn-own-view *ocr-c-then-t*)))
        (equal (ocr-archive re2) (list "<lc@example>")))))
