; Teeth for books/protocol-codes.lisp over the hostile reader archive
; (tests/acl2/hostile-reader-archive.lisp, lane shared-books): the reader
; codes a two-article archive cannot reach -- withdrawn, reclaimed and
; unframed articles, control messages -- witnessed through the host-called
; dispatcher fn-nntp-command-pinned (lane defprotocol-2).
;
; Each witness asserts, for one command line on the archive's served view:
; the reply carries exactly CODE; the keystone's conclusion at that input
; (every code is within fn-proto-reader-codes of the first token); and the
; reply is the table's text for (ROW, KEY) -- `fn-proto-text' expands to the
; row's literal, so a text edited in the table and not at the arm (or the
; reverse) contradicts the witness.
(in-package "ACL2")
(include-book "../../books/protocol-codes")
(include-book "hostile-reader-archive")

; Sessions on fn.mod.a: the fixture's (no current article), and with the
; current article at 2 (O, ordinary), 3 (R, reclaimed) and 4 (F, unframed).
(defconst *pch-s2* (fn-nntp-set-cursor (fn-nntp-open-session *hra-archive*) "fn.mod.a" 2))
(defconst *pch-s3* (fn-nntp-set-cursor (fn-nntp-open-session *hra-archive*) "fn.mod.a" 3))
(defconst *pch-s4* (fn-nntp-set-cursor (fn-nntp-open-session *hra-archive*) "fn.mod.a" 4))

(defun pch-witness (session line code text)
  (declare (xargs :verify-guards nil))
  (let* ((result (hra-reply session line))
         (effects (fn-nntp-result-effects result))
         (tokens (fn-nntp-tokenize (hra-oct line))))
    (and (fn-proto-within effects (fn-proto-reader-codes (car tokens)))
         (equal (fn-proto-effect-codes effects) (list code))
         (member-equal code (fn-proto-reader-codes (car tokens)))
         (equal effects
                (fn-nntp-result-effects (fn-nntp-single session text))))))

(defmacro pch (session line row key code)
  `(assert-event (pch-witness ,session ,line ,code (fn-proto-text ,row ,key))))

; -----------------------------------------------------------------------------
; The witnesses

; WITHDRAWN (T, number 1): 423 by number, 430 by Message-ID, all four
; retrievals (the withdrawn arms precede every retrieval arm).
(pch *hra-session* "ARTICLE 1" "ARTICLE" :withdrawn-number 423)
(pch *hra-session* "ARTICLE <t@example.invalid>" "ARTICLE" :withdrawn-msgid 430)
(pch *hra-session* "HEAD 1" "HEAD" :withdrawn-number 423)
(pch *hra-session* "HEAD <t@example.invalid>" "HEAD" :withdrawn-msgid 430)
(pch *hra-session* "BODY 1" "BODY" :withdrawn-number 423)
(pch *hra-session* "BODY <t@example.invalid>" "BODY" :withdrawn-msgid 430)
(pch *hra-session* "STAT 1" "STAT" :withdrawn-number 423)
(pch *hra-session* "STAT <t@example.invalid>" "STAT" :withdrawn-msgid 430)

; RECLAIMED (R, number 3): by number, by Message-ID and as the current
; article; STAT too (it answers from the history, and says so).
(pch *hra-session* "ARTICLE 3" "ARTICLE" :reclaimed-number 423)
(pch *hra-session* "ARTICLE <r@example.invalid>" "ARTICLE" :reclaimed-msgid 430)
(pch *pch-s3* "ARTICLE" "ARTICLE" :reclaimed-number 423)
(pch *hra-session* "HEAD 3" "HEAD" :reclaimed-number 423)
(pch *hra-session* "HEAD <r@example.invalid>" "HEAD" :reclaimed-msgid 430)
(pch *pch-s3* "HEAD" "HEAD" :reclaimed-number 423)
(pch *hra-session* "BODY 3" "BODY" :reclaimed-number 423)
(pch *hra-session* "BODY <r@example.invalid>" "BODY" :reclaimed-msgid 430)
(pch *pch-s3* "BODY" "BODY" :reclaimed-number 423)
(pch *hra-session* "STAT 3" "STAT" :reclaimed-number 423)
(pch *hra-session* "STAT <r@example.invalid>" "STAT" :reclaimed-msgid 430)
; NEXT from O (2) lands on R, LAST from F (4) lands on R.
(pch *pch-s2* "NEXT" "NEXT" :reclaimed 423)
(pch *pch-s4* "LAST" "LAST" :reclaimed 423)
; OVER/XOVER: the current article reclaimed is 423; by Message-ID 430.
(pch *pch-s3* "OVER" "OVER" :reclaimed-number 423)
(pch *pch-s3* "XOVER" "XOVER" :reclaimed-number 423)
(pch *hra-session* "OVER <r@example.invalid>" "OVER" :reclaimed-msgid 430)
; A reclaimed or unframed article is skipped by a range, and a range of one
; such number is empty: OVER and HDR answer 423 "no articles in that range",
; XOVER its legacy 420 (books/nntp-reclaimed.lisp,
; fn-nov-lines-skip-a-reclaimed-article).
(pch *hra-session* "OVER 3" "OVER" :empty-range 423)
(pch *hra-session* "OVER 4" "OVER" :empty-range 423)
(pch *hra-session* "XOVER 3" "XOVER" :none-selected 420)
(pch *hra-session* "HDR Subject 3" "HDR" :empty-range 423)
(pch *hra-session* "HDR Subject 4" "HDR" :empty-range 423)

; UNFRAMED (F, number 4): the payload readers answer 503; STAT does not
; read the payload and is not refused (the fixture book witnesses it).
(pch *hra-session* "ARTICLE 4" "ARTICLE" :no-framing 503)
(pch *hra-session* "ARTICLE <f@example.invalid>" "ARTICLE" :no-framing 503)
(pch *pch-s4* "ARTICLE" "ARTICLE" :no-framing 503)
(pch *hra-session* "HEAD 4" "HEAD" :no-framing 503)
(pch *hra-session* "HEAD <f@example.invalid>" "HEAD" :no-framing 503)
(pch *pch-s4* "HEAD" "HEAD" :no-framing 503)
(pch *hra-session* "BODY 4" "BODY" :no-framing 503)
(pch *hra-session* "BODY <f@example.invalid>" "BODY" :no-framing 503)
(pch *pch-s4* "BODY" "BODY" :no-framing 503)
(pch *hra-session* "OVER <f@example.invalid>" "OVER" :no-framing 503)
(pch *hra-session* "HDR Subject <f@example.invalid>" "HDR" :no-framing 503)
(pch *pch-s4* "HDR Subject" "HDR" :no-framing 503)
(pch *hra-session* "XHDR Subject <f@example.invalid>" "XHDR" :no-framing 503)
(pch *pch-s4* "XHDR Subject" "XHDR" :no-framing 503)
(pch *hra-session* "XPAT Subject <f@example.invalid> *" "XPAT" :no-framing 503)

; HDR/XHDR over a RECLAIMED article answer the framing refusal, not
; "article reclaimed": their Message-ID and current-article arms test the
; payload's framing first, and a tombstone has no header/body separator.
; So the rows' :reclaimed-number/:reclaimed-msgid entries for HDR and XHDR
; are not reached on this archive (a finding for the table's owner: D13
; says a reclaimed article's answer says why).
(pch *hra-session* "HDR Subject <r@example.invalid>" "HDR" :no-framing 503)
(pch *pch-s3* "HDR Subject" "HDR" :no-framing 503)
(pch *hra-session* "XHDR Subject <r@example.invalid>" "XHDR" :no-framing 503)
(pch *pch-s3* "XHDR Subject" "XHDR" :no-framing 503)

; CONTROL (C executed, D owed): HDR :fn-control's lines are the fixture's
; (hostile-reader-archive asserts them); here the keystone's conclusion and
; the one code, the table's :headers.
(defun pch-codes (session line code)
  (declare (xargs :verify-guards nil))
  (let ((effects (fn-nntp-result-effects (hra-reply session line)))
        (tokens (fn-nntp-tokenize (hra-oct line))))
    (and (fn-proto-within effects (fn-proto-reader-codes (car tokens)))
         (equal (fn-proto-effect-codes effects) (list code)))))
(assert-event (and (pch-codes *hra-session* "HDR :fn-control <c@example.invalid>" 225)
                   (pch-codes *hra-session* "HDR :fn-control <d@example.invalid>" 225)
                   (equal (fn-nntp-hdr-initial nil) (fn-proto-text "HDR" :headers))))

; -----------------------------------------------------------------------------
; Not witnessed, with the reason.
; 503 "control status unavailable" (HDR :fn-control): the arm refuses when
; the rendered item -- the status and fn-ctl-target-octets of the control
; message -- holds a TAB, CR, LF or NUL (fn-nntp-control-cleanp).  An executed
; withdrawal's target equals a held Message-ID, and the ingest paths (POST,
; IHAVE/TAKETHIS) admit only a printable Message-ID; fn-accept-prepare itself
; checks only (stringp msgid), so the kernel alone does not exclude it: an
; archive accepted directly with an unclean identifier would reach the arm.
; Unreachable in composition by that argument, not by a theorem (a
; reach_check candidate).
; 423/430 "article reclaimed" for HDR/XHDR: see above (answered 503 first).
; 501 "unsupported LIST variant" and the XFNCATCHUP 503 (a view of 2^64
; entries) need no hostile archive and are protocol-codes-tests' to name.
