; Teeth for books/protocol-codes.lisp and books/protocol-framing.lisp: the
; reader dispatcher's reply codes are its table rows.
;
; Positive witnesses: for each row, commands on a small two-article archive
; whose replies carry each listed :reader code that such a state reaches;
; each witness asserts the keystone's complete conclusion (the codes are
; within fn-proto-reader-codes of the first token) AND the exact code, so the
; row cannot lose that code without the witness contradicting the theorem.
; Must-fail teeth: each row's theorem with its witnessed success (or refusal)
; code removed does not prove.  Codes a two-article archive cannot reach
; (reclaimed and withdrawn articles, unframed payloads, the defensive 503s
; marked :unreachable in the table) are named at the end.
(in-package "ACL2")
(include-book "../../books/protocol-framing")
(include-book "must-fail-checked")

(defconst *pct-groups* '("fn.test" "fn.other"))
(defconst *pct-id-1* "<one@fn.invalid>")
(defconst *pct-id-2* "<two@fn.invalid>")
(defconst *pct-payload-1*
  (append (fn-nntp-string-octets "Message-ID: <one@fn.invalid>") '(13 10)
          (fn-nntp-string-octets "Subject: first") '(13 10)
          '(13 10) (fn-nntp-string-octets "One") '(13 10)))
(defconst *pct-payload-2*
  (append (fn-nntp-string-octets "Message-ID: <two@fn.invalid>") '(13 10)
          (fn-nntp-string-octets "Subject: second") '(13 10)
          '(13 10) (fn-nntp-string-octets "Two") '(13 10)))
;; Handles 0 and 1 name the two payloads (the records flip: an accepted
;; article's payload is an arena handle).
(defconst *pct-archive*
  (fn-accept-complete
   (fn-accept-prepare
    (fn-accept-complete
     (fn-accept-prepare (fn-initial-state *pct-groups*) 1 *pct-id-1* 0
                        '("fn.test") 841000000)
     0 1 :durable)
    2 *pct-id-2* 1 '("fn.test") 841000500)
   1 2 :durable))
(assert-event (fn-nntp-projectionp *pct-archive*))
(assert-event (equal (len (fn-state-articles *pct-archive*)) 2))
(defconst *pct-index* (fn-midx-build (fn-state-articles *pct-archive*)))
(defconst *pct-env* (fn-nntp-env nil nil nil))
(defconst *pct-env-clock*
  (fn-nntp-env (fn-clock-observation 1000 843136496000 1000 t) nil nil))
(defconst *pct-env-posting*
  (fn-nntp-env (fn-clock-observation 1000 843136496000 1000 t) nil t))

; Sessions: none selected; fn.test at 1; fn.test at 2; fn.test with no
; current article; and one whose projection verdict is negative.
(defconst *pct-s0* (fn-nntp-make-session t nil nil t))
(defconst *pct-s1* (fn-nntp-make-session t "fn.test" 1 t))
(defconst *pct-s2* (fn-nntp-make-session t "fn.test" 2 t))
(defconst *pct-sg* (fn-nntp-make-session t "fn.test" nil t))
(defconst *pct-snp* (fn-nntp-make-session t nil nil nil))

(include-book "arena-lift")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-nntp-message-id-token-is-response-text)
                          (:rewrite fn-nntp-response-text-is-octets))))
(defconst *sr-arena* (list *pct-payload-1* *pct-payload-2*))
(bpr-lift fn-nntp-command-pinned 6)

(defun pct-effects (session env line)
  (declare (xargs :mode :program))
  (fn-nntp-result-effects
   (in-arena-fn-nntp-command-pinned
    *sr-arena* session *pct-archive* *pct-index* nil env
    (fn-nntp-tokenize (fn-nntp-string-octets line)))))

; The keystone's conclusion at this input, and the one code the reply
; carries.
(defun pct-witness (session env line code)
  (declare (xargs :mode :program))
  (let ((effects (pct-effects session env line))
        (tokens (fn-nntp-tokenize (fn-nntp-string-octets line))))
    (and (fn-proto-within effects (fn-proto-reader-codes (car tokens)))
         (equal (fn-proto-effect-codes effects) (list code)))))

(defmacro pct (session line code &key (env '*pct-env*))
  `(assert-event (pct-witness ,session ,env ,line ,code)))

; -----------------------------------------------------------------------------
; Positive witnesses, row by row

(pct *pct-s0* "CAPABILITIES" 101)
(pct *pct-s0* "CAPABILITIES A B" 501)
(pct *pct-s0* "HELP" 100)
(pct *pct-s0* "HELP ME" 501)
(pct *pct-s0* "MODE READER" 201)
(pct *pct-s0* "MODE READER" 200 :env *pct-env-posting*)
(pct *pct-s0* "MODE" 501)
(pct *pct-s0* "QUIT" 205)
(pct *pct-s0* "QUIT NOW" 501)
(pct *pct-s0* "GROUP fn.test" 211)
(pct *pct-s0* "GROUP fn.none" 411)
(pct *pct-s0* "GROUP" 501)
(pct *pct-snp* "GROUP fn.test" 503)
(pct *pct-s0* "LISTGROUP fn.test" 211)
(pct *pct-s0* "LISTGROUP fn.none" 411)
(pct *pct-s0* "LISTGROUP" 412)
(pct *pct-s0* "LISTGROUP fn.test 1- x" 501)
(pct *pct-snp* "LISTGROUP fn.test" 503)
(pct *pct-s2* "LAST" 223)
(pct *pct-s1* "LAST" 422)
(pct *pct-s0* "LAST" 412)
(pct *pct-sg* "LAST" 420)
(pct *pct-s1* "LAST 1" 501)
(pct *pct-snp* "LAST" 503)
(pct *pct-s1* "NEXT" 223)
(pct *pct-s2* "NEXT" 421)
(pct *pct-s0* "NEXT" 412)
(pct *pct-sg* "NEXT" 420)
(pct *pct-s1* "NEXT 1" 501)
(pct *pct-snp* "NEXT" 503)
(pct *pct-s1* "ARTICLE" 220)
(pct *pct-s1* "ARTICLE 9" 423)
(pct *pct-s1* "ARTICLE <none@fn.invalid>" 430)
(pct *pct-s0* "ARTICLE" 412)
(pct *pct-sg* "ARTICLE" 420)
(pct *pct-s1* "ARTICLE 1 2" 501)
(pct *pct-snp* "ARTICLE" 503)
(pct *pct-s1* "HEAD 2" 221)
(pct *pct-s1* "HEAD 9" 423)
(pct *pct-s1* "HEAD <none@fn.invalid>" 430)
(pct *pct-s0* "HEAD" 412)
(pct *pct-sg* "HEAD" 420)
(pct *pct-s1* "HEAD 1 2" 501)
(pct *pct-snp* "HEAD" 503)
(pct *pct-s1* "BODY <two@fn.invalid>" 222)
(pct *pct-s1* "BODY 9" 423)
(pct *pct-s1* "BODY <none@fn.invalid>" 430)
(pct *pct-s0* "BODY" 412)
(pct *pct-sg* "BODY" 420)
(pct *pct-s1* "BODY 1 2" 501)
(pct *pct-snp* "BODY" 503)
(pct *pct-s1* "STAT" 223)
(pct *pct-s1* "STAT 9" 423)
(pct *pct-s1* "STAT <none@fn.invalid>" 430)
(pct *pct-s0* "STAT" 412)
(pct *pct-sg* "STAT" 420)
(pct *pct-s1* "STAT 1 2" 501)
(pct *pct-snp* "STAT" 503)
(pct *pct-s1* "OVER 1-2" 224)
(pct *pct-s1* "OVER 5-9" 423)
(pct *pct-s1* "OVER <none@fn.invalid>" 430)
(pct *pct-s0* "OVER" 412)
(pct *pct-sg* "OVER" 420)
(pct *pct-s1* "OVER 1 2" 501)
(pct *pct-snp* "OVER" 503)
(pct *pct-s1* "XOVER 1-2" 224)
(pct *pct-s1* "XOVER 5-9" 420)
(pct *pct-s0* "XOVER" 412)
(pct *pct-sg* "XOVER" 420)
(pct *pct-s1* "XOVER 1 2" 501)
(pct *pct-snp* "XOVER" 503)
(pct *pct-s1* "HDR Subject 1-2" 225)
(pct *pct-s1* "HDR Subject 5-9" 423)
(pct *pct-s1* "HDR Subject <none@fn.invalid>" 430)
(pct *pct-s0* "HDR Subject" 412)
(pct *pct-sg* "HDR Subject" 420)
(pct *pct-s1* "HDR" 501)
(pct *pct-snp* "HDR Subject" 503)
(pct *pct-s1* "XHDR Subject 1-2" 221)
(pct *pct-s1* "XHDR Subject 5-9" 420)
(pct *pct-s1* "XHDR Subject <none@fn.invalid>" 430)
(pct *pct-s0* "XHDR Subject" 412)
(pct *pct-sg* "XHDR Subject" 420)
(pct *pct-s1* "XHDR" 501)
(pct *pct-snp* "XHDR Subject" 503)
(pct *pct-s1* "XPAT Subject 1-2 *" 221)
(pct *pct-s1* "XPAT Subject <none@fn.invalid> *" 430)
(pct *pct-s0* "XPAT Subject 1-2 *" 412)
(pct *pct-s1* "XPAT" 501)
(pct *pct-snp* "XPAT Subject 1-2 *" 503)
(pct *pct-s0* "LIST" 215)
(pct *pct-s0* "LIST NOSUCH" 501)
(pct *pct-s0* "LIST DISTRIB.PATS" 503)
(pct *pct-snp* "LIST" 503)
(pct *pct-s0* "NEWGROUPS 20260101 000000" 231)
(pct *pct-s0* "NEWGROUPS 260101 000000" 503)
(pct *pct-s0* "NEWGROUPS" 501)
(pct *pct-snp* "NEWGROUPS 20260101 000000" 503)
(pct *pct-s0* "NEWNEWS * 20260101 000000" 230)
(pct *pct-s0* "NEWNEWS * 260101 000000" 503)
(pct *pct-s0* "NEWNEWS" 501)
(pct *pct-snp* "NEWNEWS * 20260101 000000" 503)
(pct *pct-s0* "DATE" 111 :env *pct-env-clock*)
(pct *pct-s0* "DATE" 503)
(pct *pct-s0* "DATE NOW" 501)
(pct *pct-s0* "POST" 340)
(pct *pct-s0* "POST NOW" 501)
(pct *pct-s0* "IHAVE <one@fn.invalid>" 502)
(pct *pct-s0* "CHECK <one@fn.invalid>" 502)
(pct *pct-s0* "TAKETHIS <one@fn.invalid>" 502)
(pct *pct-s0* "XFNCATCHUP" 501)
(pct *pct-snp* "XFNCATCHUP fn.test 0 0 1" 503)
(pct *pct-s0* "123" 501)
(pct *pct-s0* "FOO" 500)
(pct *pct-s0* "AUTHINFO USER carol" 500)
(pct *pct-s0* "STARTTLS" 500)
(pct *pct-s0* "XFNCATCHUP fn.test 0000000000000000 0000000000000000000000000000000000000000000000000000000000000000 262144" 291)
(pct *pct-s0* "XFNCATCHUP fn.test 0000000000000009 0000000000000000000000000000000000000000000000000000000000000000 262144" 423)

; -----------------------------------------------------------------------------
; Must-fail: each row's theorem with a witnessed code removed.  The hints
; are the generated theorem's, so a failure is the missing code and not a
; weaker proof search.

(defmacro pct-drop (name row code)
  `(must-fail-checked
    (defthm ,name
      (implies (fn-nntp-keywordp (car tokens) ,row)
               (fn-proto-within
                (fn-nntp-result-effects
                 (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))
                ',(remove code (cdr (assoc-equal row *fn-proto-reader-alist*)))))
      :hints (("Goal" :in-theory (e/d ,*fn-proto-dispatch-theory*
                                      ,(append *fn-proto-token-theory*
                                               *fn-proto-closed-theory*)))))))

(pct-drop pct-false-capabilities-without-101 "CAPABILITIES" 101)
(pct-drop pct-false-help-without-100 "HELP" 100)
(pct-drop pct-false-mode-without-201 "MODE" 201)
(pct-drop pct-false-quit-without-205 "QUIT" 205)
(pct-drop pct-false-group-without-411 "GROUP" 411)
(pct-drop pct-false-listgroup-without-412 "LISTGROUP" 412)
(pct-drop pct-false-last-without-422 "LAST" 422)
(pct-drop pct-false-next-without-421 "NEXT" 421)
(pct-drop pct-false-article-without-220 "ARTICLE" 220)
(pct-drop pct-false-head-without-221 "HEAD" 221)
(pct-drop pct-false-body-without-222 "BODY" 222)
(pct-drop pct-false-stat-without-223 "STAT" 223)
(pct-drop pct-false-over-without-224 "OVER" 224)
(pct-drop pct-false-xover-without-224 "XOVER" 224)
(pct-drop pct-false-hdr-without-225 "HDR" 225)
(pct-drop pct-false-xhdr-without-221 "XHDR" 221)
(pct-drop pct-false-xpat-without-221 "XPAT" 221)
(pct-drop pct-false-list-without-215 "LIST" 215)
(pct-drop pct-false-newgroups-without-231 "NEWGROUPS" 231)
(pct-drop pct-false-newnews-without-230 "NEWNEWS" 230)
(pct-drop pct-false-date-without-111 "DATE" 111)
(pct-drop pct-false-post-without-340 "POST" 340)
(pct-drop pct-false-ihave-without-502 "IHAVE" 502)
(pct-drop pct-false-xfncatchup-without-291 "XFNCATCHUP" 291)

; The pseudo-rows: the syntax and unrecognized codes are load-bearing.
(must-fail-checked
 (defthm pct-false-unrecognized-without-500
   (implies (and (fn-nntp-keyword-tokenp (car tokens))
                 (not (fn-nntp-keywordp (car tokens) "CAPABILITIES")))
            (fn-proto-within
             (fn-nntp-result-effects
              (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))
             '(101 501)))))

; -----------------------------------------------------------------------------
; The framing column

(defun pct-offered (session env line)
  (declare (xargs :mode :program))
  (fn-post-offeredp (pct-effects session env line)))

; POST, the one :article row, offers; every :command row's witness above
; does not.
(assert-event (and (pct-offered *pct-s0* *pct-env* "POST")
                   (fn-proto-article-framing-p
                    (car (fn-nntp-tokenize (fn-nntp-string-octets "POST")))
                    *fn-proto-article-framing*)))
(assert-event (and (not (pct-offered *pct-s0* *pct-env* "GROUP fn.test"))
                   (not (pct-offered *pct-s1* *pct-env* "ARTICLE"))
                   (not (pct-offered *pct-s0* *pct-env* "XFNCATCHUP fn.test 0000000000000000 0000000000000000000000000000000000000000000000000000000000000000 262144"))
                   (not (fn-proto-article-framing-p
                         (car (fn-nntp-tokenize (fn-nntp-string-octets "GROUP")))
                         *fn-proto-article-framing*))))

; The :article exclusion is load-bearing: without it the framing theorem
; is false of POST.
(must-fail-checked
 (defthm pct-false-no-row-offers
   (not (fn-post-offeredp
         (fn-nntp-result-effects
          (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))))))

; -----------------------------------------------------------------------------
; The codes a two-article archive cannot reach -- withdrawn, reclaimed and
; unframed articles, control messages -- are witnessed over the hostile
; reader archive in tests/acl2/protocol-codes-hra-tests.lisp (lane
; defprotocol-2), which also names the ones no archive reaches and why.
; Still not witnessed here: 501 "unsupported LIST variant", 503 "catch-up log
; position out of range" (a view of 2^64 entries), and the :unreachable rows
; (503 "stored article identifier unavailable", MODE's 502).
