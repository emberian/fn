; Teeth for books/nntp-list-counts.lisp and books/owner-list-counts-read.lisp.
(in-package "ACL2")
(include-book "../../books/owner-list-counts-read")
(include-book "std/testing/must-fail" :dir :system)

(defun nlc-t-payload (id)
  (append (fn-nntp-string-octets "Message-ID: ") (fn-nntp-string-octets id)
          '(13 10) (fn-nntp-string-octets "Subject: Test") '(13 10 13 10)
          (fn-nntp-string-octets "Hello") '(13 10)))

(defconst *nlc-t-groups* '("fn.letters" "fn.other" "fn.empty"))
(defconst *nlc-t-a1*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *nlc-t-groups*) 1 "<one@t.invalid>"
                      (nlc-t-payload "<one@t.invalid>") '("fn.letters") 841000000)
   0 1 :durable))
(defconst *nlc-t-a2*
  (fn-accept-complete
   (fn-accept-prepare *nlc-t-a1* 1 "<two@t.invalid>"
                      (nlc-t-payload "<two@t.invalid>")
                      '("fn.letters" "fn.other") 841000001)
   1 1 :durable))
(defconst *nlc-t-trie* (fn-midx-build (fn-state-articles *nlc-t-a2*)))
(defconst *nlc-t-buckets* (fn-gidx-build (fn-state-articles *nlc-t-a2*)))
(defconst *nlc-t-pin* (fn-gidx-pin *nlc-t-trie* *nlc-t-buckets*))
(defconst *nlc-t-open* (fn-nntp-open-session *nlc-t-a2*))
(defmacro nlc-t-in (group)
  `(fn-nntp-result-session (fn-nntp-group-result *nlc-t-open* *nlc-t-a2* ,group)))
(defmacro nlc-t-cmd (session index keyword args)
  `(fn-nntp-archive-command-pinned ,session *nlc-t-a2* ,index nil nil
                                   (fn-nntp-string-octets ,keyword)
                                   (list ,@(pairlis-x1 'fn-nntp-string-octets
                                                      (pairlis$ args nil)))))
(defmacro nlc-t-lines (&rest lines)
  `(list ,@(pairlis-x1 'fn-nntp-string-octets (pairlis$ lines nil))))

; Reachable, non-degenerate witness: two accepted articles, one of them in
; two groups, one configured group empty.
(assert-event (fn-statep *nlc-t-a2*))
(assert-event (fn-nntp-projectionp *nlc-t-a2*))
(assert-event (equal (len (fn-state-articles *nlc-t-a2*)) 2))

; LIST COUNTS: name high low count status, exact counts, the empty group's
; watermark pair, through the pinned buckets; the wildmat form; 501 on two
; arguments.
(assert-event
 (equal (nlc-t-cmd *nlc-t-open* *nlc-t-pin* "LIST" ("COUNTS"))
        (fn-nntp-multi *nlc-t-open* "215 list of newsgroups follows"
                       (nlc-t-lines "fn.letters 2 1 2 y" "fn.other 1 1 1 y"
                                    "fn.empty 0 1 0 y"))))
(assert-event
 (equal (nlc-t-cmd *nlc-t-open* *nlc-t-pin* "list" ("counts" "fn.o*"))
        (fn-nntp-multi *nlc-t-open* "215 list of newsgroups follows"
                       (nlc-t-lines "fn.other 1 1 1 y"))))
(assert-event
 (equal (nlc-t-cmd *nlc-t-open* *nlc-t-pin* "LIST" ("COUNTS" "a" "b"))
        (fn-nntp-single *nlc-t-open* "501 syntax error")))
; The unpinned dispatcher answers the same.
(assert-event
 (equal (nlc-t-cmd *nlc-t-open* *nlc-t-pin* "LIST" ("COUNTS"))
        (nlc-t-cmd *nlc-t-open* *nlc-t-trie* "LIST" ("COUNTS"))))
; The count is LISTGROUP's length.
(assert-event
 (equal (fn-nntp-group-count "fn.letters" (fn-state-articles *nlc-t-a2*))
        (len (fn-nntp-group-range-numbers "fn.letters" 1 2147483647
                                          (fn-state-articles *nlc-t-a2*)))))
(assert-event
 (equal (fn-nntp-group-count "fn.letters" (fn-state-articles *nlc-t-a2*)) 2))
; CAPABILITIES advertises it.
(assert-event
 (member-equal (fn-nntp-string-octets
                "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT")
               (fn-nntp-capability-lines nil)))

; fn-gidx-list-counts-command-is-the-archive-fold, hypothesis 2: buckets
; that are not the build of the archive (the first archive's) answer a
; different count for the same archive.
(defconst *nlc-t-stale*
  (fn-gidx-pin *nlc-t-trie* (fn-gidx-build (fn-state-articles *nlc-t-a1*))))
(assert-event
 (not (equal (nlc-t-cmd *nlc-t-open* *nlc-t-stale* "LIST" ("COUNTS"))
             (nlc-t-cmd *nlc-t-open* *nlc-t-trie* "LIST" ("COUNTS")))))
(must-fail
 (with-prover-step-limit
  200000
 (defthm nlc-t-fold-false-without-buckets
   (implies (fn-nntp-projectionp archive)
            (equal (fn-gidx-list-counts-command session archive buckets args)
                   (fn-nntp-list-counts-command session archive args))))))

; Hypothesis 1: an archive that is not a projection, here one article with
; two memberships in one group, has a bucket count the fold does not.
(defconst *nlc-t-art2* (car (fn-state-articles *nlc-t-a2*)))
(defconst *nlc-t-art1* (cadr (fn-state-articles *nlc-t-a2*)))
(assert-event (equal (fn-article-msgid *nlc-t-art2*) "<two@t.invalid>"))
(defconst *nlc-t-dup*
  (fn-make-state (fn-state-groups *nlc-t-a2*) (fn-state-nexts *nlc-t-a2*)
                 (list (fn-make-article
                        (fn-article-msgid *nlc-t-art2*)
                        (fn-article-payload *nlc-t-art2*)
                        (fn-article-groups *nlc-t-art2*)
                        '(("fn.letters" . 2) ("fn.letters" . 3))
                        (fn-article-pin *nlc-t-art2*)
                        (fn-article-stamp *nlc-t-art2*))
                       *nlc-t-art1*)
                 (fn-state-next-txid *nlc-t-a2*) (fn-state-pending *nlc-t-a2*)
                 (fn-state-fenced *nlc-t-a2*)))
(assert-event (not (fn-nntp-projectionp *nlc-t-dup*)))
(assert-event
 (not (equal (fn-gidx-list-counts-command
              *nlc-t-open* *nlc-t-dup*
              (fn-gidx-build (fn-state-articles *nlc-t-dup*)) nil)
             (fn-nntp-list-counts-command *nlc-t-open* *nlc-t-dup* nil))))
(must-fail
 (with-prover-step-limit
  200000
 (defthm nlc-t-fold-false-without-projection
   (implies (equal buckets (fn-gidx-build (fn-state-articles archive)))
            (equal (fn-gidx-list-counts-command session archive buckets args)
                   (fn-nntp-list-counts-command session archive args))))))

; fn-gidx-counts-work-of-build-bound, its one hypothesis: listing one group
; four times visits more than G*B + M.
(assert-event
 (< (+ (* 4 (len *nlc-t-buckets*))
       (len (fn-index-build (fn-state-articles *nlc-t-a2*))))
    (fn-gidx-counts-work *nlc-t-buckets*
                         '("fn.letters" "fn.letters" "fn.letters" "fn.letters"))))
(must-fail
 (with-prover-step-limit
  200000
 (defthm nlc-t-work-false-with-repeats
   (<= (fn-gidx-counts-work (fn-gidx-build articles) groups)
       (+ (* (len groups) (len (fn-gidx-build articles)))
          (len (fn-index-build articles))))
   ;; The ground witness above refutes it.  Without this hint the attempt
   ;; nests inductions to the step limit (3.7 s) before it fails.
   :hints (("Goal" :do-not-induct t)))))

; The numbered Message-ID answer (RFC 3977 section 6.2.1.2): the number in
; the selected group; 0 with no group selected; 0 when the article is not in
; the selected group.
(defmacro nlc-t-stat-line (text)
  `(list (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-string-octets ,text)))))
(assert-event
 (equal (fn-nntp-result-effects
         (nlc-t-cmd (nlc-t-in "fn.letters") *nlc-t-pin* "STAT" ("<two@t.invalid>")))
        (nlc-t-stat-line "223 2 <two@t.invalid> retrieved")))
(assert-event
 (equal (fn-nntp-result-effects
         (nlc-t-cmd (nlc-t-in "fn.other") *nlc-t-pin* "STAT" ("<two@t.invalid>")))
        (nlc-t-stat-line "223 1 <two@t.invalid> retrieved")))
(assert-event
 (equal (fn-nntp-result-effects
         (nlc-t-cmd *nlc-t-open* *nlc-t-pin* "STAT" ("<two@t.invalid>")))
        (nlc-t-stat-line "223 0 <two@t.invalid> retrieved")))
(assert-event
 (equal (fn-nntp-result-effects
         (nlc-t-cmd (nlc-t-in "fn.other") *nlc-t-pin* "STAT" ("<one@t.invalid>")))
        (nlc-t-stat-line "223 0 <one@t.invalid> retrieved")))
; The session is not changed by the Message-ID form.
(assert-event
 (equal (fn-nntp-result-session
         (nlc-t-cmd (nlc-t-in "fn.letters") *nlc-t-pin* "STAT" ("<two@t.invalid>")))
        (nlc-t-in "fn.letters")))
; The second command with that number retrieves the same article.
(assert-event
 (equal (fn-nntp-number-retrieval (nlc-t-in "fn.letters") *nlc-t-a2* :article
                                  (fn-nntp-string-octets "2"))
        (fn-nntp-article-response (nlc-t-in "fn.letters") *nlc-t-art2* 2
                                  :article t "fn.letters")))

; fn-nntp-msgid-number-retrieves-the-same-article, hypothesis 1 (fn-statep):
; an earlier article holding the same (group . number) is what the number
; names instead.
(defconst *nlc-t-clash*
  (fn-make-state (fn-state-groups *nlc-t-a2*) (fn-state-nexts *nlc-t-a2*)
                 (list (fn-make-article
                        (fn-article-msgid *nlc-t-art1*)
                        (fn-article-payload *nlc-t-art1*)
                        (fn-article-groups *nlc-t-art1*)
                        '(("fn.letters" . 2))
                        (fn-article-pin *nlc-t-art1*)
                        (fn-article-stamp *nlc-t-art1*))
                       *nlc-t-art2*)
                 (fn-state-next-txid *nlc-t-a2*) (fn-state-pending *nlc-t-a2*)
                 (fn-state-fenced *nlc-t-a2*)))
(assert-event (not (fn-statep *nlc-t-clash*)))
(assert-event
 (equal (fn-nntp-msgid-local-number (nlc-t-in "fn.letters")
                                    (fn-find-article
                                     "<two@t.invalid>"
                                     (fn-state-articles *nlc-t-clash*)))
        2))
(assert-event
 (not (equal (fn-nntp-number-retrieval (nlc-t-in "fn.letters") *nlc-t-clash*
                                       :stat (fn-nntp-string-octets "2"))
             (fn-nntp-article-response (nlc-t-in "fn.letters") *nlc-t-art2* 2
                                       :stat t "fn.letters"))))
(must-fail
 (with-prover-step-limit
  200000
 (defthm nlc-t-number-false-without-state
   (let* ((article (fn-find-article (fn-nntp-token-string token)
                                    (fn-state-articles archive)))
          (n (fn-nntp-msgid-local-number session article)))
     (implies (and (posp n)
                   (fn-nntp-number-tokenp number-token)
                   (equal (fn-nntp-decimal-value number-token) n))
              (equal (fn-nntp-number-retrieval session archive kind number-token)
                     (fn-nntp-article-response
                      session article n kind t
                      (fn-nntp-session-group session))))))))

; Hypothesis 2 (posp n): with no group selected the number is 0, and a
; number command then answers 412, not the article.
(assert-event
 (not (equal (fn-nntp-number-retrieval *nlc-t-open* *nlc-t-a2* :stat
                                       (fn-nntp-string-octets "0"))
             (fn-nntp-article-response *nlc-t-open* *nlc-t-art2* 0 :stat t nil))))
(must-fail
 (with-prover-step-limit
  200000
 (defthm nlc-t-number-false-without-positive
   (let* ((article (fn-find-article (fn-nntp-token-string token)
                                    (fn-state-articles archive)))
          (n (fn-nntp-msgid-local-number session article)))
     (implies (and (fn-statep archive)
                   (fn-nntp-number-tokenp number-token)
                   (equal (fn-nntp-decimal-value number-token) n))
              (equal (fn-nntp-number-retrieval session archive kind number-token)
                     (fn-nntp-article-response
                      session article n kind t
                      (fn-nntp-session-group session))))))))

; Hypotheses 3 and 4 (the token reads as n): a token for another number
; retrieves another article; a token that is not a number is 501.
(assert-event
 (not (equal (fn-nntp-number-retrieval (nlc-t-in "fn.letters") *nlc-t-a2* :stat
                                       (fn-nntp-string-octets "1"))
             (fn-nntp-article-response (nlc-t-in "fn.letters") *nlc-t-art2* 2
                                       :stat t "fn.letters"))))
(must-fail
 (with-prover-step-limit
  200000
 (defthm nlc-t-number-false-without-value
   (let* ((article (fn-find-article (fn-nntp-token-string token)
                                    (fn-state-articles archive)))
          (n (fn-nntp-msgid-local-number session article)))
     (implies (and (fn-statep archive) (posp n)
                   (fn-nntp-number-tokenp number-token))
              (equal (fn-nntp-number-retrieval session archive kind number-token)
                     (fn-nntp-article-response
                      session article n kind t
                      (fn-nntp-session-group session))))))))
(assert-event
 (equal (fn-nntp-number-retrieval (nlc-t-in "fn.letters") *nlc-t-a2* :stat
                                  (fn-nntp-string-octets "2x"))
        (fn-nntp-single (nlc-t-in "fn.letters") "501 syntax error")))
(must-fail
 (with-prover-step-limit
  200000
 (defthm nlc-t-number-false-without-token
   (let* ((article (fn-find-article (fn-nntp-token-string token)
                                    (fn-state-articles archive)))
          (n (fn-nntp-msgid-local-number session article)))
     (implies (and (fn-statep archive) (posp n)
                   (equal (fn-nntp-decimal-value number-token) n))
              (equal (fn-nntp-number-retrieval session archive kind number-token)
                     (fn-nntp-article-response
                      session article n kind t
                      (fn-nntp-session-group session))))))))
