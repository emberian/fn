; fn: the served projection of a reclaimed article (D13, STO-014, PRF-088).
;
; fn-nntp-step (books/nntp) answers ARTICLE, HEAD, BODY and STAT by
; Message-ID through `fn-nntp-msgid-retrieval-indexed' and by number through
; `fn-nntp-number-retrieval'; both reach `fn-nntp-article-response', whose
; tombstone branch (books/nntp-responses) answers "article reclaimed".
; These two theorems are stated of the functions the step calls, so a
; reclaimed article is answered 430 by Message-ID and 423 by number however
; the lookup found it, and the session is unchanged.
(in-package "ACL2")
(include-book "nntp-responses")

;  KEYSTONE.  By Message-ID: when the served index corresponds to the
; archive (the invariant the connection carries) and the article the token
; names is a tombstone, the answer is 430 article reclaimed.
(defthm fn-nntp-msgid-retrieval-answers-reclaimed
  (let ((article (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive))))
    (implies (and (fn-midx-correspondencep index (fn-state-articles archive))
                  (fn-nntp-message-id-tokenp token)
                  (consp article)
                  (fn-nntp-article-idp article)
                  (fn-rcl-tombstonep (fn-article-payload article)))
             (equal (fn-nntp-msgid-retrieval-indexed session archive index kind token)
                    (fn-nntp-single session "430 article reclaimed"))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-msgid-retrieval)
                                  (fn-rcl-tombstonep fn-nntp-article-idp
                                   fn-nntp-article-response))
                  :use (fn-nntp-msgid-retrieval-indexed-refines-scan
                        (:instance fn-nntp-reclaimed-article-answers-reclaimed
                                   (article (fn-find-article
                                             (fn-nntp-token-string token)
                                             (fn-state-articles archive)))
                                   (number (fn-nntp-msgid-local-number
                                            session
                                            (fn-find-article
                                             (fn-nntp-token-string token)
                                             (fn-state-articles archive))))
                                   (updatep nil) (group nil))))))

;  KEYSTONE.  By number in the selected group: 423 article reclaimed.
(defthm fn-nntp-number-retrieval-answers-reclaimed
  (let ((article (fn-nntp-find-group-number (fn-nntp-session-group session)
                                            (fn-nntp-decimal-value token)
                                            (fn-state-articles archive))))
    (implies (and (fn-nntp-number-tokenp token)
                  (fn-nntp-session-group session)
                  (consp article)
                  (fn-nntp-article-idp article)
                  (fn-rcl-tombstonep (fn-article-payload article)))
             (equal (fn-nntp-number-retrieval session archive kind token)
                    (fn-nntp-single session "423 article reclaimed"))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-number-retrieval)
                                  (fn-rcl-tombstonep fn-nntp-article-idp
                                   fn-nntp-article-response))
                  :use ((:instance fn-nntp-reclaimed-article-answers-reclaimed
                                   (article (fn-nntp-find-group-number
                                             (fn-nntp-session-group session)
                                             (fn-nntp-decimal-value token)
                                             (fn-state-articles archive)))
                                   (number (fn-nntp-decimal-value token))
                                   (updatep t)
                                   (group (fn-nntp-session-group session)))))))
