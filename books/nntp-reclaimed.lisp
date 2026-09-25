; fn: the served projection of a reclaimed article (D13, STO-014, PRF-088).
;
; OVER, XOVER and NEWNEWS drop a reclaimed article (the second half,
; lane reclaim-host): OVER by Message-ID answers 430 and OVER of the current
; article 423 "article reclaimed" (`fn-nntp-over-response', which
; `fn-nntp-archive-command' calls, books/nntp.lisp); a range skips it
; (`fn-nov-lines-for-numbers-indexed', which the pinned dispatcher's
; `fn-nntp-over-range-indexed' calls, and `fn-nov-lines-for-numbers', the
; unpinned OVER/XOVER range); NEWNEWS never lists it
; (`fn-nntp-newnews-scan', which `fn-nntp-newnews-response' calls).
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
(include-book "nntp-range-indexed")

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

; -----------------------------------------------------------------------------
; OVER and NEWNEWS

; A Message-ID token opens with `<', which no range token contains.
(encapsulate ()
(local (defthm rh-decimal-token-no-lt
  (implies (member-equal 60 x) (not (fn-nntp-decimal-tokenp x)))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))
(local (defthm rh-number-token-no-lt
  (implies (member-equal 60 x) (not (fn-nntp-number-tokenp x)))
  :hints (("Goal" :in-theory (enable fn-nntp-number-tokenp)))))
(local (include-book "std/lists/reverse" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (defthm rh-member-rev
  (iff (member-equal a (rev x)) (member-equal a x))
  :hints (("Goal" :in-theory (enable rev)))))
(local (defthm rh-aux-not-ok
  (implies (member-equal 60 prefix-rev)
           (not (equal (car (fn-nntp-range-parse-aux token prefix-rev)) :ok)))
  :hints (("Goal" :induct (fn-nntp-range-parse-aux token prefix-rev)
                  :in-theory (enable fn-nntp-range-parse-aux)))))
(defthm fn-nntp-reclaimed-msgid-token-is-no-range
   (implies (fn-nntp-message-id-tokenp token)
            (not (fn-nntp-range-okp (fn-nntp-parse-range token))))
   :hints (("Goal" :in-theory (enable fn-nntp-message-id-tokenp fn-nntp-parse-range
                                      fn-nntp-range-okp)
                   :expand ((fn-nntp-range-parse-aux token nil))))))


;  KEYSTONE.  OVER <message-id> of a reclaimed article: 430 article reclaimed.
(defthm fn-nntp-over-by-msgid-answers-reclaimed
  (let ((article (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive))))
    (implies (and (fn-nntp-message-id-tokenp token)
                  (consp article)
                  (fn-rcl-tombstonep (fn-article-payload article)))
             (equal (fn-nntp-over-response session archive (list token))
                    (fn-nntp-single session "430 article reclaimed"))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-response fn-nntp-over-msgid)
                                  (fn-rcl-tombstonep fn-nntp-message-id-tokenp
                                   fn-nntp-parse-range fn-nntp-range-okp)))))

;  KEYSTONE.  OVER with no argument when the current article was reclaimed:
; 423 article reclaimed.
(defthm fn-nntp-over-current-answers-reclaimed
  (let ((article (fn-nntp-available-article (fn-nntp-session-group session)
                                            (fn-nntp-session-current session)
                                            (fn-state-articles archive))))
    (implies (and (fn-nntp-session-group session)
                  (fn-nntp-session-current session)
                  (consp article)
                  (fn-rcl-tombstonep (fn-article-payload article)))
             (equal (fn-nntp-over-response session archive nil)
                    (fn-nntp-single session "423 article reclaimed"))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-response fn-nntp-over-current)
                                  (fn-rcl-tombstonep)))))

;  KEYSTONE.  A reclaimed article contributes no overview line to a range:
; the lines over NUMBERS are the lines over NUMBERS without its number.
(defthm fn-nov-lines-indexed-skip-a-reclaimed-article
  (implies (fn-rcl-tombstonep
            (fn-article-payload (fn-gidx-entry-number-article group n entries trie)))
           (equal (fn-nov-lines-for-numbers-indexed group numbers entries trie)
                  (fn-nov-lines-for-numbers-indexed group (remove-equal n numbers)
                                                    entries trie)))
  :hints (("Goal" :induct (len numbers)
                  :in-theory (e/d (fn-nov-lines-for-numbers-indexed)
                                  (fn-rcl-tombstonep fn-nov-overview fn-nov-okp
                                   fn-nov-line)))))

(defthm fn-nov-lines-skip-a-reclaimed-article
  (implies (fn-rcl-tombstonep
            (fn-article-payload (fn-nntp-available-article group n articles)))
           (equal (fn-nov-lines-for-numbers group numbers articles)
                  (fn-nov-lines-for-numbers group (remove-equal n numbers) articles)))
  :hints (("Goal" :induct (len numbers)
                  :in-theory (e/d (fn-nov-lines-for-numbers)
                                  (fn-rcl-tombstonep fn-nov-overview fn-nov-okp
                                   fn-nov-line)))))

; The Message-IDs of the articles that are not tombstones, as NEWNEWS
; prints them.
(defun fn-nntp-newnews-live-ids (articles)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp articles)
      (if (fn-rcl-tombstonep (fn-article-payload (car articles)))
          (fn-nntp-newnews-live-ids (cdr articles))
        (cons (fn-nntp-string-octets (fn-article-msgid (car articles)))
              (fn-nntp-newnews-live-ids (cdr articles))))
    nil))

;  KEYSTONE.  Every Message-ID NEWNEWS lists is that of an article that was
; not reclaimed.
(defthm fn-nntp-newnews-scan-lists-only-live-articles
  (implies (member-equal x (fn-nntp-newnews-scan groups threshold articles horizon))
           (member-equal x (fn-nntp-newnews-live-ids articles)))
  :hints (("Goal" :induct (fn-nntp-newnews-scan groups threshold articles horizon)
                  :in-theory (e/d (fn-nntp-newnews-scan)
                                  (fn-rcl-tombstonep fn-nntp-newnews-candidatep
                                   fn-nntp-newnews-newp fn-nntp-string-octets)))))
