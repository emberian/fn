; Witnesses and teeth for books/reclaim-rule, books/store-reclaim and the
; served projection in books/nntp-responses (D13, STO-014, PRF-088).
(in-package "ACL2")
(include-book "../../books/store-reclaim")
(include-book "../../books/nntp-reclaimed")
(include-book "std/testing/must-fail" :dir :system)

; Two stored articles in group "g", numbers 1 and 2, stamped at second 100.
(defconst *rt-p1* '(72 58 32 120 13 10 13 10 98 111 100 121))   ; "H: x" CRLF CRLF "body"
(defconst *rt-p2* '(72 58 32 121 13 10 13 10 99))
(defconst *rt-a1* (fn-make-article "<a1@x>" *rt-p1* '("g") '(("g" . 1)) t 100))
(defconst *rt-a2* (fn-make-article "<a2@x>" *rt-p2* '("g") '(("g" . 2)) t 100))
(defconst *rt-arts* (list *rt-a2* *rt-a1*))
(defconst *rt-s* (fn-make-state '("g") '(("g" . 3)) *rt-arts* 2 nil nil))
(defconst *rt-tomb* (fn-rcl-tombstone-of *rt-p1* (fn-record-string-octets "<a1@x>")))
(defconst *rt-rall* '(:released-by-all-holders))
(defconst *rt-none* (list nil nil nil nil))
(defconst *rt-pin* (list '(("g" . 1)) nil nil nil))
(defconst *rt-cursor* (list nil '(("g" . 0)) nil nil))
(defconst *rt-cursor-past* (list nil '(("g" . 1)) nil nil))
(defconst *rt-feed* (list nil nil '(("peer" nil "<a1@x>")) nil))
(defconst *rt-feed-retired* (list nil nil '(("peer" t "<a1@x>")) nil))
(defconst *rt-bp* (list nil nil nil '("<a1@x>")))

(assert-event (fn-statep *rt-s*))
(assert-event (fn-rcl-tombstonep *rt-tomb*))
(assert-event (not (fn-rcl-tombstonep *rt-p1*)))

; --- The rule (fn-rcl-config-rule-after-retention-set).
(defconst *rt-v0* (fn-cfg-empty-value))
(assert-event (equal (fn-rcl-config-rule *rt-v0*) '(:keep-forever)))
(assert-event (fn-rcl-rulep '(:release-after 30)))
(assert-event (equal (fn-rcl-config-rule
                      (fn-cfg-apply *rt-v0* 1 nil (fn-rcl-rule-deltas '(:release-after 30))))
                     '(:release-after 30)))
; A second `retention set' replaces the first, days row included.
(assert-event (equal (fn-rcl-config-rule
                      (fn-cfg-apply
                       (fn-cfg-apply *rt-v0* 1 nil (fn-rcl-rule-deltas '(:release-after 30)))
                       2 nil (fn-rcl-rule-deltas *rt-rall*)))
                     *rt-rall*))
(assert-event (equal (fn-rcl-rule-of-words "release-after" 7) '(:release-after 7)))
(assert-event (equal (fn-rcl-rule-of-words "release-after" 0) nil))
; Tooth: without (fn-rcl-rulep rule) -- a zero-day rule stages nothing, and
; the configuration still reads keep-forever.
(assert-event (not (fn-rcl-rulep '(:release-after 0))))
(must-fail (assert-event (equal (fn-rcl-config-rule
                                 (fn-cfg-apply *rt-v0* 1 nil
                                               (fn-rcl-rule-deltas '(:release-after 0))))
                                '(:release-after 0))))
; Tooth for fn-rcl-config-rule-without-a-row-keeps-forever: with a row.
(defconst *rt-v1* (fn-cfg-apply *rt-v0* 1 nil (fn-rcl-rule-deltas *rt-rall*)))
(assert-event (fn-rcl-limit-row (fn-cfg-limits *rt-v1*) *fn-rcl-rule-slot*))
(must-fail (assert-event (equal (fn-rcl-config-rule *rt-v1*) '(:keep-forever))))

; --- The decision (fn-rcl-reclaimable-is-no-obligation-names-it): both sides.
(defmacro rt-both (rule now h verdicts article expect)
  `(assert-event
    (and (equal (fn-rcl-reclaimable ,rule ,now ,h ,verdicts ,article) ,expect)
         (equal (and (not (fn-rcl-tombstonep (fn-article-payload ,article)))
                     (not (equal ,rule '(:keep-forever)))
                     (fn-rcl-rulep ,rule)
                     (fn-rcl-rule-permits ,rule ,now (fn-article-stamp ,article))
                     (not (fn-rcl-verdict-heldp (fn-article-msgid ,article) ,verdicts))
                     (not (fn-rcl-some-names-p (fn-rcl-obligations ,h)
                                               (fn-article-msgid ,article)
                                               (fn-article-memberships ,article))))
                ,expect))))
(rt-both *rt-rall* 0 *rt-none* nil *rt-a1* t)
(rt-both *rt-rall* 0 *rt-pin* nil *rt-a1* nil)
(rt-both *rt-rall* 0 *rt-pin* nil *rt-a2* t)
(rt-both *rt-rall* 0 *rt-cursor* nil *rt-a1* nil)
(rt-both *rt-rall* 0 *rt-cursor-past* nil *rt-a1* t)
(rt-both *rt-rall* 0 *rt-cursor-past* nil *rt-a2* nil)
(rt-both *rt-rall* 0 *rt-feed* nil *rt-a1* nil)
(rt-both *rt-rall* 0 *rt-feed-retired* nil *rt-a1* t)
(rt-both *rt-rall* 0 *rt-bp* nil *rt-a1* nil)
(rt-both '(:keep-forever) 0 *rt-none* nil *rt-a1* nil)
(rt-both '(:release-after 1) (+ 100 86400) *rt-none* nil *rt-a1* t)
(rt-both '(:release-after 1) (+ 100 86399) *rt-none* nil *rt-a1* nil)
(rt-both *rt-rall* 0 *rt-none* '(("<a1@x>" . :valid)) *rt-a1* nil)
(assert-event (equal (fn-rcl-verdict *rt-rall* 0 *rt-feed* nil *rt-a1*) :held-feed))
(assert-event (equal (fn-rcl-plan *rt-rall* 0 *rt-pin* nil *rt-arts*)
                     '(("<a2@x>" . :reclaimable) ("<a1@x>" . :held-reader-pin))))

; --- What reclamation keeps.
(defconst *rt-s1* (fn-rcl-reclaim-state *rt-s* "<a1@x>" *rt-tomb*))
(assert-event (fn-octet-listp *rt-tomb*))
(assert-event (fn-statep *rt-s1*))                      ; preserves-statep
(assert-event (fn-acceptedp "<a1@x>" (fn-state-articles *rt-s1*)))   ; history
(assert-event (equal (fn-state-nexts *rt-s1*) (fn-state-nexts *rt-s*)))
(assert-event (equal (fn-article-memberships (fn-find-article "<a1@x>" (fn-state-articles *rt-s1*)))
                     '(("g" . 1))))
(assert-event (equal (fn-article-payload (fn-find-article "<a1@x>" (fn-state-articles *rt-s1*)))
                     *rt-tomb*))
(assert-event (equal (fn-find-article "<a2@x>" (fn-state-articles *rt-s1*)) *rt-a2*))
; The reclaimed Message-ID cannot be staged again: prepare refuses it.
(assert-event (equal (fn-accept-prepare *rt-s1* 0 "<a1@x>" *rt-p1* '("g") 200) *rt-s1*))
; Tooth for fn-rcl-reclaim-preserves-statep: a non-state stays a non-state.
(must-fail (assert-event (fn-statep (fn-rcl-reclaim-state 7 "<a1@x>" *rt-tomb*))))

; fn-rcl-prepare-commutes-with-reclaim: a new article staged either way.
(assert-event (equal (fn-accept-prepare *rt-s1* 0 "<a3@x>" *rt-p2* '("g") 200)
                     (fn-rcl-reclaim-state
                      (fn-accept-prepare *rt-s* 0 "<a3@x>" *rt-p2* '("g") 200)
                      "<a1@x>" *rt-tomb*)))
; Tooth: without (fn-statep s).  An article whose payload is not octets
; makes a non-state; reclaiming it repairs the payload, and the two orders
; then differ.
(defconst *rt-bad* (fn-make-state '("g") '(("g" . 3))
                                  (list *rt-a2* (fn-make-article "<a1@x>" 'x '("g") '(("g" . 1)) t 100))
                                  2 nil nil))
(assert-event (not (fn-statep *rt-bad*)))
(must-fail (assert-event (equal (fn-accept-prepare (fn-rcl-reclaim-state *rt-bad* "<a1@x>" *rt-tomb*)
                                                   0 "<a3@x>" *rt-p2* '("g") 200)
                                (fn-rcl-reclaim-state
                                 (fn-accept-prepare *rt-bad* 0 "<a3@x>" *rt-p2* '("g") 200)
                                 "<a1@x>" *rt-tomb*))))

; fn-rcl-reclaim-never-touches-a-held-article: a pinned article, unchanged.
(assert-event (equal (fn-rcl-reclaim-if-permitted *rt-s* *rt-rall* 0 *rt-pin* nil "<a1@x>" *rt-tomb*)
                     *rt-s*))
(assert-event (equal (fn-rcl-reclaim-if-permitted *rt-s* '(:keep-forever) 0 *rt-none* nil "<a1@x>" *rt-tomb*)
                     *rt-s*))
; Tooth: with neither hypothesis (no holder, a releasing rule) it changes.
(must-fail (assert-event (equal (fn-rcl-reclaim-if-permitted *rt-s* *rt-rall* 0 *rt-none* nil
                                                             "<a1@x>" *rt-tomb*)
                                *rt-s*)))

; --- D25 after reclamation (fn-rcl-existing-action-after-reclaim).
(defconst *rt-arts1* (fn-rcl-reclaim-articles *rt-arts* "<a1@x>" *rt-tomb*))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g") *rt-arts*) :duplicate))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g") *rt-arts1*) :duplicate))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p2* '("g") *rt-arts*) :conflict))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p2* '("g") *rt-arts1*) :conflict))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("h") *rt-arts1*) :conflict))
(assert-event (equal (fn-rcl-action-over "<a9@x>" *rt-p1* '("g") *rt-arts1*) nil))
; Tooth: without (not (fn-rcl-tombstonep held)) -- reclaiming a tombstone
; again digests the tombstone, and the resend of the original becomes a
; conflict with no collision in sight.
(defconst *rt-t2* (fn-rcl-tombstone-of *rt-tomb* (fn-record-string-octets "<a1@x>")))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g") *rt-arts1*) :duplicate))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g")
                                         (fn-rcl-reclaim-articles *rt-arts1* "<a1@x>" *rt-t2*))
                     :conflict))
(assert-event (not (fn-rcl-collisionp *rt-p1* *rt-tomb*)))
(must-fail (assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g")
                                                    (fn-rcl-reclaim-articles *rt-arts1* "<a1@x>" *rt-t2*))
                                (fn-rcl-action-over "<a1@x>" *rt-p1* '("g") *rt-arts1*))))

; --- The served projection (fn-nntp-reclaimed-article-answers-reclaimed).
(defconst *rt-session* (fn-nntp-make-session t "g" nil t))
(defconst *rt-r1* (fn-find-article "<a1@x>" (fn-state-articles *rt-s1*)))
(assert-event (fn-nntp-article-idp *rt-r1*))
(assert-event (equal (fn-nntp-article-response *rt-session* *rt-r1* 0 :article nil nil)
                     (fn-nntp-single *rt-session* "430 article reclaimed")))
(assert-event (equal (fn-nntp-article-response *rt-session* *rt-r1* 1 :body t "g")
                     (fn-nntp-single *rt-session* "423 article reclaimed")))
; Teeth: a live article is served; an article with no usable identifier is 503.
(must-fail (assert-event (equal (fn-nntp-article-response *rt-session* *rt-a1* 1 :article t "g")
                                (fn-nntp-single *rt-session* "423 article reclaimed"))))
(defconst *rt-noid* (fn-make-article "no-angle" *rt-tomb* '("g") '(("g" . 1)) t 100))
(assert-event (not (fn-nntp-article-idp *rt-noid*)))
(must-fail (assert-event (equal (fn-nntp-article-response *rt-session* *rt-noid* 1 :article t "g")
                                (fn-nntp-single *rt-session* "423 article reclaimed"))))

; fn-nntp-number-retrieval-answers-reclaimed: ARTICLE 1 in "g".
(defconst *rt-tok1* '(49))
(assert-event (and (fn-nntp-number-tokenp *rt-tok1*)
                   (fn-nntp-session-group *rt-session*)
                   (consp *rt-r1*)
                   (equal (fn-nntp-find-group-number "g" 1 (fn-state-articles *rt-s1*)) *rt-r1*)))
(assert-event (equal (fn-nntp-number-retrieval *rt-session* *rt-s1* :article *rt-tok1*)
                     (fn-nntp-single *rt-session* "423 article reclaimed")))
; Tooth (tombstone hypothesis): article 2 is live and is not answered so.
(must-fail (assert-event (equal (fn-nntp-number-retrieval *rt-session* *rt-s1* :article '(50))
                                (fn-nntp-single *rt-session* "423 article reclaimed"))))
; Tooth (a selected group): with none, 412.
(must-fail (assert-event (equal (fn-nntp-number-retrieval (fn-nntp-make-session t nil nil t)
                                                          *rt-s1* :article *rt-tok1*)
                                (fn-nntp-single *rt-session* "423 article reclaimed"))))
; By Message-ID over the scan the indexed lookup refines: 430.
(assert-event (equal (fn-nntp-msgid-retrieval *rt-session* *rt-s1* :article
                                              (fn-record-string-octets "<a1@x>"))
                     (fn-nntp-single *rt-session* "430 article reclaimed")))
(must-fail (assert-event (equal (fn-nntp-msgid-retrieval *rt-session* *rt-s1* :article
                                                         (fn-record-string-octets "<a2@x>"))
                                (fn-nntp-single *rt-session* "430 article reclaimed"))))

; --- OVER and NEWNEWS drop a reclaimed article (lane reclaim-host).
; A store with two whole articles in "g": 1 reclaimed, 2 live.
(defun rt-crlf-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) '(13 10) (rt-crlf-lines (cdr lines)))
    nil))
(defconst *rt-w1* (rt-crlf-lines '("From: a@example.invalid" "Subject: one"
                                   "Date: Thu, 24 Sep 2026 10:00:00 +0000"
                                   "Message-ID: <w1@x>" "Newsgroups: g" "" "body one")))
(defconst *rt-w2* (rt-crlf-lines '("From: a@example.invalid" "Subject: two"
                                   "Date: Thu, 24 Sep 2026 10:00:01 +0000"
                                   "Message-ID: <w2@x>" "Newsgroups: g" "" "body two")))
(defconst *rt-wa1* (fn-make-article "<w1@x>" *rt-w1* '("g") '(("g" . 1)) t 100))
(defconst *rt-wa2* (fn-make-article "<w2@x>" *rt-w2* '("g") '(("g" . 2)) t 101))
(defconst *rt-wtomb* (fn-rcl-tombstone-of *rt-w1* (fn-record-string-octets "<w1@x>")))
(defconst *rt-warts* (fn-rcl-reclaim-articles (list *rt-wa2* *rt-wa1*) "<w1@x>" *rt-wtomb*))
(defconst *rt-ws* (fn-make-state '("g") '(("g" . 3)) *rt-warts* 2 nil nil))
(defconst *rt-wr1* (fn-find-article "<w1@x>" *rt-warts*))
(assert-event (and (fn-rcl-tombstonep (fn-article-payload *rt-wr1*))
                   (fn-nov-okp (fn-nov-overview *rt-wa1*))
                   (fn-nov-okp (fn-nov-overview *rt-wa2*))))

; fn-nntp-over-by-msgid-answers-reclaimed, and its teeth.
(defconst *rt-wid1* (fn-record-string-octets "<w1@x>"))
(assert-event (and (fn-nntp-message-id-tokenp *rt-wid1*)
                   (equal (fn-nntp-over-response *rt-session* *rt-ws* (list *rt-wid1*))
                          (fn-nntp-single *rt-session* "430 article reclaimed"))))
; Before reclamation the same command is answered with the overview.
(assert-event (equal (car (fn-nntp-over-response
                           *rt-session*
                           (fn-make-state '("g") '(("g" . 3)) (list *rt-wa2* *rt-wa1*) 2 nil nil)
                           (list *rt-wid1*)))
                     (car (fn-nntp-multi *rt-session* "224 overview information follows" nil))))
; Tooth (tombstone): the live article 2.
(must-fail (assert-event (equal (fn-nntp-over-response *rt-session* *rt-ws*
                                                       (list (fn-record-string-octets "<w2@x>")))
                                (fn-nntp-single *rt-session* "430 article reclaimed"))))
; Tooth (a Message-ID token): the number token 1 is a range.
(must-fail (assert-event (equal (fn-nntp-over-response *rt-session* *rt-ws* (list '(49)))
                                (fn-nntp-single *rt-session* "430 article reclaimed"))))
; Tooth (the article is held): an unknown Message-ID.
(must-fail (assert-event (equal (fn-nntp-over-response *rt-session* *rt-ws*
                                                       (list (fn-record-string-octets "<zz@x>")))
                                (fn-nntp-single *rt-session* "430 article reclaimed"))))

; fn-nntp-over-current-answers-reclaimed, and its teeth.
(defconst *rt-cur1* (fn-nntp-make-session t "g" 1 t))
(assert-event (equal (fn-nntp-over-response *rt-cur1* *rt-ws* nil)
                     (fn-nntp-single *rt-cur1* "423 article reclaimed")))
(must-fail (assert-event (equal (fn-nntp-over-response (fn-nntp-make-session t "g" 2 t) *rt-ws* nil)
                                (fn-nntp-single (fn-nntp-make-session t "g" 2 t)
                                                "423 article reclaimed"))))
(must-fail (assert-event (equal (fn-nntp-over-response (fn-nntp-make-session t nil 1 t) *rt-ws* nil)
                                (fn-nntp-single (fn-nntp-make-session t nil 1 t)
                                                "423 article reclaimed"))))
(must-fail (assert-event (equal (fn-nntp-over-response (fn-nntp-make-session t "g" nil t) *rt-ws* nil)
                                (fn-nntp-single (fn-nntp-make-session t "g" nil t)
                                                "423 article reclaimed"))))
(must-fail (assert-event (equal (fn-nntp-over-response (fn-nntp-make-session t "g" 7 t) *rt-ws* nil)
                                (fn-nntp-single (fn-nntp-make-session t "g" 7 t)
                                                "423 article reclaimed"))))

; fn-nov-lines-skip-a-reclaimed-article: range 1-2 gives the one line of 2.
(assert-event (equal (len (fn-nov-lines-for-numbers "g" '(1 2) *rt-warts*)) 1))
(assert-event (equal (fn-nov-lines-for-numbers "g" '(1 2) *rt-warts*)
                     (fn-nov-lines-for-numbers "g" '(2) *rt-warts*)))
; Tooth (tombstone): removing the live 2 changes the lines.
(must-fail (assert-event (equal (fn-nov-lines-for-numbers "g" '(1 2) *rt-warts*)
                                (fn-nov-lines-for-numbers "g" '(1) *rt-warts*))))

; fn-nntp-newnews-scan-lists-only-live-articles: 2 is listed, 1 is not,
; though 1 is a candidate and new.
(defconst *rt-nn* (fn-nntp-newnews-scan '("g") 0 *rt-warts* :none))
(assert-event (and (equal *rt-nn* (list (fn-nntp-string-octets "<w2@x>")))
                   (fn-nntp-newnews-candidatep '("g") *rt-wr1*)
                   (fn-nntp-newnews-newp 0 100 :none)
                   (equal (fn-nntp-newnews-live-ids *rt-warts*) *rt-nn*)))
; Tooth (membership in the scan): the reclaimed id is not a live id.
(must-fail (assert-event (member-equal (fn-nntp-string-octets "<w1@x>")
                                       (fn-nntp-newnews-live-ids *rt-warts*))))
