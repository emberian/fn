; Witnesses and teeth for books/reclaim-rule, books/store-reclaim and the
; served projection in books/nntp-responses (D13, STO-014, PRF-088).
(in-package "ACL2")
(include-book "../../books/store-reclaim")
(include-book "../../books/nntp-reclaimed")
(include-book "must-fail-checked")
(include-book "held-rows-tests")

; Two stored articles in group "g", numbers 1 and 2, stamped at second 100.
(defconst *rt-p1* '(72 58 32 120 13 10 13 10 98 111 100 121))   ; "H: x" CRLF CRLF "body"
(defconst *rt-p2* '(72 58 32 121 13 10 13 10 99))
; After the flip (records-flip) an acceptance article's payload is a HANDLE
; into the arena, and reclamation writes the sealed tombstone under a new
; handle (books/store-reclaim.lisp).  The arena here holds, in order, the
; bytes of a1 (handle 0), a2 (handle 1), a1's tombstone (handle 2) and the
; payload of a later article a3 (handle 3); it is built by interning wire
; records that carry them.  The -wire articles are the pre-flip octet
; articles, which alpha of the handle articles must reproduce.
(defconst *rt-tomb-octets* (fn-rcl-tombstone-of *rt-p1* (fn-record-string-octets "<a1@x>")))
(defun rt-carrier (i msgid payload)
  (fn-record-make i i i msgid payload '("g") "rt-pin" "rt-subject" "rt-release" 1 841000000))
(defconst *rt-prior*
  (list (rt-carrier 0 "<a1@x>" *rt-p1*) (rt-carrier 1 "<a2@x>" *rt-p2*)
        (rt-carrier 2 "<a1-tomb@x>" *rt-tomb-octets*) (rt-carrier 3 "<a3@x>" *rt-p2*)))
(assert-event (equal (fn-hrt-bytes *rt-prior* 0) *rt-p1*))
(assert-event (equal (fn-hrt-bytes *rt-prior* 1) *rt-p2*))
(assert-event (equal (fn-hrt-bytes *rt-prior* 2) *rt-tomb-octets*))
(defconst *rt-a1-wire* (fn-make-article "<a1@x>" *rt-p1* '("g") '(("g" . 1)) t 100))
(defconst *rt-a2-wire* (fn-make-article "<a2@x>" *rt-p2* '("g") '(("g" . 2)) t 100))
(defconst *rt-arts-wire* (list *rt-a2-wire* *rt-a1-wire*))
(defconst *rt-a1* (fn-make-article "<a1@x>" 0 '("g") '(("g" . 1)) t 100))
(defconst *rt-a2* (fn-make-article "<a2@x>" 1 '("g") '(("g" . 2)) t 100))
(defconst *rt-arts* (list *rt-a2* *rt-a1*))
(assert-event (equal (fn-hrt-articles-wire-of *rt-prior* *rt-arts*) *rt-arts-wire*))
(defconst *rt-s* (fn-make-state '("g") '(("g" . 3)) *rt-arts* 2 nil nil))
(defconst *rt-tomb* 2)
; The handle of the payload a later article offers (bytes *rt-p2*).
(defconst *rt-h3* 3)
(defconst *rt-rall* '(:released-by-all-holders))
(defconst *rt-none* (list nil nil nil nil))
(defconst *rt-pin* (list '(("g" . 1)) nil nil nil))
(defconst *rt-cursor* (list nil '(("g" . 0)) nil nil))
(defconst *rt-cursor-past* (list nil '(("g" . 1)) nil nil))
; FEEDS and BP are keyed by Message-ID (books/store-reclaim): (msgid . peer)
; and (msgid . subject).  A retired peer's queue is not in the slot (its
; producer, books/store-reclaim-owner-holders, reads the live table); a feed
; owing another article holds nothing here.
(defconst *rt-feed* (list nil nil '(("<a1@x>" . "peer")) nil))
(defconst *rt-feed-other* (list nil nil '(("<a9@x>" . "peer")) nil))
(defconst *rt-bp* (list nil nil nil '(("<a1@x>" . "subject-a1"))))

(assert-event (fn-statep *rt-s*))
(assert-event (fn-rcl-tombstonep *rt-tomb-octets*))
(assert-event (fn-rcl-tombstonep (fn-hrt-bytes *rt-prior* *rt-tomb*)))
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
(must-fail-checked (assert-event (equal (fn-rcl-config-rule
                                 (fn-cfg-apply *rt-v0* 1 nil
                                               (fn-rcl-rule-deltas '(:release-after 0))))
                                '(:release-after 0))))
; Tooth for fn-rcl-config-rule-without-a-row-keeps-forever: with a row.
(defconst *rt-v1* (fn-cfg-apply *rt-v0* 1 nil (fn-rcl-rule-deltas *rt-rall*)))
(assert-event (fn-rcl-limit-row (fn-cfg-limits *rt-v1*) *fn-rcl-rule-slot*))
(must-fail-checked (assert-event (equal (fn-rcl-config-rule *rt-v1*) '(:keep-forever))))

; --- The decision (fn-rcl-reclaimable-is-no-obligation-names-it): both sides.
(defmacro rt-both (rule now h verdicts article expect)
  `(assert-event
    (and (equal (fn-rcl-reclaimable ,rule ,now ,h ,verdicts ,article) ,expect)
         (equal (and (not (equal ,rule '(:keep-forever)))
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
(rt-both *rt-rall* 0 *rt-feed-other* nil *rt-a1* t)
(rt-both *rt-rall* 0 *rt-bp* nil *rt-a1* nil)
(rt-both '(:keep-forever) 0 *rt-none* nil *rt-a1* nil)
(rt-both '(:release-after 1) (+ 100 86400) *rt-none* nil *rt-a1* t)
(rt-both '(:release-after 1) (+ 100 86399) *rt-none* nil *rt-a1* nil)
(rt-both *rt-rall* 0 *rt-none* '(("<a1@x>" . :valid)) *rt-a1* nil)
(assert-event (equal (fn-rcl-verdict *rt-rall* 0 *rt-feed* nil *rt-a1*) :held-feed))
; fn-rcl-verdict-reclaimable-by-definition (PKT-858): the octet model's
; verdict tests the tombstone on the payload's OCTETS; fn-rcl-reclaimable
; (the standing verdict) reads no payload -- its caller tests the octets it
; holds.  An octet article whose payload is a tombstone: :already-reclaimed,
; though nothing holds it.
(defconst *rt-a1-tomb*
  (fn-make-article (fn-article-msgid *rt-a1*) (fn-hrt-bytes *rt-prior* *rt-tomb*)
                   (fn-article-groups *rt-a1*) (fn-article-memberships *rt-a1*)
                   (fn-article-pin *rt-a1*) (fn-article-stamp *rt-a1*)))
(assert-event (fn-rcl-tombstonep (fn-article-payload *rt-a1-tomb*)))
(assert-event (equal (fn-rcl-verdict *rt-rall* 0 *rt-none* nil *rt-a1-tomb*) :already-reclaimed))
(assert-event (fn-rcl-reclaimable *rt-rall* 0 *rt-none* nil *rt-a1-tomb*))
(assert-event (equal (fn-rcl-verdict *rt-rall* 0 *rt-none* nil *rt-a1*) :reclaimable))
; Mutation: the model verdict does not answer :reclaimable for the tombstone.
(must-fail-checked (assert-event (equal (fn-rcl-verdict *rt-rall* 0 *rt-none* nil *rt-a1-tomb*)
                                        :reclaimable)))
; The retained article (a HANDLE payload) has the same standing verdict as
; its octet model: the standing verdict reads no payload.
(assert-event (equal (fn-rcl-standing-verdict *rt-rall* 0 *rt-pin* nil *rt-a1*)
                     (fn-rcl-standing-verdict *rt-rall* 0 *rt-pin* nil *rt-a1-tomb*)))
(assert-event (equal (fn-rcl-plan *rt-rall* 0 *rt-pin* nil *rt-arts*)
                     '(("<a2@x>" . :reclaimable) ("<a1@x>" . :held-reader-pin))))

; --- What reclamation keeps.
(defconst *rt-s1* (fn-rcl-reclaim-state *rt-s* "<a1@x>" *rt-tomb*))
; by specification: the flip makes the tombstone a handle (fn-rcl-reclaim-state
; acts only on a natp); the bytes under it are the octet tombstone.
(assert-event (natp *rt-tomb*))
(assert-event (fn-octet-listp (fn-hrt-bytes *rt-prior* *rt-tomb*)))
(assert-event (fn-statep *rt-s1*))                      ; preserves-statep
(assert-event (fn-acceptedp "<a1@x>" (fn-state-articles *rt-s1*)))   ; history
(assert-event (equal (fn-state-nexts *rt-s1*) (fn-state-nexts *rt-s*)))
(assert-event (equal (fn-article-memberships (fn-find-article "<a1@x>" (fn-state-articles *rt-s1*)))
                     '(("g" . 1))))
(assert-event (equal (fn-article-payload (fn-find-article "<a1@x>" (fn-state-articles *rt-s1*)))
                     *rt-tomb*))
(assert-event (equal (fn-hrt-bytes *rt-prior*
                                   (fn-article-payload
                                    (fn-find-article "<a1@x>" (fn-state-articles *rt-s1*))))
                     *rt-tomb-octets*))
(assert-event (equal (fn-find-article "<a2@x>" (fn-state-articles *rt-s1*)) *rt-a2*))
; The reclaimed Message-ID cannot be staged again: prepare refuses it.
; by specification: the flip makes the offered payload a handle (a1's bytes
; are under handle 0); a new Message-ID with a handle does stage, so the
; refusal is the Message-ID's.
(assert-event (equal (fn-accept-prepare *rt-s1* 0 "<a1@x>" 0 '("g") 200) *rt-s1*))
(assert-event (not (equal (fn-accept-prepare *rt-s1* 0 "<a3@x>" 0 '("g") 200) *rt-s1*)))
; Tooth for fn-rcl-reclaim-preserves-statep: a non-state stays a non-state.
(must-fail-checked (assert-event (fn-statep (fn-rcl-reclaim-state 7 "<a1@x>" *rt-tomb*))))

; fn-rcl-prepare-commutes-with-reclaim: a new article staged either way.
(assert-event (equal (fn-accept-prepare *rt-s1* 0 "<a3@x>" *rt-h3* '("g") 200)
                     (fn-rcl-reclaim-state
                      (fn-accept-prepare *rt-s* 0 "<a3@x>" *rt-h3* '("g") 200)
                      "<a1@x>" *rt-tomb*)))
; Tooth: without (fn-statep s).  An article whose payload is not octets
; makes a non-state; reclaiming it repairs the payload, and the two orders
; then differ.
(defconst *rt-bad* (fn-make-state '("g") '(("g" . 3))
                                  (list *rt-a2* (fn-make-article "<a1@x>" 'x '("g") '(("g" . 1)) t 100))
                                  2 nil nil))
(assert-event (not (fn-statep *rt-bad*)))
(must-fail-checked (assert-event (equal (fn-accept-prepare (fn-rcl-reclaim-state *rt-bad* "<a1@x>" *rt-tomb*)
                                                   0 "<a3@x>" *rt-h3* '("g") 200)
                                (fn-rcl-reclaim-state
                                 (fn-accept-prepare *rt-bad* 0 "<a3@x>" *rt-h3* '("g") 200)
                                 "<a1@x>" *rt-tomb*))))

; fn-rcl-reclaim-never-touches-a-held-article: a pinned article, unchanged.
(assert-event (equal (fn-rcl-reclaim-if-permitted *rt-s* *rt-rall* 0 *rt-pin* nil "<a1@x>" *rt-tomb*)
                     *rt-s*))
(assert-event (equal (fn-rcl-reclaim-if-permitted *rt-s* '(:keep-forever) 0 *rt-none* nil "<a1@x>" *rt-tomb*)
                     *rt-s*))
; Tooth: with neither hypothesis (no holder, a releasing rule) it changes.
(must-fail-checked (assert-event (equal (fn-rcl-reclaim-if-permitted *rt-s* *rt-rall* 0 *rt-none* nil
                                                             "<a1@x>" *rt-tomb*)
                                *rt-s*)))

; --- D25 after reclamation (fn-rcl-existing-action-after-reclaim).
; The decision compares octets, so it runs over alpha of the articles (the
; host's entry fn-store-existing-action is fn-rcl-action-over over alpha).
; *rt-arts-wire* is alpha of the handle articles, and *rt-arts1* alpha of
; their reclamation under the tombstone handle, which is the octet
; reclamation of the pre-flip articles.
(defconst *rt-arts-handles* *rt-arts*)
(defconst *rt-arts1*
  (fn-hrt-articles-wire-of *rt-prior*
                           (fn-rcl-reclaim-articles *rt-arts-handles* "<a1@x>" *rt-tomb*)))
(assert-event (equal *rt-arts1*
                     (fn-rcl-reclaim-articles *rt-arts-wire* "<a1@x>" *rt-tomb-octets*)))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g") *rt-arts-wire*) :duplicate))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g") *rt-arts1*) :duplicate))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p2* '("g") *rt-arts-wire*) :conflict))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p2* '("g") *rt-arts1*) :conflict))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("h") *rt-arts1*) :conflict))
(assert-event (equal (fn-rcl-action-over "<a9@x>" *rt-p1* '("g") *rt-arts1*) nil))
; Tooth: without (not (fn-rcl-tombstonep held)) -- reclaiming a tombstone
; again digests the tombstone, and the resend of the original becomes a
; conflict with no collision in sight.
(defconst *rt-t2* (fn-rcl-tombstone-of *rt-tomb-octets* (fn-record-string-octets "<a1@x>")))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g") *rt-arts1*) :duplicate))
(assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g")
                                         (fn-rcl-reclaim-articles *rt-arts1* "<a1@x>" *rt-t2*))
                     :conflict))
(assert-event (not (fn-rcl-collisionp *rt-p1* *rt-tomb-octets*)))
; fn-rcl-collisionp's in-domain positive -- two distinct octet lists with one
; BLAKE3 digest -- is a BLAKE3 collision: UNCONSTRUCTIBLE, so no witness over
; octets exists.  OUT-OF-DOMAIN anchor (labelled): fn-blake3 reads any object
; as octets, and NIL and the symbol FOO both read as the empty message, so
; they are distinct and digest alike.  A constantly-false definition fails
; this; it says nothing about octet lists.
(assert-event (and (not (equal nil 'foo))
                   (equal (fn-blake3 nil) (fn-blake3 'foo))
                   (fn-rcl-collisionp nil 'foo)))
(must-fail-checked (assert-event (equal (fn-rcl-action-over "<a1@x>" *rt-p1* '("g")
                                                    (fn-rcl-reclaim-articles *rt-arts1* "<a1@x>" *rt-t2*))
                                (fn-rcl-action-over "<a1@x>" *rt-p1* '("g") *rt-arts1*))))

; --- The served projection (fn-nntp-reclaimed-article-answers-reclaimed).
(defconst *rt-session* (fn-nntp-make-session t "g" nil t))
; The NNTP projection reads article bytes (the tombstone, the overview): it
; is driven here over the served view, alpha of the reclaimed state (the
; handle articles read through the arena); the ring above the store is not
; flipped yet.
(defconst *rt-s1-handles* *rt-s1*)
(defconst *rt-s1-served*
  (fn-make-state (fn-state-groups *rt-s1-handles*) (fn-state-nexts *rt-s1-handles*)
                 (fn-hrt-articles-wire-of *rt-prior* (fn-state-articles *rt-s1-handles*))
                 (fn-state-next-txid *rt-s1-handles*) (fn-state-pending *rt-s1-handles*)
                 (fn-state-fenced *rt-s1-handles*)))
(defconst *rt-r1* (fn-find-article "<a1@x>" (fn-state-articles *rt-s1-served*)))
(assert-event (fn-nntp-article-idp *rt-r1*))
(include-book "arena-lift")
;; The arena: handle 0 = *rt-p1* (a1), 1 = *rt-p2* (a2), 2 = a1's tombstone
;; *rt-tomb-octets*, 3 = *rt-p2* (a3's offer); the bytes of *rt-prior*.
(defconst *sr-arena* (list *rt-p1* *rt-p2* *rt-tomb-octets* *rt-p2*))
(bpr-lift fn-nntp-article-response 6)
(bpr-lift fn-nntp-msgid-retrieval 4)
(bpr-lift fn-nntp-newnews-live-ids 1)
(bpr-lift fn-nntp-newnews-scan 4)
(bpr-lift fn-nntp-number-retrieval 4)
(bpr-lift fn-nntp-over-response 3)
(bpr-lift fn-nov-lines-for-numbers 3)
(bpr-lift fn-nov-overview 1)
(assert-event (equal (in-arena-fn-nntp-article-response *sr-arena* *rt-session* *rt-r1* 0 :article nil nil)
                     (fn-nntp-single *rt-session* "430 article reclaimed")))
(assert-event (equal (in-arena-fn-nntp-article-response *sr-arena* *rt-session* *rt-r1* 1 :body t "g")
                     (fn-nntp-single *rt-session* "423 article reclaimed")))
; Teeth: a live article is served; an article with no usable identifier is 503.
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-article-response *sr-arena* *rt-session* *rt-a1-wire* 1 :article t "g")
                                (fn-nntp-single *rt-session* "423 article reclaimed"))))
(defconst *rt-noid* (fn-make-article "no-angle" *rt-tomb-octets* '("g") '(("g" . 1)) t 100))
(assert-event (not (fn-nntp-article-idp *rt-noid*)))
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-article-response *sr-arena* *rt-session* *rt-noid* 1 :article t "g")
                                (fn-nntp-single *rt-session* "423 article reclaimed"))))

; fn-nntp-number-retrieval-answers-reclaimed: ARTICLE 1 in "g".
(defconst *rt-tok1* '(49))
(assert-event (and (fn-nntp-number-tokenp *rt-tok1*)
                   (fn-nntp-session-group *rt-session*)
                   (consp *rt-r1*)
                   (equal (fn-nntp-find-group-number "g" 1 (fn-state-articles *rt-s1-served*)) *rt-r1*)))
(assert-event (equal (in-arena-fn-nntp-number-retrieval *sr-arena* *rt-session* *rt-s1-served* :article *rt-tok1*)
                     (fn-nntp-single *rt-session* "423 article reclaimed")))
; Tooth (tombstone hypothesis): article 2 is live and is not answered so.
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-number-retrieval *sr-arena* *rt-session* *rt-s1-served* :article '(50))
                                (fn-nntp-single *rt-session* "423 article reclaimed"))))
; Tooth (a selected group): with none, 412.
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-number-retrieval *sr-arena* (fn-nntp-make-session t nil nil t) *rt-s1-served* :article *rt-tok1*)
                                (fn-nntp-single *rt-session* "423 article reclaimed"))))
; By Message-ID over the scan the indexed lookup refines: 430.
(assert-event (equal (in-arena-fn-nntp-msgid-retrieval *sr-arena* *rt-session* *rt-s1-served* :article (fn-record-string-octets "<a1@x>"))
                     (fn-nntp-single *rt-session* "430 article reclaimed")))
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-msgid-retrieval *sr-arena* *rt-session* *rt-s1-served* :article (fn-record-string-octets "<a2@x>"))
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
                   (fn-nov-okp (in-arena-fn-nov-overview *sr-arena* *rt-wa1*))
                   (fn-nov-okp (in-arena-fn-nov-overview *sr-arena* *rt-wa2*))))

; fn-nntp-over-by-msgid-answers-reclaimed, and its teeth.
(defconst *rt-wid1* (fn-record-string-octets "<w1@x>"))
(assert-event (and (fn-nntp-message-id-tokenp *rt-wid1*)
                   (equal (in-arena-fn-nntp-over-response *sr-arena* *rt-session* *rt-ws* (list *rt-wid1*))
                          (fn-nntp-single *rt-session* "430 article reclaimed"))))
; Before reclamation the same command is answered with the overview.
(assert-event (equal (car (in-arena-fn-nntp-over-response *sr-arena* *rt-session* (fn-make-state '("g") '(("g" . 3)) (list *rt-wa2* *rt-wa1*) 2 nil nil) (list *rt-wid1*)))
                     (car (fn-nntp-multi *rt-session* "224 overview information follows" nil))))
; Tooth (tombstone): the live article 2.
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* *rt-session* *rt-ws* (list (fn-record-string-octets "<w2@x>")))
                                (fn-nntp-single *rt-session* "430 article reclaimed"))))
; Tooth (a Message-ID token): the number token 1 is a range.
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* *rt-session* *rt-ws* (list '(49)))
                                (fn-nntp-single *rt-session* "430 article reclaimed"))))
; Tooth (the article is held): an unknown Message-ID.
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* *rt-session* *rt-ws* (list (fn-record-string-octets "<zz@x>")))
                                (fn-nntp-single *rt-session* "430 article reclaimed"))))

; fn-nntp-over-current-answers-reclaimed, and its teeth.
(defconst *rt-cur1* (fn-nntp-make-session t "g" 1 t))
(assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* *rt-cur1* *rt-ws* nil)
                     (fn-nntp-single *rt-cur1* "423 article reclaimed")))
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* (fn-nntp-make-session t "g" 2 t) *rt-ws* nil)
                                (fn-nntp-single (fn-nntp-make-session t "g" 2 t)
                                                "423 article reclaimed"))))
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* (fn-nntp-make-session t nil 1 t) *rt-ws* nil)
                                (fn-nntp-single (fn-nntp-make-session t nil 1 t)
                                                "423 article reclaimed"))))
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* (fn-nntp-make-session t "g" nil t) *rt-ws* nil)
                                (fn-nntp-single (fn-nntp-make-session t "g" nil t)
                                                "423 article reclaimed"))))
(must-fail-checked (assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* (fn-nntp-make-session t "g" 7 t) *rt-ws* nil)
                                (fn-nntp-single (fn-nntp-make-session t "g" 7 t)
                                                "423 article reclaimed"))))

; fn-nov-lines-skip-a-reclaimed-article: range 1-2 gives the one line of 2.
(assert-event (equal (len (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(1 2) *rt-warts*)) 1))
(assert-event (equal (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(1 2) *rt-warts*)
                     (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(2) *rt-warts*)))
; Tooth (tombstone): removing the live 2 changes the lines.
(must-fail-checked (assert-event (equal (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(1 2) *rt-warts*)
                                (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(1) *rt-warts*))))

; fn-nntp-newnews-scan-lists-only-live-articles: 2 is listed, 1 is not,
; though 1 is a candidate and new.
(defconst *rt-nn* (in-arena-fn-nntp-newnews-scan *sr-arena* '("g") 0 *rt-warts* :none))
(assert-event (and (equal *rt-nn* (list (fn-nntp-string-octets "<w2@x>")))
                   (fn-nntp-newnews-candidatep '("g") *rt-wr1*)
                   (fn-nntp-newnews-newp 0 100 :none)
                   (equal (in-arena-fn-nntp-newnews-live-ids *sr-arena* *rt-warts*) *rt-nn*)))
; Tooth (membership in the scan): the reclaimed id is not a live id.
(must-fail-checked (assert-event (member-equal (fn-nntp-string-octets "<w1@x>")
                                       (in-arena-fn-nntp-newnews-live-ids *sr-arena* *rt-warts*))))

; -----------------------------------------------------------------------------
; The served keystones over the FLIPPED store (keystone-audit 2026-09-27): the
; witnesses above drive the served view (octet payloads, the non-handle arm
; of fn-nntp-payload-bytes), so the arena arm the running server takes was
; never exercised.  *rt-s1* is the reclaimed store itself: its articles carry
; arena handles (a1 the tombstone at handle 2, a2 its payload at handle 1),
; read through *sr-arena*.
(bpr-lift fn-nntp-msgid-retrieval-indexed 5)
(bpr-lift fn-nntp-article-tombstonep 1)
(defconst *rt-h-arts* (fn-state-articles *rt-s1*))
(defconst *rt-h-r1* (fn-find-article "<a1@x>" *rt-h-arts*))
(assert-event (and (natp (fn-article-payload *rt-h-r1*))
                   (fn-nntp-article-idp *rt-h-r1*)
                   (in-arena-fn-nntp-article-tombstonep *sr-arena* *rt-h-r1*)))
; fn-nntp-number-retrieval-answers-reclaimed over handles: ARTICLE 1 in "g".
(assert-event (and (fn-nntp-number-tokenp *rt-tok1*)
                   (fn-nntp-session-group *rt-session*)
                   (equal (fn-nntp-find-group-number "g" 1 *rt-h-arts*) *rt-h-r1*)
                   (equal (in-arena-fn-nntp-number-retrieval *sr-arena* *rt-session* *rt-s1* :article *rt-tok1*)
                          (fn-nntp-single *rt-session* "423 article reclaimed"))))
; Tooth (tombstone): the live a2 (handle 1) is not answered so.
(assert-event (and (not (in-arena-fn-nntp-article-tombstonep
                         *sr-arena* (fn-nntp-find-group-number "g" 2 *rt-h-arts*)))
                   (not (equal (in-arena-fn-nntp-number-retrieval *sr-arena* *rt-session* *rt-s1* :article '(50))
                               (fn-nntp-single *rt-session* "423 article reclaimed")))))
; fn-nntp-msgid-retrieval-answers-reclaimed: its subject is the INDEXED
; lookup the host calls; the index is fn-midx-build of the store's articles
; (the correspondence hypothesis asserted).
(defconst *rt-h-index* (fn-midx-build *rt-h-arts*))
(assert-event (and (fn-midx-correspondencep *rt-h-index* *rt-h-arts*)
                   (fn-nntp-message-id-tokenp (fn-record-string-octets "<a1@x>"))
                   (equal (in-arena-fn-nntp-msgid-retrieval-indexed
                           *sr-arena* *rt-session* *rt-s1* *rt-h-index* :article (fn-record-string-octets "<a1@x>"))
                          (fn-nntp-single *rt-session* "430 article reclaimed"))))
; Tooth (tombstone): a2 by Message-ID is served, not 430.
(assert-event (not (equal (in-arena-fn-nntp-msgid-retrieval-indexed
                           *sr-arena* *rt-session* *rt-s1* *rt-h-index* :article
                           (fn-record-string-octets "<a2@x>"))
                          (fn-nntp-single *rt-session* "430 article reclaimed"))))
; Tooth (the correspondence): an empty index misses a1 (430 is not answered).
(assert-event (and (not (fn-midx-correspondencep nil *rt-h-arts*))
                   (not (equal (in-arena-fn-nntp-msgid-retrieval-indexed
                                *sr-arena* *rt-session* *rt-s1* nil :article (fn-record-string-octets "<a1@x>"))
                               (fn-nntp-single *rt-session* "430 article reclaimed")))))
; fn-nntp-over-by-msgid-answers-reclaimed and fn-nntp-over-current-answers-
; reclaimed over handles.
(assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* *rt-session* *rt-s1* (list (fn-record-string-octets "<a1@x>")))
                     (fn-nntp-single *rt-session* "430 article reclaimed")))
(assert-event (not (equal (in-arena-fn-nntp-over-response *sr-arena* *rt-session* *rt-s1*
                                                          (list (fn-record-string-octets "<a2@x>")))
                          (fn-nntp-single *rt-session* "430 article reclaimed"))))
(assert-event (equal (in-arena-fn-nntp-over-response *sr-arena* *rt-cur1* *rt-s1* nil)
                     (fn-nntp-single *rt-cur1* "423 article reclaimed")))
(assert-event (not (equal (in-arena-fn-nntp-over-response *sr-arena* (fn-nntp-make-session t "g" 2 t) *rt-s1* nil)
                          (fn-nntp-single (fn-nntp-make-session t "g" 2 t) "423 article reclaimed"))))
; fn-nov-lines-skip-a-reclaimed-article over handles.
(assert-event (equal (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(1 2) *rt-h-arts*)
                     (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(2) *rt-h-arts*)))
(assert-event (not (equal (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(1 2) *rt-h-arts*)
                          (in-arena-fn-nov-lines-for-numbers *sr-arena* "g" '(1) *rt-h-arts*))))
