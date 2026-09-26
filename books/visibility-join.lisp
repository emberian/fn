; fn: a resend of an accepted source stays answered from the Store after its
; withdrawal and after its reclamation (NNT-019, PRF-115; the mandate's 5.1,
; "stored, visible and absent are not synonyms").
;
; A poster whose POST reply was lost settles what the node accepted by
; re-submitting the same immutable source under the same Message-ID (D25).
; A Message-ID lookup cannot settle it: C3 withdrawal answers `430 withdrawn'
; to every view published after the cancel (books/nntp-control.lisp), and a
; reclaimed article answers 430 as well (books/nntp-reclaimed.lisp), while
; the Store still holds the identity history.  This book proves the
; re-submission is the honest question: once a Message-ID is held, the
; decision the host calls answers `:duplicate' or `:conflict' -- never nil,
; which is the only answer that reaches a prepare -- across every Store
; completion (the cancel's acceptance is one) and across reclamation, and
; the served reply to it is one of the two 441 lines, never 240.
;
; The subject is what the host calls.  host/native/owner.lisp
; `fnn-owner-attempt' asks host/owner-host.lisp
; `fn-owner-existing-action-buffer', whose decision is
; `fn-rclb-existing-action' (books/store-reclaim-buffer), and returns
; `:duplicate' / `:conflict' as its word before `fnn-advance-frontier' or
; `fn-owner-prepare-buffer' run, so no transaction number and no article
; number is allocated.  The carried-signature ingress
; (`fnn-owner-attempt-transit') asks `fn-owner-existing-action', whose
; decision is `fn-rcl-existing-action' (books/store-reclaim).  Both are
; stated.  The word goes to `fn-own-outcome' (host/owner-host.lisp
; `fn-owner-outcome'), whose reply is `fn-pb-served-reply'
; (books/poster-bytes-invariants).
;
; Withdrawal is not a Store mutation.  A cancel is an ordinary article
; accepted by `fn-sn-finish' (the owner's carried commit is
; `fn-ccar-sn-finish', equal to it by `fn-ccar-sn-finish-is-sn-finish'); the
; withdrawal record is derived from the article list by the owner's control
; refresh and hides the target from reader views only.  So the withdrawal
; keystone is a statement over `fn-sn-finish'.  Reclamation replaces a
; payload by its tombstone (`fn-rcl-reclaim-state'); no host verb drives it
; yet (planning/now.md, reclamation), so the reclamation keystone is over
; the Store transition itself.
;
; Keystones:
;   fn-vj-a-completion-keeps-a-held-message-id-answered
;   fn-vj-reclamation-keeps-a-held-message-id-answered
;   fn-vj-a-held-message-id-is-answered-441
; The exact :duplicate for the same source across reclamation is
; `fn-rcl-existing-action-after-reclaim' (books/store-reclaim), whose
; collision disjuncts stand.
;
; Prefix `fn-vj-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "store-reclaim-buffer")
(include-book "store-node-retention")
(include-book "poster-bytes-invariants")

; The Store's article list.
(defun fn-vj-articles (s)
  (declare (xargs :guard t))
  (fn-state-articles (fn-node-acceptance (fn-sn-node s))))

; -----------------------------------------------------------------------------
; Held is a property of the article list, found by the lookup the decision
; makes.

(local
 (defthm fn-vj-find-of-accepted-is-a-member
   (implies (fn-acceptedp msgid xs)
            (and (member-equal (fn-find-article msgid xs) xs)
                 (equal (fn-article-msgid (fn-find-article msgid xs)) msgid)))
   :hints (("Goal" :in-theory (enable fn-acceptedp fn-find-article)))))

(local
 (defthm fn-vj-a-member-is-accepted
   (implies (and (member-equal a xs) (equal (fn-article-msgid a) msgid))
            (fn-acceptedp msgid xs))
   :hints (("Goal" :in-theory (enable fn-acceptedp)))))

(local
 (defthm fn-vj-accepted-string-is-found
   (implies (and (fn-acceptedp msgid xs) (stringp msgid))
            (fn-find-article msgid xs))
   :hints (("Goal" :in-theory (enable fn-acceptedp fn-find-article)))))

; The decision, both entries, answers from the Store whenever the Message-ID
; is held.  (By the definitions: the lookup is by Message-ID.)
(defthm fn-vj-a-held-message-id-is-answered-by-definition
  (implies (and (stringp msgid) (fn-acceptedp msgid (fn-vj-articles s)))
           (and (member-equal (fn-rclb-existing-action msgid fn-octets groups s)
                              '(:duplicate :conflict))
                (member-equal (fn-rcl-existing-action msgid payload groups s)
                              '(:duplicate :conflict))))
  :hints (("Goal" :in-theory (enable fn-rclb-existing-action fn-rcl-existing-action)
                  :use ((:instance fn-vj-accepted-string-is-found
                                   (xs (fn-vj-articles s)))))))

; -----------------------------------------------------------------------------
;  KEYSTONE (withdrawal).  A Message-ID held before any Store completion --
; the cancel that withdraws it is one, and so is every other acceptance,
; retention or identity event -- is still answered from the Store after it:
; a resend under it is never prepared as a fresh acceptance.
(defthm fn-vj-a-completion-keeps-a-held-message-id-answered
  (implies (and (stringp msgid) (fn-acceptedp msgid (fn-vj-articles s)))
           (and (member-equal (fn-rclb-existing-action msgid fn-octets groups
                                                       (fn-sn-finish s))
                              '(:duplicate :conflict))
                (member-equal (fn-rcl-existing-action msgid payload groups
                                                      (fn-sn-finish s))
                              '(:duplicate :conflict))))
  :hints (("Goal"
           :in-theory (disable fn-sn-finish fn-acceptedp fn-find-article
                               fn-rclb-existing-action fn-rcl-existing-action
                               fn-rcl-existing-action-is-action-over-by-definition
                               fn-sn-finish-keeps-accepted-articles
                               fn-vj-find-of-accepted-is-a-member
                               fn-vj-a-member-is-accepted
                               fn-vj-accepted-string-is-found
                               fn-vj-a-held-message-id-is-answered-by-definition)
           :use ((:instance fn-vj-find-of-accepted-is-a-member
                            (xs (fn-vj-articles s)))
                 (:instance fn-sn-finish-keeps-accepted-articles
                            (article (fn-find-article msgid (fn-vj-articles s))))
                 (:instance fn-vj-a-member-is-accepted
                            (a (fn-find-article msgid (fn-vj-articles s)))
                            (xs (fn-vj-articles (fn-sn-finish s))))
                 (:instance fn-vj-a-held-message-id-is-answered-by-definition
                            (s (fn-sn-finish s)))))))

; Reclamation keeps the held Message-IDs (fn-rcl-reclaim-keeps-the-duplicate-
; history, read through the state).
(local
 (defthm fn-vj-reclaim-state-keeps-accepted
   (equal (fn-acceptedp msgid (fn-state-articles (fn-rcl-reclaim-state acc r tomb)))
          (fn-acceptedp msgid (fn-state-articles acc)))
   :hints (("Goal" :in-theory (enable fn-rcl-reclaim-state)))))

(local
 (defthm fn-vj-a-held-list-is-answered
   (implies (and (stringp msgid) (fn-acceptedp msgid arts)
                 (equal (fn-vj-articles s) arts))
            (and (member-equal (fn-rclb-existing-action msgid fn-octets groups s)
                               '(:duplicate :conflict))
                 (member-equal (fn-rcl-existing-action msgid payload groups s)
                               '(:duplicate :conflict))))
   :hints (("Goal" :use (fn-vj-a-held-message-id-is-answered-by-definition)
                   :in-theory (disable fn-vj-a-held-message-id-is-answered-by-definition
                                       fn-rclb-existing-action fn-rcl-existing-action
                                       fn-rcl-existing-action-is-action-over-by-definition
                                       fn-acceptedp fn-vj-articles)))))

;  KEYSTONE (reclamation).  Reclaiming any article R of an acceptance state
; ACC keeps every held Message-ID answered: for any Store S2 whose article
; list is the reclaimed one, both entries answer from the Store.
(defthm fn-vj-reclamation-keeps-a-held-message-id-answered
  (implies (and (stringp msgid)
                (fn-acceptedp msgid (fn-state-articles acc))
                (equal (fn-vj-articles s2)
                       (fn-state-articles (fn-rcl-reclaim-state acc r tomb))))
           (and (member-equal (fn-rclb-existing-action msgid fn-octets groups s2)
                              '(:duplicate :conflict))
                (member-equal (fn-rcl-existing-action msgid payload groups s2)
                              '(:duplicate :conflict))))
  :hints (("Goal"
           :in-theory (disable fn-vj-articles fn-rcl-reclaim-state fn-acceptedp
                               fn-rclb-existing-action fn-rcl-existing-action
                               fn-rcl-existing-action-is-action-over-by-definition
                               fn-vj-a-held-list-is-answered
                               fn-vj-reclaim-state-keeps-accepted)
           :use ((:instance fn-vj-reclaim-state-keeps-accepted)
                 (:instance fn-vj-a-held-list-is-answered
                            (s s2)
                            (arts (fn-state-articles
                                   (fn-rcl-reclaim-state acc r tomb))))))))

;; The two Store words are rendered as their two 441 lines while the
;; resend is in flight (fn-pb-same-article-is-answered-already-stored and
;; fn-pb-different-article-is-answered-conflict, for any source of the word).
(local
 (defthm fn-vj-a-store-word-is-answered-441
   (implies (and (fn-own-find-conn id (fn-own-conns o))
                 (fn-own-inflight o)
                 (equal (fn-own-sub-id (fn-own-inflight o)) id)
                 (not (fn-own-completion-consumedp o))
                 (member-equal word '(:duplicate :conflict)))
            (member-equal (car (fn-own-outcome o id word))
                          (list (fn-pb-served-reply o id :duplicate)
                                (fn-pb-served-reply o id :conflict))))
   :hints (("Goal"
            :cases ((equal word :duplicate))
            :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                             fn-own-outcome-rendering fn-own-refusal-wordp
                             fn-post-store-refusalp)
                            (fn-served-post-outcome fn-own-advance
                             fn-own-feed-durable fn-own-find-conn
                             fn-served-make-conn-group-indexed))))))

;  KEYSTONE (the served reply).  While the resend is the connection's
; in-flight submission and no completion was consumed, a held Message-ID
; gets the duplicate line or the conflict line, and nothing else: in
; particular not 240, which only a consumed durable completion renders
; (books/nntp-post.lisp).
(defthm fn-vj-a-held-message-id-is-answered-441
  (implies (and (fn-own-find-conn id (fn-own-conns o))
                (fn-own-inflight o)
                (equal (fn-own-sub-id (fn-own-inflight o)) id)
                (not (fn-own-completion-consumedp o))
                (stringp msgid)
                (fn-acceptedp msgid (fn-vj-articles s)))
           (member-equal (car (fn-own-outcome
                               o id (fn-rclb-existing-action msgid fn-octets groups s)))
                         (list (fn-pb-served-reply o id :duplicate)
                               (fn-pb-served-reply o id :conflict))))
  :hints (("Goal"
           :use ((:instance fn-vj-a-held-message-id-is-answered-by-definition)
                 (:instance fn-vj-a-store-word-is-answered-441
                            (word (fn-rclb-existing-action msgid fn-octets groups s))))
           :in-theory (disable fn-vj-a-store-word-is-answered-441
                               fn-vj-a-held-message-id-is-answered-by-definition
                               fn-own-outcome fn-pb-served-reply
                               fn-rclb-existing-action fn-rcl-existing-action
                               fn-rcl-existing-action-is-action-over-by-definition
                               fn-rclb-existing-action-is-rcl-existing-action
                               fn-acceptedp fn-vj-articles)))
  :rule-classes nil)
