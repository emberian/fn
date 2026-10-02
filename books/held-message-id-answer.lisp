; fn: a held Message-ID keeps its exact answer across a Store completion
; (Q3d (i), PKT-239; NNT-019, PRF-115).
;
; books/visibility-join.lisp proves only that a held Message-ID is answered
; :duplicate or :conflict after `fn-sn-finish' (the cancel's acceptance is
; one): without uniqueness a completion could put a second article under the
; same Message-ID ahead of the first (completions prepend), and the lookup
; would answer from it.  Uniqueness is CARRIED, not revalidated: `fn-statep'
; (books/acceptance.lisp, inside `fn-sn-statep') holds `fn-article-listp',
; whose Message-IDs are distinct (fn-article-listp-is-shape-and-distinct-
; msgids), and `fn-sn-finish-preserves-state' keeps it.  So the article the
; lookup finds after the completion is the one it found before, and the
; decision the host calls is unchanged: a resend of the same source stays
; :duplicate, a changed one stays :conflict.  No served scan is added.
;
; The subject is what the host calls: host/native/owner.lisp `fnn-owner-attempt'
; reaches `fn-store-existing-action' (books/store-intern.lisp) through
; host/owner-host.lisp `fn-owner-existing-action-buffer' / `fn-pidx-existing-
; action' (fn-pidx-existing-action-is-store-existing-action), and the
; carried-signature ingress through `fn-owner-existing-action'.  The Store
; transition is `fn-sn-finish' (the owner's carried commit fn-ccar-sn-finish
; equals it, fn-ccar-sn-finish-is-sn-finish).  Its only hypothesis is that
; the Message-ID is held: (stringp msgid), a hypothesis of the visibility-join
; keystone, and fn-sn-statep are not needed, and the weakened theorem is
; proved (outside fn-sn-statep the completion's gate is closed).
;
; KEYSTONE fn-hma-a-completion-keeps-the-held-answer.  Prefix `fn-hma-'.
; GEN: def-carried -- the invariant carried is fn-statep's article-list
; conjunct, already established at init and preserved per transition by
; books/store-node-invariants-base.lisp; no new carried predicate is needed.
(in-package "ACL2")
(include-book "visibility-join")
(include-book "store-node-invariants-base")

(local (defthm fn-hma-a-member-is-accepted
  (implies (member-equal a xs)
           (fn-acceptedp (fn-article-msgid a) xs))
  :hints (("Goal" :in-theory (enable fn-acceptedp)))))
(local (defthm fn-hma-member-msgid-of-member
  (implies (member-equal a xs)
           (member-equal (fn-article-msgid a) (fn-article-msgids xs)))
  :hints (("Goal" :in-theory (enable fn-article-msgids)))))
(local (defthm fn-hma-a-held-article-is-the-found-one
  (implies (and (fn-article-listp configured xs)
                (member-equal a xs)
                (equal (fn-article-msgid a) msgid))
           (equal (fn-find-article msgid xs) a))
  :hints (("Goal" :in-theory (enable fn-find-article fn-article-msgids)))))
(local (defthm fn-hma-store-articles-are-an-article-list
  (implies (fn-sn-statep s)
           (fn-article-listp (fn-state-groups (fn-node-acceptance (fn-sn-node s)))
                             (fn-vj-articles s)))
  :hints (("Goal" :in-theory (enable fn-sn-statep fn-node-statep fn-statep fn-vj-articles)))))

(local (defthm fn-hma-found-article-is-held
  (implies (fn-acceptedp msgid xs)
           (and (member-equal (fn-find-article msgid xs) xs)
                (equal (fn-article-msgid (fn-find-article msgid xs)) msgid)))
  :hints (("Goal" :in-theory (enable fn-acceptedp fn-find-article)))))

(local (defthm fn-hma-finish-finds-the-same-article
  (implies (and (fn-sn-statep s)
                (fn-acceptedp msgid (fn-vj-articles s)))
           (equal (fn-find-article msgid (fn-vj-articles (fn-sn-finish s)))
                  (fn-find-article msgid (fn-vj-articles s))))
  :hints (("Goal"
           :in-theory (e/d (fn-vj-articles)
                           (fn-sn-finish fn-sn-statep fn-find-article fn-acceptedp
                            fn-sn-finish-keeps-accepted-articles
                            fn-hma-a-held-article-is-the-found-one
                            fn-hma-found-article-is-held
                            fn-hma-store-articles-are-an-article-list))
           :use ((:instance fn-hma-found-article-is-held (xs (fn-vj-articles s)))
                 (:instance fn-sn-finish-keeps-accepted-articles
                            (article (fn-find-article msgid (fn-vj-articles s))))
                 fn-sn-finish-preserves-state
                 (:instance fn-hma-store-articles-are-an-article-list (s (fn-sn-finish s)))
                 (:instance fn-hma-a-held-article-is-the-found-one
                            (configured (fn-state-groups
                                         (fn-node-acceptance (fn-sn-node (fn-sn-finish s)))))
                            (xs (fn-vj-articles (fn-sn-finish s)))
                            (a (fn-find-article msgid (fn-vj-articles s)))))))))

(local (defthm fn-hma-a-completion-on-a-store-keeps-the-held-answer
  (implies (and (fn-sn-statep s)
                (fn-acceptedp msgid (fn-vj-articles s)))
           (equal (fn-store-existing-action msgid payload groups (fn-sn-finish s) fn-arena)
                  (fn-store-existing-action msgid payload groups s fn-arena)))
  :hints (("Goal" :use fn-hma-finish-finds-the-same-article
                  :in-theory (e/d (fn-store-existing-action fn-vj-articles)
                                  (fn-hma-finish-finds-the-same-article
                                   fn-store-existing-action-is-the-verdict-over-alpha
                                   fn-sn-finish fn-sn-statep fn-find-article
                                   fn-handle-bytes fn-rcl-same-articlep))))))

; Outside the Store invariant the completion is a stutter: its gate
; (fn-sn-completion-core-enabledp) requires fn-sn-statep.
(local (defthm fn-hma-finish-outside-the-state-is-a-stutter
  (implies (not (fn-sn-statep s))
           (equal (fn-sn-finish s) s))
  :hints (("Goal" :in-theory (enable fn-sn-finish fn-sn-completion-enabledp
                                     fn-sn-completion-core-enabledp)))))

; KEYSTONE.  One hypothesis: the Message-ID is held.  fn-sn-statep is not
; needed (outside it the completion changes nothing), nor (stringp msgid).
(defthm fn-hma-a-completion-keeps-the-held-answer
  (implies (fn-acceptedp msgid (fn-vj-articles s))
           (equal (fn-store-existing-action msgid payload groups (fn-sn-finish s) fn-arena)
                  (fn-store-existing-action msgid payload groups s fn-arena)))
  :hints (("Goal" :cases ((fn-sn-statep s))
                  :use fn-hma-a-completion-on-a-store-keeps-the-held-answer
                  :in-theory (disable fn-hma-a-completion-on-a-store-keeps-the-held-answer
                                      fn-sn-finish fn-sn-statep fn-store-existing-action))))
