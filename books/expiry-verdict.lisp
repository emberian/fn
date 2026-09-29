; fn: expiry as a second release authority beside the retention rule (Q14;
; D03, D13, STO-014).
;
; `fn-rcl-standing-verdict' (books/store-reclaim) answers why a stored article
; stays, or :reclaimable, under the operator's store-wide retention rule and
; every holder.  The operator's per-group expiry policy (books/expiry-policy,
; decided per article by books/expiry) is a second authorized release: an
; article the policy has expired is released as though the rule were
; `released-by-all-holders', and nothing else changes -- every holder the
; lifetimes table names (reader pin, consumer cursor, undelivered feed, BP
; obligation) and an authorship verdict that needs the payload (STO-008) still
; keep it.  So an expired article's payload leaves only when the rule's own
; conditions other than age and policy would let it leave.
;
; EXPIRED is the set of Message-IDs the policy expires at the reclaim's
; instant, a fast alist (msgid . t) (books/expiry `fn-xpy-expired-set').  With
; no policy the set is empty and every verdict is the rule's
; (`fn-xpy-standing-verdict-without-expiry').
;
; The verdict :expired is kept distinct from :reclaimable (released by the
; rule) so the verb's report and the status classes can name why an article
; left; both rewrite the article to the same tombstone, which the served path
; answers `423'/`430 article reclaimed': distinct from `withdrawn' (a cancel)
; and from `no article' (never held).
(in-package "ACL2")
(include-book "store-reclaim")

(defconst *fn-xpy-release-rule* '(:released-by-all-holders))

; Whether the expired set names MSGID.
(defun fn-xpy-expiredp (msgid expired)
  (declare (xargs :guard t))
  (if (hons-get msgid expired) t nil))

;; Why an article stays, :reclaimable (the rule releases it) or :expired (the
; expiry policy releases it and no holder keeps it).
(defun fn-xpy-standing-verdict (rule now h verdicts expired article)
  (declare (xargs :guard t))
  (let ((base (fn-rcl-standing-verdict rule now h verdicts article)))
    (if (and (not (equal base :reclaimable))
             (fn-xpy-expiredp (fn-article-msgid article) expired))
        (let ((v (fn-rcl-standing-verdict *fn-xpy-release-rule* now h verdicts article)))
          (if (equal v :reclaimable) :expired v))
      base)))

(defun fn-xpy-releasablep (rule now h verdicts expired article)
  (declare (xargs :guard t))
  (if (member-eq (fn-xpy-standing-verdict rule now h verdicts expired article)
                 '(:reclaimable :expired))
      t
    nil))

; -----------------------------------------------------------------------------
; Keystones

;  With no expiry (nothing in the set names the article) the verdict is the
; retention rule's, exactly: a store without an expiry policy reclaims as it
; did (D03's default is the rule's keep-forever).
(defthm fn-xpy-standing-verdict-without-expiry
  (implies (not (fn-xpy-expiredp (fn-article-msgid article) expired))
           (equal (fn-xpy-standing-verdict rule now h verdicts expired article)
                  (fn-rcl-standing-verdict rule now h verdicts article))))

(defthm fn-xpy-releasablep-without-expiry
  (implies (not (fn-xpy-expiredp (fn-article-msgid article) expired))
           (equal (fn-xpy-releasablep rule now h verdicts expired article)
                  (fn-rcl-reclaimable rule now h verdicts article)))
  :hints (("Goal" :in-theory (enable fn-rcl-reclaimable))))

; The rule's verdict is never :expired (it names only its own reasons).
(local
 (defthm fn-xpy-rule-verdict-is-not-expired
   (not (equal (fn-rcl-standing-verdict rule now h verdicts article) :expired))
   :hints (("Goal" :in-theory (enable fn-rcl-standing-verdict)))))

;  KEYSTONE (Q14, the release).  An article is released -- its payload may
; become a tombstone -- exactly when the rule releases it, or the expiry
; policy has expired it and no authorship verdict needs its payload and NO
; obligation in the lifetimes table's list (reader pin, consumer cursor,
; undelivered feed to a live peer, BP obligation) names it.  Expiry adds an
; authority; it removes no holder.
(defthm fn-xpy-releasablep-is-rule-or-expired-and-unheld
  (equal (fn-xpy-releasablep rule now h verdicts expired article)
         (or (fn-rcl-reclaimable rule now h verdicts article)
             (and (fn-xpy-expiredp (fn-article-msgid article) expired)
                  (not (fn-rcl-verdict-heldp (fn-article-msgid article) verdicts))
                  (not (fn-rcl-some-names-p (fn-rcl-obligations h)
                                            (fn-article-msgid article)
                                            (fn-article-memberships article))))))
  :hints (("Goal" :use ((:instance fn-rcl-reclaimable-is-no-obligation-names-it
                                   (rule *fn-xpy-release-rule*)))
                  :in-theory (e/d (fn-rcl-reclaimable)
                                  (fn-rcl-reclaimable-is-no-obligation-names-it
                                   fn-rcl-standing-verdict fn-rcl-some-names-p
                                   fn-rcl-obligations fn-rcl-verdict-heldp
                                   fn-xpy-expiredp)))))

;  KEYSTONE (distinct outcomes).  :expired is answered only for an article
; the policy expired, and only when the rule alone would keep it; an article
; the rule releases is :reclaimable whatever the policy says.
(defthm fn-xpy-expired-verdict-is-the-policys
  (implies (equal (fn-xpy-standing-verdict rule now h verdicts expired article) :expired)
           (and (fn-xpy-expiredp (fn-article-msgid article) expired)
                (not (fn-rcl-reclaimable rule now h verdicts article))))
  :hints (("Goal" :in-theory (e/d (fn-rcl-reclaimable)
                                  (fn-rcl-standing-verdict fn-xpy-expiredp)))))

;  KEYSTONE (a held article is never released by expiry).  An article some
; obligation names, or whose verdict needs its payload, is not :expired.
(defthm fn-xpy-held-article-is-not-expired
  (implies (or (fn-rcl-some-names-p (fn-rcl-obligations h)
                                    (fn-article-msgid article)
                                    (fn-article-memberships article))
               (fn-rcl-verdict-heldp (fn-article-msgid article) verdicts))
           (not (equal (fn-xpy-standing-verdict rule now h verdicts expired article)
                       :expired)))
  :hints (("Goal" :use ((:instance fn-rcl-reclaimable-is-no-obligation-names-it
                                   (rule *fn-xpy-release-rule*)))
                  :in-theory (e/d (fn-rcl-reclaimable)
                                  (fn-rcl-reclaimable-is-no-obligation-names-it
                                   fn-rcl-standing-verdict fn-rcl-some-names-p
                                   fn-rcl-obligations fn-rcl-verdict-heldp
                                   fn-xpy-expiredp)))))

(in-theory (disable fn-xpy-standing-verdict fn-xpy-releasablep fn-xpy-expiredp))
