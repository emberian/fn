; General logical acceptance preservation, with no disk or crypto claims.
(in-package "ACL2")
(include-book "acceptance")

(defthm fn-bump-preserves-nexts
  (implies (fn-nexts-for-p configured nexts)
           (fn-nexts-for-p configured (fn-bump-number group nexts)))
  :hints (("Goal" :induct (fn-nexts-for-p configured nexts))))

(defthm fn-next-positive
  (implies (and (fn-nexts-for-p configured nexts)
                (member-equal group configured))
           (posp (fn-next-number group nexts)))
  :hints (("Goal" :induct (fn-nexts-for-p configured nexts))))

(defthm fn-next-bump-other
  (implies (not (equal a b))
           (equal (fn-next-number a (fn-bump-number b nexts))
                  (fn-next-number a nexts))))

(defthm fn-next-bump-same
  (implies (and (fn-nexts-for-p configured nexts)
                (member-equal group configured))
           (equal (fn-next-number group (fn-bump-number group nexts))
                  (+ 1 (fn-next-number group nexts))))
  :hints (("Goal" :induct (fn-nexts-for-p configured nexts))))

(defthm fn-allocate-valid-memberships
  (implies (and (fn-nexts-for-p configured nexts)
                (fn-subsetp groups configured))
           (fn-membership-listp groups
                                (fn-allocate-memberships groups nexts)))
  :hints (("Goal" :induct (fn-allocate-memberships groups nexts))))

(defthm fn-watermark-bump-other
  (implies (and (fn-membership-listp groups memberships)
                (not (member-equal group groups)))
           (equal (fn-memberships-at-watermarkp
                   memberships (fn-bump-number group nexts))
                  (fn-memberships-at-watermarkp memberships nexts)))
  :hints (("Goal" :induct (fn-membership-listp groups memberships))))

(defthm fn-allocated-watermark-bump-other
  (implies (and (fn-nexts-for-p configured nexts)
                (fn-subsetp groups configured)
                (not (member-equal group groups)))
           (equal (fn-memberships-at-watermarkp
                   (fn-allocate-memberships groups (fn-bump-number group nexts))
                   (fn-bump-number group nexts))
                  (fn-memberships-at-watermarkp
                   (fn-allocate-memberships groups (fn-bump-number group nexts))
                   nexts)))
  :hints (("Goal"
           :use ((:instance fn-watermark-bump-other
                  (memberships (fn-allocate-memberships
                                groups (fn-bump-number group nexts))))
                 (:instance fn-allocate-valid-memberships
                  (nexts (fn-bump-number group nexts))))
           :in-theory (disable fn-watermark-bump-other
                               fn-allocate-valid-memberships
                               fn-allocate-memberships fn-membership-listp
                               fn-memberships-at-watermarkp fn-nexts-for-p
                               fn-subsetp fn-bump-number))))

(defthm fn-allocate-at-watermark
  (implies (and (fn-nexts-for-p configured nexts)
                (fn-subsetp groups configured)
                (fn-no-duplicatesp groups))
           (fn-memberships-at-watermarkp
            (fn-allocate-memberships groups nexts) nexts))
  :hints (("Goal" :induct (fn-allocate-memberships groups nexts))))

(defthm fn-prepare-preserves-state
  (implies (fn-statep s)
           (fn-statep
            (fn-accept-prepare s generation msgid payload groups)))
  :hints (("Goal" :in-theory (enable fn-accept-prepare fn-statep))))

(defthm fn-advance-preserves-nexts
  (implies (fn-nexts-for-p configured nexts)
           (fn-nexts-for-p configured (fn-advance-nexts groups nexts)))
  :hints (("Goal" :induct (fn-advance-nexts groups nexts))))

(defthm fn-next-bump-monotone
  (implies (fn-nexts-for-p configured nexts)
           (<= (fn-next-number group nexts)
               (fn-next-number group (fn-bump-number other nexts))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-nexts-for-p configured nexts))))

(defthm fn-next-advance-monotone
  (implies (fn-nexts-for-p configured nexts)
           (<= (fn-next-number group nexts)
               (fn-next-number group (fn-advance-nexts groups nexts))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-advance-nexts groups nexts)
           :in-theory (disable fn-next-number fn-bump-number fn-nexts-for-p))))

(defthm fn-next-advance-after-bump-greater
  (implies (and (fn-nexts-for-p configured nexts)
                (member-equal group configured))
           (< (fn-next-number group nexts)
              (fn-next-number group
               (fn-advance-nexts groups (fn-bump-number group nexts)))))
  :hints (("Goal"
           :use ((:instance fn-next-advance-monotone
                  (nexts (fn-bump-number group nexts))))
           :in-theory (disable fn-next-number fn-bump-number fn-nexts-for-p
                               fn-advance-nexts))))

(defthm fn-next-advance-greater
  (implies (and (fn-nexts-for-p configured nexts)
                (member-equal group configured)
                (member-equal group groups))
           (< (fn-next-number group nexts)
              (fn-next-number group (fn-advance-nexts groups nexts))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-advance-nexts groups nexts)
           :in-theory (disable fn-next-number fn-bump-number fn-nexts-for-p))))

(defthm fn-below-preserved-by-advance
  (implies (and (fn-nexts-for-p configured nexts)
                (fn-memberships-below-nextsp memberships nexts))
           (fn-memberships-below-nextsp
            memberships (fn-advance-nexts groups nexts)))
  :hints (("Goal" :induct (fn-memberships-below-nextsp memberships nexts)
           :in-theory (disable fn-next-number fn-advance-nexts fn-nexts-for-p))))

(defthm fn-articles-below-preserved-by-advance
  (implies (and (fn-nexts-for-p configured nexts)
                (fn-articles-below-nextsp articles nexts))
           (fn-articles-below-nextsp articles (fn-advance-nexts groups nexts)))
  :hints (("Goal" :induct (fn-articles-below-nextsp articles nexts)
           :in-theory (disable fn-memberships-below-nextsp
                               fn-advance-nexts fn-nexts-for-p))))

(defthm fn-watermark-memberships-below-advance
  (implies (and (fn-nexts-for-p configured nexts)
                (fn-membership-listp selected memberships)
                (fn-subsetp selected configured)
                (fn-subsetp selected groups)
                (fn-memberships-at-watermarkp memberships nexts))
           (fn-memberships-below-nextsp memberships
                                        (fn-advance-nexts groups nexts)))
  :hints (("Goal" :induct (fn-membership-listp selected memberships)
           :in-theory (disable fn-next-number fn-advance-nexts fn-nexts-for-p))))

(defthm fn-subset-cons-right
  (implies (fn-subsetp xs ys)
           (fn-subsetp xs (cons x ys))))

(defthm fn-subset-self
  (fn-subsetp groups groups))

(defthm fn-below-append
  (equal (fn-memberships-below-nextsp (append a b) nexts)
         (and (fn-memberships-below-nextsp a nexts)
              (fn-memberships-below-nextsp b nexts))))

(defthm fn-flatten-articles-below
  (implies (fn-articles-below-nextsp articles nexts)
           (fn-memberships-below-nextsp
            (fn-all-article-memberships articles) nexts)))

(defthm fn-watermark-pair-not-below-member
  (implies (and (equal (cdr pair) (fn-next-number (car pair) nexts))
                (fn-memberships-below-nextsp memberships nexts))
           (not (fn-pair-memberp pair memberships)))
  :hints (("Goal" :induct (fn-pair-memberp pair memberships)
           :in-theory (disable fn-next-number))))

(defthm fn-watermark-does-not-conflict
  (implies (and (fn-memberships-at-watermarkp memberships nexts)
                (fn-articles-below-nextsp articles nexts))
           (not (fn-memberships-conflictsp memberships articles)))
  :hints (("Goal" :induct (fn-memberships-conflictsp memberships articles)
           :in-theory (disable fn-next-number fn-all-article-memberships
                               fn-articles-below-nextsp fn-pair-memberp))))

(defthm fn-accepted-iff-id-member
  (iff (member-equal msgid (fn-article-msgids articles))
       (fn-acceptedp msgid articles)))

(defthm fn-pending-to-article-valid
  (implies (fn-pendingp configured nexts next-txid pending)
           (fn-articlep configured (fn-article-from-pending pending))))

(defthm fn-install-preserves-state
  (implies (and (fn-statep s)
                (consp (fn-state-pending s)))
           (fn-statep (fn-install-pending s)))
  :hints (("Goal" :in-theory (enable fn-install-pending fn-statep))))

(defthm fn-complete-preserves-state
  (implies (fn-statep s)
           (fn-statep (fn-accept-complete s txid generation completion-status)))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-recover-preserves-state
  (implies (fn-statep s)
           (fn-statep (fn-accept-recover s txid generation recovery-result)))
  :hints (("Goal" :in-theory (enable fn-accept-recover))))

; Existing bindings retain the entire article record: payload, memberships,
; and archive pin, including when a different pending article is published.
(defthm fn-prepare-preserves-existing-message-id-binding
  (implies (fn-statep s)
           (equal (fn-find-article
                   existing-msgid
                   (fn-state-articles
                    (fn-accept-prepare s generation msgid payload groups)))
                  (fn-find-article existing-msgid (fn-state-articles s))))
  :hints (("Goal" :in-theory (disable fn-statep fn-state-articles fn-accept-prepare fn-find-article))))

(defthm fn-install-preserves-existing-message-id-binding
  (implies (and (fn-statep s)
                (consp (fn-state-pending s))
                (fn-acceptedp msgid (fn-state-articles s)))
           (equal (fn-find-article msgid
                                  (fn-state-articles (fn-install-pending s)))
                  (fn-find-article msgid (fn-state-articles s))))
  :hints (("Goal" :in-theory (enable fn-statep fn-install-pending))))

(defthm fn-complete-preserves-existing-message-id-binding
  (implies (and (fn-statep s)
                (fn-acceptedp msgid (fn-state-articles s)))
           (equal (fn-find-article
                   msgid (fn-state-articles
                          (fn-accept-complete s txid generation completion-status)))
                  (fn-find-article msgid (fn-state-articles s))))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-recover-preserves-existing-message-id-binding
  (implies (and (fn-statep s)
                (fn-acceptedp msgid (fn-state-articles s)))
           (equal (fn-find-article
                   msgid (fn-state-articles
                          (fn-accept-recover s txid generation recovery-result)))
                  (fn-find-article msgid (fn-state-articles s))))
  :hints (("Goal" :in-theory (enable fn-accept-recover))))

; No two distinct committed article records acquire the same (group . number).
(defthm fn-state-has-fresh-local-numbers
  (implies (fn-statep s)
           (fn-articles-freshp (fn-state-articles s))))

(defthm fn-prepare-preserves-local-number-uniqueness
  (implies (fn-statep s)
           (fn-articles-freshp
            (fn-state-articles
             (fn-accept-prepare s generation msgid payload groups))))
  :hints (("Goal" :use ((:instance fn-state-has-fresh-local-numbers
                        (s (fn-accept-prepare s generation msgid payload groups))))
           :in-theory (disable fn-statep fn-articles-freshp fn-accept-prepare))))

(defthm fn-complete-preserves-local-number-uniqueness
  (implies (fn-statep s)
           (fn-articles-freshp
            (fn-state-articles
             (fn-accept-complete s txid generation completion-status))))
  :hints (("Goal" :use ((:instance fn-state-has-fresh-local-numbers
                        (s (fn-accept-complete s txid generation completion-status))))
           :in-theory (disable fn-statep fn-articles-freshp fn-accept-complete))))

(defthm fn-recover-preserves-local-number-uniqueness
  (implies (fn-statep s)
           (fn-articles-freshp
            (fn-state-articles
             (fn-accept-recover s txid generation recovery-result))))
  :hints (("Goal" :use ((:instance fn-state-has-fresh-local-numbers
                        (s (fn-accept-recover s txid generation recovery-result))))
           :in-theory (disable fn-statep fn-articles-freshp fn-accept-recover))))
