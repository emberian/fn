; fn: the holders a Store itself carries, and the reclamation counts the
; status report prints (D13, STO-014, PRF-088).
;
; `fn-rcl-verdict' (books/store-reclaim) takes the holders as an argument:
; (pins cursors feeds bp).  This book reads the ones the Store state
; carries.  What it reads, and what it cannot:
;
;   consumer cursors  the E2 consumer projection (`fn-sn-consumer'): a
;                     registered consumer acknowledges a Store journal
;                     position, not a group number.  Mapping that position
;                     to the articles after it needs the record sequence of
;                     each article, which the acceptance state does not
;                     keep.  So the reading is conservative: a consumer whose
;                     acknowledgement is below the committed frontier holds
;                     EVERY article (a cursor at 0 in every group).  Sound,
;                     and coarse: nothing is reclaimable while any consumer
;                     lags.  The precise reading is open (PRF-088).
;   reader pins       none: a reader's pin lives in its connection and has no
;                     durable form.  `store reclaim' is offline (refused
;                     while an owner runs), so no connection exists when it
;                     decides; the live status count is advisory.
;   feeds, BP         not in this Store's state (feed state is the feed
;                     service's, FNBS rows the BP node's); open (PRF-088).
;
; Keystone: `fn-rcl-store-holders-hold-behind-a-lagging-consumer'.
(in-package "ACL2")
(include-book "store-reclaim")
(include-book "store-node")

; A registered consumer whose acknowledgement is below FRONTIER.
(defun fn-rcl-lagging-consumerp (entries frontier)
  (declare (xargs :guard t))
  (if (consp entries)
      (or (let ((ack (fn-cp-nth 7 (car entries))))
            (and (natp ack) (natp frontier) (< ack frontier)))
          (fn-rcl-lagging-consumerp (cdr entries) frontier))
    nil))

(defun fn-rcl-cursors-at-zero (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (if (stringp (car groups))
          (cons (cons (car groups) 0) (fn-rcl-cursors-at-zero (cdr groups)))
        (fn-rcl-cursors-at-zero (cdr groups)))
    nil))

(defun fn-rcl-store-holders (s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((cp (fn-sn-consumer s)))
    (list nil
          (if (fn-rcl-lagging-consumerp (fn-cp-nth 5 cp) (fn-cp-nth 3 cp))
              (fn-rcl-cursors-at-zero
               (fn-state-groups (fn-node-acceptance (fn-sn-node s))))
            nil)
          nil
          nil)))

(local
 (defthm fn-rcl-above-zero-in-cursors
   (implies (and (member-equal g groups) (stringp g)
                 (member-equal (cons g n) (true-list-fix memberships))
                 (posp n))
            (fn-rcl-unacknowledged-p memberships (fn-rcl-cursors-at-zero groups)))
   :hints (("Goal" :induct (fn-rcl-cursors-at-zero groups)))))

(local
 (defthm fn-rcl-above-p-of-member
   (implies (and (member-equal (cons g n) (true-list-fix memberships)) (posp n))
            (fn-rcl-above-p g 0 memberships))))

;  KEYSTONE (the conservative consumer reading).  While any registered
; consumer's acknowledgement is below the committed frontier, no article
; numbered in a group the Store serves is reclaimable, whatever the rule,
; clock or verdicts.
(defthm fn-rcl-store-holders-hold-behind-a-lagging-consumer
  (let ((cp (fn-sn-consumer s)))
    (implies (and (fn-rcl-lagging-consumerp (fn-cp-nth 5 cp) (fn-cp-nth 3 cp))
                  (member-equal g (fn-state-groups (fn-node-acceptance (fn-sn-node s))))
                  (stringp g) (posp n)
                  (member-equal (cons g n) (true-list-fix (fn-article-memberships article))))
             (not (fn-rcl-reclaimable rule now (fn-rcl-store-holders s) verdicts article))))
  :hints (("Goal" :use ((:instance fn-rcl-above-zero-in-cursors
                                   (groups (fn-state-groups
                                            (fn-node-acceptance (fn-sn-node s))))
                                   (memberships (fn-article-memberships article))))
                  :in-theory (disable fn-rcl-tombstonep fn-rcl-rulep fn-rcl-rule-permits
                                      fn-rcl-pinned-p fn-rcl-undelivered-p
                                      fn-rcl-unacknowledged-p fn-rcl-above-zero-in-cursors
                                      fn-rcl-cursors-at-zero
                                      fn-rcl-verdict-heldp fn-sn-consumer))))

; -----------------------------------------------------------------------------
; The counts `status' prints: (reclaimable reclaimable-octets reclaimed
; freed-octets held).  HELD counts articles some holder keeps (reader pin,
; consumer, feed, BP), not those the rule or a verdict keeps.

(defun fn-rcl-heldp (verdict)
  (declare (xargs :guard t))
  (if (member-eq verdict '(:held-reader-pin :held-consumer-cursor :held-feed
                           :held-bp-obligation))
      t nil))

(defun fn-rcl-held-count (rule now h verdicts articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (+ (if (fn-rcl-heldp (fn-rcl-verdict rule now h verdicts (car articles))) 1 0)
         (fn-rcl-held-count rule now h verdicts (cdr articles)))
    0))

(defun fn-rcl-store-counts (rule now s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-sn-verdicts s))
        (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (append (fn-rcl-summary rule now h verdicts articles)
            (list (fn-rcl-held-count rule now h verdicts articles)))))

; -----------------------------------------------------------------------------
; Why an :absent verdict holds nothing (`fn-rcl-verdict-heldp',
; books/store-reclaim).  The statement index is re-derived from the stored
; payloads at open (`fn-stx-index-of-store' over `fn-stx-delta' of each
; payload, under the keyring of that open).  The verdict the Store recorded
; for an article is `fn-stx-verdict-of-octets' of its payload under the
; keyring of its acceptance (`fn-sn-finish-records-the-acceptance-verdict',
; books/store-node-invariants).  When that verdict is :absent the payload
; contributes nothing to the index under EVERY keyring, and neither does the
; tombstone that replaces it (`fn-rcl-tombstone-contributes-nothing',
; books/reclaim-admission), so reclaiming it cannot change the index any
; later open derives from the payloads.
(defthm fn-rcl-absent-verdict-contributes-nothing
  (implies (equal (fn-stx-verdict-token (fn-stx-verdict-of-octets payload k1 g))
                  :absent)
           (equal (fn-stx-delta payload k2) nil))
  :hints (("Goal" :in-theory (enable (:d fn-stx-verdict-of-octets) (:d fn-stx-verdict)
                                     (:d fn-stx-delta) (:d fn-stx-verifiedp)
                                     (:d fn-stx-statement-of) fn-prin-verifiedp
                                     fn-stx-make-verdict fn-stx-verdict-token))))
