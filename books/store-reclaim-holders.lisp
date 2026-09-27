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
(include-book "payload-arena")

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

; -----------------------------------------------------------------------------
; The counts over the arena (audit-fixes, 2026-09-27).  Since the acceptance
; flip an article's payload is a HANDLE into the arena
; (books/payload-arena.lisp).  `fn-rcl-summary' is the octet-list model: it
; reads the payload as octets, so over handles its two octet figures were 0
; for every article and it never saw a tombstone (an already-reclaimed
; article was counted again by its holders).  ALPHA of an article replaces its
; handle by the octets the arena holds there (an octet payload is its own);
; the counts the host calls read each length and the tombstone's fixed head
; through the arena, never copying an article's bytes, and are the model's
; counts over ALPHA (KEYSTONE fn-rcl-store-counts-is-the-model-over-alpha).
(defun fn-rcl-payload-bytes (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (natp p)
      (if (< p (fn-arena-count fn-arena)) (fn-arena-payload p fn-arena) nil)
    p))
(defun fn-rcl-article-alpha (a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-make-article (fn-article-msgid a)
                   (fn-rcl-payload-bytes (fn-article-payload a) fn-arena)
                   (fn-article-groups a) (fn-article-memberships a)
                   (fn-article-pin a) (fn-article-stamp a)))
(defun fn-rcl-articles-alpha (articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (cons (fn-rcl-article-alpha (car articles) fn-arena)
            (fn-rcl-articles-alpha (cdr articles) fn-arena))
    nil))
(defun fn-rcl-arena-prefixp (prefix h i fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (true-listp prefix) (natp h) (natp i)
                              (< h (fn-arena-count fn-arena)))
                  :measure (len prefix)))
  (if (consp prefix)
      (and (< i (fn-arena-payload-len h fn-arena))
           (equal (car prefix) (fn-arena-get h i fn-arena))
           (fn-rcl-arena-prefixp (cdr prefix) h (+ 1 i) fn-arena))
    t))
(encapsulate ()
  (local (defthm fn-rcl-car-nthcdr (equal (car (nthcdr i xs)) (nth i xs))))
  (local (defthm fn-rcl-cdr-nthcdr
           (implies (natp i) (equal (cdr (nthcdr i xs)) (nthcdr (+ 1 i) xs)))))
  (local (defthm fn-rcl-nthcdr-of-nil (equal (nthcdr i nil) nil)))
  (local (defthm fn-rcl-consp-nthcdr
           (implies (natp i) (iff (consp (nthcdr i xs)) (< i (len xs))))))
  (local (in-theory (disable nthcdr nth)))
  (defthm fn-rcl-arena-prefixp-is-rcl-prefixp
    (implies (natp i)
             (equal (fn-rcl-arena-prefixp prefix h i fn-arena)
                    (fn-rcl-prefixp prefix (nthcdr i (nth h fn-arena)))))
    :hints (("Goal" :induct (fn-rcl-arena-prefixp prefix h i fn-arena)
             :in-theory (enable fn-rcl-prefixp fn-arena-get-is-nth
                                fn-arena-payload-len-is-len-nth)))))
(defthm fn-rcl-arena-prefixp-at-0
  (equal (fn-rcl-arena-prefixp prefix h 0 fn-arena)
         (fn-rcl-prefixp prefix (nth h fn-arena)))
  :hints (("Goal" :use ((:instance fn-rcl-arena-prefixp-is-rcl-prefixp (i 0)))
           :in-theory (enable nthcdr))))
(local
 (defthm fn-rcl-at-leastp-is-len
   (implies (natp n)
            (equal (fn-rcl-at-leastp n xs) (<= n (len xs))))
   :hints (("Goal" :in-theory (enable fn-rcl-at-leastp)))))
(local
 (defthm fn-rcl-tombstonep-unfolds
   (equal (fn-rcl-tombstonep payload)
          (and (<= *fn-rcl-tombstone-fixed* (len payload))
               (fn-rcl-prefixp *fn-rcl-magic* payload)))
   :hints (("Goal" :in-theory '(fn-rcl-tombstonep fn-rcl-at-leastp-is-len
                                 (:e natp))))))
(defun fn-rcl-payload-len (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :in-theory '(fn-rcl-payload-bytes
                                                     fn-arena-payload-is-nth
                                                     fn-arena-count-is-len
                                                     fn-arena-payload-len-is-len-nth)))))
  (mbe :logic (len (fn-rcl-payload-bytes p fn-arena))
       :exec (if (and (natp p) (< p (fn-arena-count fn-arena)))
                 (fn-arena-payload-len p fn-arena)
               (len (fn-rcl-payload-bytes p fn-arena)))))
(defun fn-rcl-payload-tombstonep (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :in-theory '(fn-rcl-tombstonep-unfolds
                                                     fn-rcl-payload-bytes
                                                     fn-arena-payload-is-nth
                                                     fn-arena-count-is-len
                                                     fn-arena-payload-len-is-len-nth
                                                     fn-rcl-arena-prefixp-at-0)))))
  (mbe :logic (fn-rcl-tombstonep (fn-rcl-payload-bytes p fn-arena))
       :exec (if (and (natp p) (< p (fn-arena-count fn-arena)))
                 (and (<= *fn-rcl-tombstone-fixed* (fn-arena-payload-len p fn-arena))
                      (fn-rcl-arena-prefixp *fn-rcl-magic* p 0 fn-arena))
               (fn-rcl-tombstonep (fn-rcl-payload-bytes p fn-arena)))))
; A tombstone is small (its fixed 89 octets and the Path agent), so its
; length field is read from its bytes.
(defun fn-rcl-payload-tomb-length (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-rcl-tomb-length (fn-rcl-payload-bytes p fn-arena)))

(defun fn-rcl-verdict-in (rule now h verdicts a fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (fn-rcl-payload-tombstonep (fn-article-payload a) fn-arena)
      :already-reclaimed
    (fn-rcl-verdict rule now h verdicts a)))

(defun fn-rcl-summary-in (rule now h verdicts articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (let* ((rest (fn-rcl-summary-in rule now h verdicts (cdr articles) fn-arena))
             (a (car articles))
             (p (fn-article-payload a))
             (verdict (fn-rcl-verdict-in rule now h verdicts a fn-arena)))
        (cond ((equal verdict :reclaimable)
               (list (+ 1 (nfix (nth 0 rest)))
                     (+ (fn-rcl-payload-len p fn-arena) (nfix (nth 1 rest)))
                     (nfix (nth 2 rest)) (nfix (nth 3 rest))))
              ((equal verdict :already-reclaimed)
               (list (nfix (nth 0 rest)) (nfix (nth 1 rest))
                     (+ 1 (nfix (nth 2 rest)))
                     (+ (nfix (- (fn-rcl-payload-tomb-length p fn-arena)
                                 (fn-rcl-payload-len p fn-arena)))
                        (nfix (nth 3 rest)))))
              (t (list (nfix (nth 0 rest)) (nfix (nth 1 rest))
                       (nfix (nth 2 rest)) (nfix (nth 3 rest))))))
    (list 0 0 0 0)))

(defun fn-rcl-held-count-in (rule now h verdicts articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (+ (if (fn-rcl-heldp (fn-rcl-verdict-in rule now h verdicts (car articles) fn-arena)) 1 0)
         (fn-rcl-held-count-in rule now h verdicts (cdr articles) fn-arena))
    0))

; (reclaimable reclaimable-octets reclaimed reclaimed-octets-freed held):
; what `status' prints and the reclaim verbs report.
(defun fn-rcl-store-counts (rule now s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-sn-verdicts s))
        (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (append (fn-rcl-summary-in rule now h verdicts articles fn-arena)
            (list (fn-rcl-held-count-in rule now h verdicts articles fn-arena)))))

(local
 (defthm fn-rcl-article-alpha-accessors
   (and (equal (fn-article-msgid (fn-rcl-article-alpha a fn-arena)) (fn-article-msgid a))
        (equal (fn-article-memberships (fn-rcl-article-alpha a fn-arena))
               (fn-article-memberships a))
        (equal (fn-article-stamp (fn-rcl-article-alpha a fn-arena)) (fn-article-stamp a))
        (equal (fn-article-payload (fn-rcl-article-alpha a fn-arena))
               (fn-rcl-payload-bytes (fn-article-payload a) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-rcl-article-alpha) (fn-rcl-payload-bytes))))))

(local
 (defthm fn-rcl-tombstonep-of-an-atom
   (implies (not (consp p)) (not (fn-rcl-tombstonep p)))
   :hints (("Goal" :in-theory (enable fn-rcl-tombstonep fn-rcl-at-leastp)))))

; The verdict reads the payload only for the tombstone test, so the verdict
; of ALPHA is the tombstone test of the bytes, else the verdict of the article
; itself (whose handle is no tombstone).
(local
 (defthm fn-rcl-verdict-of-alpha
   (equal (fn-rcl-verdict rule now h verdicts (fn-rcl-article-alpha a fn-arena))
          (if (fn-rcl-tombstonep (fn-rcl-payload-bytes (fn-article-payload a) fn-arena))
              :already-reclaimed
            (fn-rcl-verdict rule now h verdicts a)))
   :hints (("Goal" :in-theory (e/d (fn-rcl-verdict fn-rcl-article-alpha-accessors)
                                   (fn-rcl-tombstonep fn-rcl-rulep fn-rcl-rule-permits
                                    fn-rcl-verdict-heldp fn-rcl-pinned-p
                                    fn-rcl-unacknowledged-p fn-rcl-undelivered-p
                                    fn-rcl-article-alpha))
            :cases ((natp (fn-article-payload a)))))))

(defthm fn-rcl-verdict-in-is-verdict-of-alpha
  (equal (fn-rcl-verdict-in rule now h verdicts a fn-arena)
         (fn-rcl-verdict rule now h verdicts (fn-rcl-article-alpha a fn-arena)))
  :hints (("Goal" :in-theory '(fn-rcl-verdict-in fn-rcl-payload-tombstonep
                               fn-rcl-verdict-of-alpha))))

(defthm fn-rcl-summary-in-is-summary-of-alpha
  (equal (fn-rcl-summary-in rule now h verdicts articles fn-arena)
         (fn-rcl-summary rule now h verdicts (fn-rcl-articles-alpha articles fn-arena)))
  :hints (("Goal" :induct (fn-rcl-summary-in rule now h verdicts articles fn-arena)
           :in-theory (e/d (fn-rcl-summary fn-rcl-summary-in fn-rcl-articles-alpha
                            fn-rcl-payload-len fn-rcl-payload-tomb-length
                            fn-rcl-article-alpha-accessors)
                           (fn-rcl-verdict fn-rcl-verdict-in fn-rcl-tombstonep
                            fn-rcl-tomb-length fn-rcl-payload-bytes fn-rcl-article-alpha)))))

(defthm fn-rcl-held-count-in-is-held-count-of-alpha
  (equal (fn-rcl-held-count-in rule now h verdicts articles fn-arena)
         (fn-rcl-held-count rule now h verdicts (fn-rcl-articles-alpha articles fn-arena)))
  :hints (("Goal" :induct (fn-rcl-held-count-in rule now h verdicts articles fn-arena)
           :in-theory (e/d (fn-rcl-held-count fn-rcl-held-count-in fn-rcl-articles-alpha)
                           (fn-rcl-verdict fn-rcl-verdict-in fn-rcl-heldp
                            fn-rcl-article-alpha)))))

; KEYSTONE.  The counts the host calls (status's reclaim line,
; books/native-live-status.lisp fn-nls-reclaim-words; the reclaim verbs'
; decisions, books/store-reclaim-pack.lisp fn-rclp-decide,
; books/store-reclaim-stream.lisp fn-rcls-decide, books/store-log-reclaim.lisp
; fn-lgr-decide(-stream)) are the octet-list model's summary and held count
; over ALPHA of the Store's articles: each reclaimable article counts its
; stored octets, each tombstone its freed octets.
(defthm fn-rcl-store-counts-is-the-model-over-alpha
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-sn-verdicts s))
        (alpha (fn-rcl-articles-alpha
                (fn-state-articles (fn-node-acceptance (fn-sn-node s))) fn-arena)))
    (equal (fn-rcl-store-counts rule now s fn-arena)
           (append (fn-rcl-summary rule now h verdicts alpha)
                   (list (fn-rcl-held-count rule now h verdicts alpha)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-rcl-store-counts fn-rcl-summary-in-is-summary-of-alpha
                               fn-rcl-held-count-in-is-held-count-of-alpha))))

; The books above reason about the counts as they did before the flip: the
; equalities stay off unless a proof names them.
(in-theory (disable fn-rcl-verdict-in-is-verdict-of-alpha
                    fn-rcl-summary-in-is-summary-of-alpha
                    fn-rcl-held-count-in-is-held-count-of-alpha))

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
