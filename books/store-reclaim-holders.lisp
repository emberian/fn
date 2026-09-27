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
(include-book "article-arena-reads")  ; fn-nntp-article-tombstonep, -length

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

; -----------------------------------------------------------------------------
; The counts over the ARENA (lane matrix-reds-reclaim).  Since the records
; flip an archive article's payload position is an arena HANDLE
; (books/store-intern.lisp), so `fn-rcl-verdict''s tombstone test and
; `fn-rcl-summary''s `len' read a natural: :already-reclaimed was never
; answered (a reclaimed article counted as reclaimable again) and every
; octet count was 0.  The counts the host prints read each article through
; the arena instead (books/article-arena-reads.lisp): its length in O(1),
; whether it is a tombstone from the tombstone's fixed head, and a
; tombstone's recorded length from the tombstone's own octets (fixed size).
; No payload octet list is built for a live article (D27).  The arena is
; only read (flip-L6-2's rule).
;
; The wire functions above stay the octet-list model; each arena function
; below is that model over the articles' octet models
; (books/nntp-session.lisp fn-nntp-article-alpha): the keystones
; fn-rcl-verdict-arena-is-the-model-verdict and
; fn-rcl-store-counts-arena-is-the-model-counts.

(defun fn-rcl-verdict-arena (rule now h verdicts article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-rcl-rulep
                                                            fn-rcl-rule-permits
                                                            fn-nntp-article-tombstonep)))))
  (let ((msgid (fn-article-msgid article))
        (memberships (fn-article-memberships article)))
    (cond ((fn-nntp-article-tombstonep article fn-arena) :already-reclaimed)
          ((equal rule '(:keep-forever)) :rule-keeps)
          ((not (fn-rcl-rulep rule)) :rule-refused)
          ((not (fn-rcl-rule-permits rule now (fn-article-stamp article)))
           :too-recent)
          ((fn-rcl-verdict-heldp msgid verdicts) :verdict-needs-payload)
          ((fn-rcl-pinned-p (fn-rcl-pins h) memberships) :held-reader-pin)
          ((fn-rcl-unacknowledged-p memberships (fn-rcl-cursors h))
           :held-consumer-cursor)
          ((fn-rcl-undelivered-p (fn-rcl-feeds h) msgid) :held-feed)
          ((member-equal msgid (true-list-fix (fn-rcl-bp h))) :held-bp-obligation)
          (t :reclaimable))))

; KEYSTONE.  The verdict over the arena is `fn-rcl-verdict' of the article's
; octet model: the pre-flip verdict, which read the article's own payload.
(defthm fn-rcl-verdict-arena-is-the-model-verdict
  (equal (fn-rcl-verdict-arena rule now h verdicts article fn-arena)
         (fn-rcl-verdict rule now h verdicts (fn-nntp-article-alpha article fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-article-alpha)
                                  (fn-rcl-tombstonep fn-rcl-rulep fn-rcl-rule-permits
                                   fn-rcl-verdict-heldp fn-rcl-pinned-p
                                   fn-rcl-unacknowledged-p fn-rcl-undelivered-p
                                   fn-nntp-article-bytes)))))

(defun fn-rcl-summary-arena (rule now h verdicts articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp articles)
      (let* ((rest (fn-rcl-summary-arena rule now h verdicts (cdr articles) fn-arena))
             (a (car articles))
             (verdict (fn-rcl-verdict-arena rule now h verdicts a fn-arena)))
        (cond ((equal verdict :reclaimable)
               (list (+ 1 (nfix (nth 0 rest)))
                     (+ (fn-nntp-article-length a fn-arena) (nfix (nth 1 rest)))
                     (nfix (nth 2 rest)) (nfix (nth 3 rest))))
              ((equal verdict :already-reclaimed)
               (list (nfix (nth 0 rest)) (nfix (nth 1 rest))
                     (+ 1 (nfix (nth 2 rest)))
                     (+ (nfix (- (fn-rcl-tomb-length (fn-nntp-article-bytes a fn-arena))
                                 (fn-nntp-article-length a fn-arena)))
                        (nfix (nth 3 rest)))))
              (t (list (nfix (nth 0 rest)) (nfix (nth 1 rest))
                       (nfix (nth 2 rest)) (nfix (nth 3 rest))))))
    (list 0 0 0 0)))

(defun fn-rcl-held-count-arena (rule now h verdicts articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp articles)
      (+ (if (fn-rcl-heldp (fn-rcl-verdict-arena rule now h verdicts (car articles) fn-arena))
             1 0)
         (fn-rcl-held-count-arena rule now h verdicts (cdr articles) fn-arena))
    0))

; What the host calls (books/native-live-status.lisp fn-nls-reclaim-words,
; books/store-log-reclaim.lisp fn-lgr-decide-stream).
(defun fn-rcl-store-counts-arena (rule now s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-sn-verdicts s))
        (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (append (fn-rcl-summary-arena rule now h verdicts articles fn-arena)
            (list (fn-rcl-held-count-arena rule now h verdicts articles fn-arena)))))

; The octet models of an article list (logical: the statement's model).
(defun fn-rcl-articles-alpha (articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (cons (fn-nntp-article-alpha (car articles) fn-arena)
            (fn-rcl-articles-alpha (cdr articles) fn-arena))
    nil))

(defthm fn-rcl-summary-arena-is-the-model-summary
  (equal (fn-rcl-summary-arena rule now h verdicts articles fn-arena)
         (fn-rcl-summary rule now h verdicts (fn-rcl-articles-alpha articles fn-arena)))
  :hints (("Goal" :induct (fn-rcl-summary-arena rule now h verdicts articles fn-arena)
           :in-theory (e/d (fn-nntp-article-alpha fn-nntp-article-length)
                           (fn-rcl-verdict fn-rcl-verdict-arena fn-rcl-tomb-length
                            fn-nntp-article-bytes)))))

(defthm fn-rcl-held-count-arena-is-the-model-held-count
  (equal (fn-rcl-held-count-arena rule now h verdicts articles fn-arena)
         (fn-rcl-held-count rule now h verdicts (fn-rcl-articles-alpha articles fn-arena)))
  :hints (("Goal" :in-theory (disable fn-rcl-verdict fn-rcl-verdict-arena fn-rcl-heldp))))

; KEYSTONE.  The counts the host prints are the octet-list model's counts
; (`fn-rcl-store-counts''s summary and held count) over the octet models of
; the Store's articles: the counts the pre-flip Store printed.  Subject:
; fn-rcl-store-counts-arena, called by fn-nls-reclaim-words (the status
; report, host/native-live-status-host.lisp and the owner's live report) and
; fn-lgr-decide-stream (host/checkpoint-host.lisp
; fn-store-log-reclaim-decide-stream, `store reclaim').
(defthm fn-rcl-store-counts-arena-is-the-model-counts
  (let ((h (fn-rcl-store-holders s))
        (verdicts (fn-sn-verdicts s))
        (models (fn-rcl-articles-alpha
                 (fn-state-articles (fn-node-acceptance (fn-sn-node s))) fn-arena)))
    (equal (fn-rcl-store-counts-arena rule now s fn-arena)
           (append (fn-rcl-summary rule now h verdicts models)
                   (list (fn-rcl-held-count rule now h verdicts models)))))
  :hints (("Goal" :in-theory (disable fn-rcl-summary fn-rcl-held-count
                                      fn-rcl-summary-arena fn-rcl-held-count-arena
                                      fn-rcl-store-holders))))

