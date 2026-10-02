; fn: the holders the OWNER carries for the online reclaim pass, and the
; end of the pass's context (RECLAIM-RETENTION, 2026-10-03; D13, STO-014,
; PRF-088).
;
; books/store-reclaim-holders reads the holders a Store carries.  The
; owner's outbound feed queues are not Store state: each queue holds the
; Message-IDs still owed to a live peer, and the feed renders an article's
; bytes from the arena only when it offers it (books/owner-feed-article
; fn-ofa-feed-article).  So a queued article reclaimed before its offer was
; sent to the peer as its tombstone.  This book is the feed slot's producer
; and the context the online pass reads:
;
;   fn-rcl-owner-feed-holders  every queue entry of every peer in the owner's
;                              feed table (a dropped entry included: the
;                              queue holds undelivered obligations only,
;                              books/peer-feed PRF-335), keyed by the
;                              Message-ID string the renderer resolves
;                              (fn-record-octets-string, as
;                              fn-apr-feed-article does), as a fast alist
;                              (msgid . peer).  Built on the owner mutex at
;                              the capture (host/owner-host.lisp
;                              fn-owner-orc-capture); a queue grows only
;                              by an accepting commit, which the swap's
;                              empty-delta test defers.
;   fn-rclp-ctx-with-feeds     the context with that slot in place.
;   fn-rclp-ctx-free           frees the context's fast alists (index,
;                              expired set, feeds, BP) once the pass is done
;                              with it; logically the identity on nothing.
;
; KEYSTONES fn-rclp-owner-ctx-never-releases-a-queued-article and
; fn-rclp-owner-ctx-never-releases-a-forward-pinned-article.
(in-package "ACL2")
(include-book "expiry-instant")
(include-book "owner")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The feed slot.

(defun fn-rcl-feed-queue-holders (peer queue acc)
  (declare (xargs :guard t))
  (if (consp queue)
      (fn-rcl-feed-queue-holders
       peer (cdr queue)
       (hons-acons (fn-record-octets-string (fn-feed-entry-msgid (car queue))) peer acc))
    acc))

(defun fn-rcl-feed-table-holders (tbl acc)
  (declare (xargs :guard t))
  (if (consp tbl)
      (fn-rcl-feed-table-holders
       (cdr tbl)
       (fn-rcl-feed-queue-holders (fn-own-feed-entry-name (car tbl))
                                  (fn-feed-queue (fn-own-feed-entry-feed (car tbl)))
                                  acc))
    acc))

(defun fn-rcl-owner-feed-holders (o)
  (declare (xargs :guard t))
  (fn-rcl-feed-table-holders (fn-own-feeds o) nil))

; The specification: some queue entry of some peer resolves to MSGID.
(defun fn-rcl-queue-owes-p (msgid queue)
  (declare (xargs :guard t))
  (if (consp queue)
      (or (equal (fn-record-octets-string (fn-feed-entry-msgid (car queue))) msgid)
          (fn-rcl-queue-owes-p msgid (cdr queue)))
    nil))

(defun fn-rcl-table-owes-p (msgid tbl)
  (declare (xargs :guard t))
  (if (consp tbl)
      (or (fn-rcl-queue-owes-p msgid (fn-feed-queue (fn-own-feed-entry-feed (car tbl))))
          (fn-rcl-table-owes-p msgid (cdr tbl)))
    nil))

(local
 (defthm fn-rcl-feed-queue-holders-finds
   (iff (hons-assoc-equal msgid (fn-rcl-feed-queue-holders peer queue acc))
        (or (hons-assoc-equal msgid acc) (fn-rcl-queue-owes-p msgid queue)))
   :hints (("Goal" :induct (fn-rcl-feed-queue-holders peer queue acc)))))

(local
 (defthm fn-rcl-feed-table-holders-finds
   (iff (hons-assoc-equal msgid (fn-rcl-feed-table-holders tbl acc))
        (or (hons-assoc-equal msgid acc) (fn-rcl-table-owes-p msgid tbl)))
   :hints (("Goal" :induct (fn-rcl-feed-table-holders tbl acc)))))

; The slot names MSGID exactly when some live peer's queue owes it.
(defthm fn-rcl-owner-feed-holders-is-the-queues
  (iff (hons-assoc-equal msgid (fn-rcl-owner-feed-holders o))
       (fn-rcl-table-owes-p msgid (fn-own-feeds o))))

(local
 (defthm fn-rcl-queue-owes-p-of-member
   (implies (and (member-equal q queue)
                 (equal (fn-record-octets-string (fn-feed-entry-msgid q)) msgid))
            (fn-rcl-queue-owes-p msgid queue))))

(defthm fn-rcl-table-owes-p-of-members
  (implies (and (member-equal e tbl)
                (member-equal q (fn-feed-queue (fn-own-feed-entry-feed e)))
                (equal (fn-record-octets-string (fn-feed-entry-msgid q)) msgid))
           (fn-rcl-table-owes-p msgid tbl))
  :hints (("Goal" :induct (member-equal e tbl))))

; -----------------------------------------------------------------------------
; The online pass's context: the Store's holders with the owner's feeds.

(defun fn-rclp-ctx-with-feeds (ctx feeds)
  (declare (xargs :guard t))
  (let ((h (fn-rcl-nth 2 ctx)))
    (list (fn-rcl-nth 0 ctx) (fn-rcl-nth 1 ctx)
          (list (fn-rcl-pins h) (fn-rcl-cursors h) feeds (fn-rcl-bp h))
          (fn-rcl-nth 3 ctx) (fn-rcl-nth 4 ctx) (fn-rcl-nth 5 ctx) (fn-rcl-nth 6 ctx))))

; Its fast alists, freed when the pass is done with the context.  Every one
; of them is built for this context alone (fn-rclp-ctx-expiring builds the
; index, fn-xpy-expired-set the expired set, fn-rcl-store-holders the BP
; slot, fn-owner-orc-capture the feed slot).  `fast-alist-free' is the
; identity in the logic, so no theorem reads it; what freeing changes is that
; a later probe of a freed alist would walk it.  The host calls this once,
; after the last use of the context (host/native/owner.lisp, the pass's
; end).
(defun fn-rclp-ctx-free (ctx)
  (declare (xargs :guard t))
  (let ((h (fn-rcl-nth 2 ctx)))
    (prog2$ (fast-alist-free (fn-rcl-nth 6 ctx))
            (prog2$ (fast-alist-free (fn-rcl-nth 5 ctx))
                    (prog2$ (fast-alist-free (fn-rcl-feeds h))
                            (prog2$ (fast-alist-free (fn-rcl-bp h)) nil))))))

; -----------------------------------------------------------------------------
; Keystones over the context the online pass builds.

(local
 (defthm fn-rclp-msgid-of-found
   (implies (consp (fn-find-article m articles))
            (equal (fn-article-msgid (fn-find-article m articles)) m))
   :hints (("Goal" :in-theory (enable fn-find-article)))))

(local
 (defthm fn-rclp-keyed-feed-is-not-releasable
   (implies (fn-rcl-keyedp (fn-article-msgid article) (fn-rcl-feeds h))
            (not (fn-xpy-releasablep rule now h verdicts expired article)))
   :hints (("Goal" :in-theory (e/d (fn-xpy-releasablep fn-xpy-standing-verdict
                                    fn-rcl-standing-verdict fn-rcl-undelivered-p)
                                   (fn-rcl-keyedp fn-rcl-tombstonep fn-rcl-rulep
                                    fn-rcl-rule-permits fn-rcl-pinned-p
                                    fn-rcl-unacknowledged-p
                                    fn-rcl-verdict-heldp fn-xpy-expiredp))))))

(local
 (defthm fn-rclp-keyed-bp-is-not-releasable
   (implies (fn-rcl-keyedp (fn-article-msgid article) (fn-rcl-bp h))
            (not (fn-xpy-releasablep rule now h verdicts expired article)))
   :hints (("Goal" :in-theory (e/d (fn-xpy-releasablep fn-xpy-standing-verdict
                                    fn-rcl-standing-verdict)
                                   (fn-rcl-keyedp fn-rcl-tombstonep fn-rcl-rulep
                                    fn-rcl-rule-permits fn-rcl-pinned-p
                                    fn-rcl-undelivered-p fn-rcl-unacknowledged-p
                                    fn-rcl-verdict-heldp fn-xpy-expiredp))))))

; The context's verdict for M, opened onto the article the index finds.
(local
 (defthm fn-rclp-with-feeds-reclaimable-opens
   (equal (fn-rclp-ctx-reclaimable
           (fn-rclp-ctx-with-feeds (fn-rclp-ctx-expiring rule now s expired) feeds) m)
          (fn-xpy-releasablep
           rule now
           (list nil (fn-rcl-cursors (fn-rcl-store-holders s)) feeds
                 (fn-rcl-bp-holders (fn-sn-node s)))
           (fn-sn-verdicts s) expired
           (fn-find-article m (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
   :hints (("Goal" :in-theory (e/d (fn-rclp-ctx-reclaimable fn-rclp-ctx-expiring
                                    fn-rcl-store-holders)
                                   (fn-xpy-releasablep fn-rcl-bp-holders
                                    fn-rcl-lagging-consumerp fn-rcl-cursors-at-zero))))))

(local
 (defthm fn-rclp-rewrite-of-unreclaimable
   (implies (not (fn-rclp-ctx-reclaimable
                  ctx (fn-record-msgid (fn-record-result-record
                                        (fn-record-decode-exact octets)))))
            (equal (fn-rclp-event octets ctx) octets))
   :hints (("Goal" :in-theory (enable fn-rclp-event fn-rclp-rewrites-p)))))

;  KEYSTONE (a queued feed article is kept).  The subject is the per-record
; rewrite the online pass runs (books/owner-reclaim fn-orc-chunk, the
; offline rewrite by fn-orc-rewrite-rows-is-the-offline-rewrite) under the
; context host/owner-host.lisp fn-owner-orc-ctx builds: the Store's context
; at the recorded instant with the owner's feed slot.  An article record
; whose Message-ID a live peer's queue still owes is the same octets after
; the rewrite, under the rule and under expiry.
(defthm fn-rclp-owner-ctx-never-releases-a-queued-article
  (let ((m (fn-record-msgid (fn-record-result-record (fn-record-decode-exact octets)))))
    (implies (and (member-equal e (fn-own-feeds o))
                  (member-equal q (fn-feed-queue (fn-own-feed-entry-feed e)))
                  (equal (fn-record-octets-string (fn-feed-entry-msgid q)) m)
                  (consp (fn-find-article
                          m (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
             (equal (fn-rclp-event octets
                                   (fn-rclp-ctx-with-feeds
                                    (fn-rclp-ctx-expiring rule now s expired)
                                    (fn-rcl-owner-feed-holders o)))
                    octets)))
  :hints (("Goal" :in-theory (e/d (fn-rcl-keyedp)
                                  (fn-rclp-ctx-with-feeds fn-rclp-ctx-expiring
                                   fn-rcl-owner-feed-holders fn-xpy-releasablep
                                   fn-rclp-event fn-rclp-ctx-reclaimable
                                   fn-rclp-keyed-feed-is-not-releasable
                                   fn-rcl-table-owes-p-of-members))
                  :use ((:instance fn-rcl-table-owes-p-of-members
                                   (tbl (fn-own-feeds o))
                                   (msgid (fn-record-msgid (fn-record-result-record
                                                            (fn-record-decode-exact octets)))))
                        (:instance fn-rclp-keyed-feed-is-not-releasable
                                   (h (list nil (fn-rcl-cursors (fn-rcl-store-holders s))
                                            (fn-rcl-owner-feed-holders o)
                                            (fn-rcl-bp-holders (fn-sn-node s))))
                                   (verdicts (fn-sn-verdicts s))
                                   (article (fn-find-article
                                             (fn-record-msgid (fn-record-result-record
                                                               (fn-record-decode-exact octets)))
                                             (fn-state-articles
                                              (fn-node-acceptance (fn-sn-node s))))))))))

;  KEYSTONE (the canonical BP retention pin, over the online context).  The
; feed slot leaves the Store's BP slot in place.
(defthm fn-rclp-owner-ctx-never-releases-a-forward-pinned-article
  (let* ((node (fn-sn-node s))
         (m (fn-record-msgid (fn-record-result-record (fn-record-decode-exact octets)))))
    (implies (and (member-equal pin (fn-retain-pins (fn-node-retention node)))
                  (not (equal (fn-retain-obligation-kind pin) :archive))
                  (member-equal b (fn-node-bindings node))
                  (equal (fn-node-binding-subject b) (fn-retain-obligation-subject pin))
                  (equal (fn-node-binding-msgid b) m)
                  (consp (fn-find-article m (fn-state-articles (fn-node-acceptance node)))))
             (equal (fn-rclp-event octets
                                   (fn-rclp-ctx-with-feeds
                                    (fn-rclp-ctx-expiring rule now s expired) feeds))
                    octets)))
  :hints (("Goal" :in-theory (e/d (fn-rcl-keyedp)
                                  (fn-rclp-ctx-with-feeds fn-rclp-ctx-expiring
                                   fn-rcl-bp-holders fn-xpy-releasablep
                                   fn-rclp-event fn-rclp-ctx-reclaimable
                                   fn-rclp-keyed-bp-is-not-releasable
                                   fn-rcl-bp-holders-is-the-pinned-bindings))
                  :use ((:instance fn-rcl-bp-holders-is-the-pinned-bindings
                                   (node (fn-sn-node s))
                                   (msgid (fn-record-msgid (fn-record-result-record
                                                            (fn-record-decode-exact octets)))))
                        (:instance fn-rcl-bp-boundp-of-member
                                   (msgid (fn-record-msgid (fn-record-result-record
                                                            (fn-record-decode-exact octets))))
                                   (bindings (fn-node-bindings (fn-sn-node s)))
                                   (pins (fn-retain-pins (fn-node-retention (fn-sn-node s)))))
                        (:instance fn-rclp-keyed-bp-is-not-releasable
                                   (h (list nil (fn-rcl-cursors (fn-rcl-store-holders s))
                                            feeds (fn-rcl-bp-holders (fn-sn-node s))))
                                   (verdicts (fn-sn-verdicts s))
                                   (article (fn-find-article
                                             (fn-record-msgid (fn-record-result-record
                                                               (fn-record-decode-exact octets)))
                                             (fn-state-articles
                                              (fn-node-acceptance (fn-sn-node s))))))))))
