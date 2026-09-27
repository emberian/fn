; fn: witnesses and teeth for books/store-reclaim-holders.lisp and the
; reclamation words of the status report (D13, STO-014, PRF-088).
(in-package "ACL2")
(include-book "../../books/store-reclaim-holders")
(include-book "../../books/native-live-status")
(include-book "std/testing/must-fail" :dir :system)
(include-book "arena-lift")
(include-book "owner-served-invariants-tests")
; A verified article (*stxt-r1*) and the keyring it verifies under.
(include-book "stx-transit-tests")

; The owner fixture's store, its one article, and a group it is numbered in.
; The completing owner's store after its article completed, as in
; octets-stobj-tests (not included: it depends on the octet buffer books).
(defconst *rht-s0* (fn-own-store (cdr (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*))))
(defconst *rht-art* (car (fn-state-articles (fn-node-acceptance (fn-sn-node *rht-s0*)))))
(defconst *rht-m* (car (fn-article-memberships *rht-art*)))
(defconst *rht-g* (car *rht-m*))
(defconst *rht-n* (cdr *rht-m*))
(assert-event (and (stringp *rht-g*) (posp *rht-n*)
                   (member-equal *rht-g* (fn-state-groups (fn-node-acceptance
                                                           (fn-sn-node *rht-s0*))))))

; The store with a consumer projection: frontier 5, one consumer at ACK.
(defun rht-with-consumer (s ack)
  (update-nth 11 (fn-cp-state 1 1 5 2 (list (fn-cp-entry 7 1 1 0 0 1 ack))) s))
(defconst *rht-lag* (rht-with-consumer *rht-s0* 3))
(defconst *rht-caught* (rht-with-consumer *rht-s0* 5))
(defconst *rht-rule* '(:released-by-all-holders))

; Keystone witness: a lagging consumer holds the article under a releasing
; rule; caught up, the same article is reclaimable.
(assert-event (fn-rcl-lagging-consumerp (fn-cp-nth 5 (fn-sn-consumer *rht-lag*))
                                        (fn-cp-nth 3 (fn-sn-consumer *rht-lag*))))
(assert-event (equal (fn-rcl-verdict *rht-rule* 0 (fn-rcl-store-holders *rht-lag*) nil *rht-art*)
                     :held-consumer-cursor))
(assert-event (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-caught*) nil *rht-art*))
; Tooth (a lagging consumer): caught up, the conclusion fails.
(must-fail (assert-event (not (fn-rcl-reclaimable *rht-rule* 0
                                                  (fn-rcl-store-holders *rht-caught*)
                                                  nil *rht-art*))))
; Tooth (numbered, posp n): an article with no membership is not held.
(defconst *rht-bare* (fn-make-article (fn-article-msgid *rht-art*) (fn-article-payload *rht-art*)
                                      (fn-article-groups *rht-art*) nil t
                                      (fn-article-stamp *rht-art*)))
(must-fail (assert-event (not (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-lag*)
                                                  nil *rht-bare*))))
; Tooth (the group is served): numbered only in a group the store lacks.
(defconst *rht-other* (fn-make-article (fn-article-msgid *rht-art*) (fn-article-payload *rht-art*)
                                       (fn-article-groups *rht-art*) '(("zz.none" . 1)) t
                                       (fn-article-stamp *rht-art*)))
(must-fail (assert-event (not (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-lag*)
                                                  nil *rht-other*))))

; The verdict list.  Every article the fixture accepted has a verdict
; entry, and each is :absent (no authorship field): the Store's own list
; holds nothing, so the article is reclaimable with it.  An :unverified
; entry for the same Message-ID holds the payload.
(defconst *rht-msgid* (fn-article-msgid *rht-art*))
(assert-event (and (consp (fn-sn-verdicts *rht-caught*))
                   (fn-rcl-verdict-heldp *rht-msgid*
                                         (list (cons *rht-msgid* '(:unverified :signature 0))))
                   (not (fn-rcl-verdict-heldp *rht-msgid* (fn-sn-verdicts *rht-caught*)))))
(assert-event (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-caught*)
                                  (fn-sn-verdicts *rht-caught*) *rht-art*))
; Tooth (the entry is :absent): an :unverified verdict holds the article.
(must-fail (assert-event (fn-rcl-reclaimable *rht-rule* 0 (fn-rcl-store-holders *rht-caught*)
                                             (list (cons *rht-msgid* '(:unverified :signature 0)))
                                             *rht-art*)))

; fn-rcl-absent-verdict-contributes-nothing.  Witness: the fixture's own
; article is :absent under the empty keyring and contributes nothing under
; the keyring that verifies *stxt-r1*.  Tooth (the verdict is :absent):
; *stxt-r1* is :unverified under the empty keyring (its key not enrolled)
; and contributes a statement under *stxt-keyring*.
; by specification: the flip -- the article carries its payload as an arena
; handle (natp); the theorem is about the payload's OCTETS, which are the
; bytes under that handle in the arena that interned the completing journal
; (owner-served-invariants-tests osi-finish; held-rows-tests fn-hrt-bytes).
(defconst *rht-art-octets*
  (fn-hrt-bytes *osi-completing-prior* (fn-article-payload *rht-art*)))
(assert-event (and (natp (fn-article-payload *rht-art*))
                   (consp *rht-art-octets*)))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict-of-octets *rht-art-octets* nil 0))
                     :absent))
(assert-event (equal (fn-stx-delta *rht-art-octets* *stxt-keyring*) nil))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict-of-octets (fn-article-payload *stxt-r1*) nil 0))
                     :unverified))
(must-fail (assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r1*) *stxt-keyring*)
                                nil)))

; The counts: caught up, the article is counted reclaimable and nothing
; held; lagging, nothing is reclaimable and it is counted held.
(assert-event (let ((c (fn-rcl-store-counts *rht-rule* 0 *rht-caught*)))
                (and (<= 1 (nth 0 c)) (<= (len (fn-article-payload *rht-art*)) (nth 1 c))
                     (equal (nth 4 c) 0))))
(assert-event (let ((c (fn-rcl-store-counts *rht-rule* 0 *rht-lag*)))
                (and (equal (nth 0 c) 0) (<= 1 (nth 4 c)))))
; Keep-forever (no row): nothing reclaimable, nothing counted held.
(assert-event (equal (fn-rcl-store-counts '(:keep-forever) 0 *rht-caught*) (list 0 0 0 0 0)))

; The status words over the configuration's rule (no row: keep-forever).
(assert-event
 (equal (fn-nls-reclaim-words *rht-caught* (fn-cfg-initial) '(nil nil (:full-replay :absent) nil) fn-arena)
        (fn-record-string-octets
         "reclaim rule=keep-forever reclaimable=0 reclaimable-octets=0 held=0 reclaimed=0 freed-octets=0")))

; -----------------------------------------------------------------------------
; The counts over the ARENA (lane matrix-reds-reclaim).  The fixture is a
; flipped Store: its three articles carry handles 2, 1 and 0 (the tested
; article *rht-art* is handle 2); the arena below holds, at each handle, the
; bytes the arena that interned the completing journal holds there, or, for
; the reclaimed case, *rht-art*'s tombstone at its handle.
(defconst *rht-h* (fn-article-payload *rht-art*))
(defconst *rht-b0* (fn-hrt-bytes *osi-completing-prior* 0))
(defconst *rht-b1* (fn-hrt-bytes *osi-completing-prior* 1))
(defconst *rht-arena* (list *rht-b0* *rht-b1* *rht-art-octets*))
(defconst *rht-tomb*
  (fn-rcl-tombstone-of *rht-art-octets* (fn-record-string-octets *rht-msgid*)))
(defconst *rht-tomb-arena* (list *rht-b0* *rht-b1* *rht-tomb*))
(defconst *rht-live-octets* (+ (len *rht-b0*) (len *rht-b1*) (len *rht-art-octets*)))
(defconst *rht-freed* (- (len *rht-art-octets*) (len *rht-tomb*)))
(assert-event (and (equal *rht-h* 2)
                   (fn-rcl-tombstonep *rht-tomb*)
                   (not (fn-rcl-tombstonep *rht-art-octets*))
                   (consp *rht-b0*) (consp *rht-b1*)
                   (< 0 *rht-freed*)
                   (equal (len (fn-state-articles (fn-node-acceptance (fn-sn-node *rht-caught*))))
                          3)))
(defun rht-counts-model (rule now s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((models (fn-rcl-articles-alpha
                 (fn-state-articles (fn-node-acceptance (fn-sn-node s))) fn-arena)))
    (append (fn-rcl-summary rule now (fn-rcl-store-holders s) (fn-sn-verdicts s) models)
            (list (fn-rcl-held-count rule now (fn-rcl-store-holders s) (fn-sn-verdicts s)
                                     models)))))
(bpr-lift fn-rcl-store-counts-arena 3)
(bpr-lift rht-counts-model 3)
(bpr-lift fn-rcl-verdict-arena 5)

; fn-rcl-store-counts-arena-is-the-model-counts, reachable: caught up, the
; three articles are reclaimable and the octet count is the bytes under
; their handles; with *rht-art* reclaimed (its tombstone under its handle)
; it counts as reclaimed and its freed octets are its recorded length less
; the tombstone's.  Each equals the octet-list model's counts over the
; articles' octet models.
(assert-event
 (equal (in-arena-fn-rcl-store-counts-arena *rht-arena* *rht-rule* 0 *rht-caught*)
        (list 3 *rht-live-octets* 0 0 0)))
(assert-event
 (equal (in-arena-fn-rcl-store-counts-arena *rht-tomb-arena* *rht-rule* 0 *rht-caught*)
        (list 2 (+ (len *rht-b0*) (len *rht-b1*)) 1 *rht-freed* 0)))
(assert-event
 (and (equal (in-arena-fn-rcl-store-counts-arena *rht-arena* *rht-rule* 0 *rht-caught*)
             (in-arena-rht-counts-model *rht-arena* *rht-rule* 0 *rht-caught*))
      (equal (in-arena-fn-rcl-store-counts-arena *rht-tomb-arena* *rht-rule* 0 *rht-caught*)
             (in-arena-rht-counts-model *rht-tomb-arena* *rht-rule* 0 *rht-caught*))))
; Lagging, the live articles are held; the reclaimed one stays reclaimed.
(assert-event
 (equal (in-arena-fn-rcl-store-counts-arena *rht-arena* *rht-rule* 0 *rht-lag*)
        (list 0 0 0 0 3)))
(assert-event
 (equal (in-arena-fn-rcl-store-counts-arena *rht-tomb-arena* *rht-rule* 0 *rht-lag*)
        (list 0 0 1 *rht-freed* 2)))
; The mutation (the pre-lane counts, which parsed the handles): the wire
; counts over the flipped Store count no octets, and the reclaimed article
; as reclaimable again.
(assert-event (equal (fn-rcl-store-counts *rht-rule* 0 *rht-caught*) (list 3 0 0 0 0)))
(must-fail
 (assert-event
  (equal (fn-rcl-store-counts *rht-rule* 0 *rht-caught*)
         (in-arena-fn-rcl-store-counts-arena *rht-tomb-arena* *rht-rule* 0 *rht-caught*))))
(must-fail
 (assert-event
  (equal (fn-rcl-store-counts *rht-rule* 0 *rht-caught*)
         (in-arena-fn-rcl-store-counts-arena *rht-arena* *rht-rule* 0 *rht-caught*))))

; fn-rcl-verdict-arena-is-the-model-verdict: the tombstone under the handle
; is :already-reclaimed, the live octets :reclaimable; the wire verdict of
; the handle itself (the mutation) is never :already-reclaimed.
(assert-event
 (and (equal (in-arena-fn-rcl-verdict-arena *rht-tomb-arena* *rht-rule* 0
                                            (fn-rcl-store-holders *rht-caught*) nil *rht-art*)
             :already-reclaimed)
      (equal (in-arena-fn-rcl-verdict-arena *rht-arena* *rht-rule* 0
                                            (fn-rcl-store-holders *rht-caught*) nil *rht-art*)
             :reclaimable)))
(must-fail
 (assert-event
  (equal (fn-rcl-verdict *rht-rule* 0 (fn-rcl-store-holders *rht-caught*) nil *rht-art*)
         :already-reclaimed)))
