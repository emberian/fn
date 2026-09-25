; fn: witnesses and teeth for books/store-reclaim-holders.lisp and the
; reclamation words of the status report (D13, STO-014, PRF-088).
(in-package "ACL2")
(include-book "../../books/store-reclaim-holders")
(include-book "../../books/native-live-status")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-served-invariants-tests")

; The owner fixture's store, its one article, and a group it is numbered in.
; The completing owner's store after its article completed, as in
; octets-stobj-tests (not included: it depends on the octet buffer books).
(defconst *rht-s0* (fn-own-store (cdr (fn-own-finish *osi-completing* *osi-cfg*))))
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
 (equal (fn-nls-reclaim-words *rht-caught* (fn-cfg-initial) '(nil nil (:full-replay :absent) nil))
        (fn-record-string-octets
         "reclaim rule=keep-forever reclaimable=0 reclaimable-octets=0 held=0 reclaimed=0 freed-octets=0")))
