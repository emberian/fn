; fn: reachable Store-node witnesses over an article-holding byte store for
; the byte keystones that quantify over a Store-node state s (rows B26-B29,
; B40, B42, B44, B45, B47, B59, B60 of
; planning/evidence/vacuity-audit-2026-09-29.md).  The shared fixture is the
; actual Store node that published the K5 fixture's first article.
; lane assurance-hygiene-6, 2026-09-29.
(in-package "ACL2")
(include-book "../../books/byte-store-keystones")
(include-book "../../books/byte-store-record-provenance")
(include-book "../../books/byte-store-arena")
(include-book "byte-store-stable-prefix-tests")
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; The shared fixture: the actual Store node that published the K5 fixture's
; first article.  The node is driven by the same callbacks the host issues
; (fn-sn-io for each P-ALLOC/P-RECORD syscall result, fn-sn-prepare for the
; article, fn-sn-finish for the completion), and its file kernel is exactly
; the kernel of the byte run bsk5-finished: the node and the byte state are
; related, and the node carries its full consumer relation.
(defun bsnw-reserved ()
  (let ((s (fn-sn-initial *bsk5-groups* *bsk5-capacity*)))
    (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                  :frontier-file :ok)
                        :frontier-replace :ok)
              :frontier-directory :ok)))
(defun bsnw-node ()
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-prepare (bsnw-reserved) *bsk5-row*)
                                 :record-file :ok)
                       :record-link :ok)
             :record-directory :ok)))
(assert-event
 (and (fn-sn-statep (bsnw-node))
      (equal (fn-sn-files (bsnw-node)) (cdr (bsk5-finished)))
      (fn-csi-full-relationp (bsnw-node))
      (fn-bs-store-relation (car (bsk5-finished)) (fn-sn-files (bsnw-node)) *bsk5-arena*)
      (equal (fn-sf-phase (fn-sn-files (bsnw-node))) :ready)
      (equal (fn-sf-records (fn-sn-files (bsnw-node))) (list *bsk5-row*))
      (equal (fn-bs-durable-records (car (bsk5-finished))) (list *bsk5-record*))
      (equal (fn-sf-successes (fn-sn-files (bsnw-node))) '((0 . 0)))))

; The same node going on to the second article: the next allocation, the
; second article prepared, its record file durable.  Its kernel is exactly
; bsk5-linked-2's, whose byte state has the second transaction link pending
; (so its crash images hold one article or two).
(defun bsnw-node-2-reserved ()
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io (bsnw-node) :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun bsnw-node-2-durable ()
  (fn-sn-io (fn-sn-prepare (bsnw-node-2-reserved) *bsk5-row-2*) :record-file :ok))
(assert-event
 (and (equal (fn-sn-files (bsnw-node-2-reserved)) (cdr (bsk5-frontier-2)))
      (equal (fn-sn-files (bsnw-node-2-durable)) (cdr (bsk5-linked-2)))
      (fn-csi-full-relationp (bsnw-node-2-durable))
      (fn-bs-store-relation (car (bsk5-linked-2)) (fn-sn-files (bsnw-node-2-durable))
                            *bsk5-arena*)
      (equal (fn-sf-phase (fn-sn-files (bsnw-node-2-durable))) :record-data-durable)
      (consp (fn-bs-ops-for-dir (fn-bs-pending (car (bsk5-linked-2))) :transactions))
      (equal (fn-bs-durable-records (car (bsk5-linked-2))) (list *bsk5-record*))))

; Crash images: every pending op kept, or every one lost.
(defun bsnw-keep-choices (bs) (fn-bs-view-choices (fn-bs-pending bs) (fn-bs-unit bs)))
(defun bsnw-keep (bs) (fn-bs-crash bs (bsnw-keep-choices bs)))
(defun bsnw-lose (bs) (fn-bs-crash bs nil))
(defthm bsnw-lose-finished-is-a-crash-image
  (fn-bs-crash-imagep (car (bsk5-finished)) (bsnw-lose (car (bsk5-finished))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-crash-imagep)
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (car (bsk5-finished))) (choices nil)
                            (image (bsnw-lose (car (bsk5-finished)))))))))
(defthm bsnw-keep-linked-2-is-a-crash-image
  (fn-bs-crash-imagep (car (bsk5-linked-2)) (bsnw-keep (car (bsk5-linked-2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-crash-imagep)
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (car (bsk5-linked-2)))
                            (choices (bsnw-keep-choices (car (bsk5-linked-2))))
                            (image (bsnw-keep (car (bsk5-linked-2)))))))))
(defthm bsnw-lose-linked-2-is-a-crash-image
  (fn-bs-crash-imagep (car (bsk5-linked-2)) (bsnw-lose (car (bsk5-linked-2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-crash-imagep)
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (car (bsk5-linked-2))) (choices nil)
                            (image (bsnw-lose (car (bsk5-linked-2)))))))))
(assert-event
 (and (fn-bs-crash-choicesp nil (fn-bs-pending (car (bsk5-finished)))
                            (fn-bs-unit (car (bsk5-finished))))
      (fn-bs-crash-choicesp (bsnw-keep-choices (car (bsk5-linked-2)))
                            (fn-bs-pending (car (bsk5-linked-2)))
                            (fn-bs-unit (car (bsk5-linked-2))))
      (fn-bs-crash-choicesp nil (fn-bs-pending (car (bsk5-linked-2)))
                            (fn-bs-unit (car (bsk5-linked-2))))))

(defun bsnw-rows (s image) (fn-bs-scanned-rows (fn-sn-files s) image *bsk5-arena*))
(defun bsnw-opened (s image)
  (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                       (fn-bs-scan-frontier (fn-bs-scan-store image))
                       (bsnw-rows s image)))

;;; KEYSTONE fn-bs-crash-image-consumer-replay-ok (PRF-041, row B26 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; A crash image of a store related to a fully related Store node replays its consumer projection.
;;; KEYSTONE fn-bs-crash-image-reopens (PRF-041, row B27 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Such an image whose identity and topic histories replay reopens through fn-sn-open-observed.
;;; KEYSTONE fn-bs-acknowledged-record-survives-byte-crash (PRF-041, row B28 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; An outcome the node acknowledged before the crash names a record of the reopened state.
; One predicate carries the three theorems: the antecedents (the crash-image
; premise is the ground theorems above), the three conclusions, and the
; non-emptiness of the scanned history.
(defun bsnw-k4-okp (s bs image pair)
  (and (fn-csi-full-relationp s)
       (fn-bs-store-relation bs (fn-sn-files s) *bsk5-arena*)
       (consp (bsnw-rows s image))
       (fn-sn-observed-identity-okp (bsnw-rows s image))
       (fn-sn-observed-topic-okp (bsnw-rows s image))
       (member-equal pair (fn-sf-successes (fn-sn-files s)))
       (fn-sn-observed-consumer-okp (bsnw-rows s image))
       (fn-sn-open-okp (bsnw-opened s image))
       (fn-sf-record-has-pairp
        pair (fn-sf-records (fn-sn-files (fn-sn-open-state (bsnw-opened s image)))))))
(assert-event
 (and (bsnw-k4-okp (bsnw-node) (car (bsk5-finished))
                   (bsnw-lose (car (bsk5-finished))) '(0 . 0))
      (bsnw-k4-okp (bsnw-node-2-durable) (car (bsk5-linked-2))
                   (bsnw-keep (car (bsk5-linked-2))) '(0 . 0))
      (bsnw-k4-okp (bsnw-node-2-durable) (car (bsk5-linked-2))
                   (bsnw-lose (car (bsk5-linked-2))) '(0 . 0))
      (equal (bsnw-rows (bsnw-node) (bsnw-lose (car (bsk5-finished))))
             (list *bsk5-row*))
      (equal (bsnw-rows (bsnw-node-2-durable) (bsnw-keep (car (bsk5-linked-2))))
             (list *bsk5-row* *bsk5-row-2*))
      (equal (bsnw-rows (bsnw-node-2-durable) (bsnw-lose (car (bsk5-linked-2))))
             (list *bsk5-row*))))
; Drop the node relation: the node's first article under the empty kernel's
; byte image is not related, and its (empty) scan names no acknowledged pair.
(assert-event
 (not (fn-bs-store-relation (bsk5-initial) (fn-sn-files (bsnw-node)) *bsk5-arena*)))
(must-fail-checked
 (assert-event
  (bsnw-k4-okp (bsnw-node) (bsk5-initial) (bsk5-initial) '(0 . 0))))
; Drop the acknowledgement: no pair (1 . 1) was acknowledged, and none is held.
(must-fail-checked
 (assert-event
  (bsnw-k4-okp (bsnw-node) (car (bsk5-finished))
               (bsnw-lose (car (bsk5-finished))) '(1 . 1))))

;;; KEYSTONE fn-bs-sweep-round-keeps-every-cut-reopenable (PRF-041, row B29 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Every cut of the byte run of the names fn-sn-sweep-round returns keeps the kernel, the scan and the reopen.
; The sweep runs on a node that finished recovery: the node of the second
; article crashed with its link kept, reopened through fn-sn-open-observed,
; and passed the three recovery barriers to :ready.  Its byte state is the
; crash image, which still holds the second publication's staging name, and
; the kernel holds both articles.
(defun bsnw-crashed () (bsnw-keep (car (bsk5-linked-2))))
(defun bsnw-reopened ()
  (let ((s (fn-sn-open-state (bsnw-opened (bsnw-node-2-durable) (bsnw-crashed)))))
    (fn-sn-io (fn-sn-io (fn-sn-io s :recovery-barrier :ok) :recovery-barrier :ok)
              :recovery-barrier :ok)))
; The host observes the staging directory as octet names.
(defconst *bsnw-orphan* '(46 115 116 97 103 101 45 107 53 45 50)) ; .stage-k5-2
(defun bsnw-sweep-names ()
  (cadr (fn-sn-sweep-round (bsnw-reopened) (list *bsnw-orphan*) nil nil)))
(defun bsnw-sweep-run ()
  (fn-bs-run (bsnw-crashed) (fn-sn-files (bsnw-reopened))
             (fn-bs-recover-sweep-program (bsnw-sweep-names))
             nil *bsk5-groups* *bsk5-capacity*))
(defun bsnw-sweep-pair () (car (bsnw-sweep-run)))
(defthm bsnw-sweep-pair-lose-is-a-crash-image
  (fn-bs-crash-imagep (car (bsnw-sweep-pair)) (bsnw-lose (car (bsnw-sweep-pair))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bs-crash-imagep)
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (car (bsnw-sweep-pair))) (choices nil)
                            (image (bsnw-lose (car (bsnw-sweep-pair)))))))))
(defun bsnw-sweep-okp (s bs pair image)
  (and (fn-csi-full-relationp s)
       (fn-bs-store-relation bs (fn-sn-files s) *bsk5-arena*)
       (member-equal pair (fn-bs-run bs (fn-sn-files s)
                                     (fn-bs-recover-sweep-program (bsnw-sweep-names))
                                     nil *bsk5-groups* *bsk5-capacity*))
       (fn-sn-observed-identity-okp (bsnw-rows s image))
       (fn-sn-observed-topic-okp (bsnw-rows s image))
       (equal (cdr pair) (fn-sn-files s))
       (equal (fn-bs-scan-store (car pair)) (fn-bs-scan-store bs))
       (fn-sn-open-okp (bsnw-opened s image))))
(assert-event
 (let ((s (bsnw-reopened)) (bs (bsnw-crashed)))
   (and (equal (fn-sf-phase (fn-sn-files s)) :ready)
        (equal (fn-sf-records (fn-sn-files s)) (list *bsk5-row* *bsk5-row-2*))
        (fn-bs-lookup bs :staging ".stage-k5-2")
        (equal (fn-bs-pending bs) nil)
        (fn-bs-crash-choicesp nil (fn-bs-pending (car (bsnw-sweep-pair)))
                              (fn-bs-unit (car (bsnw-sweep-pair))))
        (equal (bsnw-sweep-names) (list *bsnw-orphan*))
        (bsnw-sweep-okp s bs (bsnw-sweep-pair) (bsnw-lose (car (bsnw-sweep-pair))))
        (equal (bsnw-rows s (bsnw-lose (car (bsnw-sweep-pair))))
               (list *bsk5-row* *bsk5-row-2*)))))
; FINDING (why B29 stays PARTIAL): the sweep's names are octet lists
; (fn-sn-staging-namep) and the byte model's names are strings (fn-bs-namep),
; so the composed program's unlink step is not an fn-bs-stepp and its model
; answer is :enoent: the run is the one failed-unlink pair and the orphan the
; byte state holds as ".stage-k5-2" is never removed.  The cut after an
; actual unlink (recovery-stage-unlinked) is unreachable from
; fn-sn-sweep-round's output in the byte model; the theorem is true there
; only because the byte state never changes.
(assert-event
 (let ((run (bsnw-sweep-run)))
   (and (equal (len run) 1)
        (not (fn-bs-namep *bsnw-orphan*))
        (equal (mv-let (r bs1) (fn-bs-unlink (bsnw-crashed) :staging *bsnw-orphan* :ok)
                 (declare (ignore bs1)) r)
               :enoent)
        (equal (car (bsnw-sweep-pair)) (bsnw-crashed))
        (fn-bs-lookup (car (bsnw-sweep-pair)) :staging ".stage-k5-2"))))
; Drop sweep enablement: before recovery the node is not :ready and the round
; removes nothing, so the run is empty and has no pair.
(assert-event
 (equal (fn-sn-sweep-round (fn-sn-open-state (bsnw-opened (bsnw-node-2-durable) (bsnw-crashed)))
                           (list *bsnw-orphan*) nil nil)
        '(:done nil)))

;;; KEYSTONE fn-bs-k0-frontier-node-root-eio-applied-fences-related-state (PRF-041, row B40 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; A root-directory EIO after the frontier rename, with the rename applied, fences the node at a related byte state holding the new frontier.
;;; KEYSTONE fn-bs-k0-frontier-node-root-eio-dropped-fences-related-state (PRF-041, row B44 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; The same EIO with the rename dropped fences the node at a related byte state keeping the old frontier.
; From the fixture node holding article 1 (bsk5-finished), the second
; allocation's callbacks :start-frontier .. :frontier-replace, then the root
; fsync's EIO under either legal choice.
(defun bsnw-eio-failed (bs ks stage octets choice)
  (let ((file (car (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                                     nil *bsk5-groups* *bsk5-capacity*)))))
    (mv-let (r renamed)
      (fn-bs-rename file :staging stage :root *fn-bs-frontier-name* :ok)
      (declare (ignore r))
      (mv-let (r failed) (fn-bs-fsync-dir renamed :root (list :eio choice))
        (declare (ignore r))
        failed))))
(defun bsnw-node-s3 (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier :ok) :frontier-file :ok)
            :frontier-replace :ok))
(defun bsnw-node-eio-okp (s bs stage octets choice)
  (let* ((ks (fn-sn-files s))
         (run (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                         nil *bsk5-groups* *bsk5-capacity*))
         (failed (bsnw-eio-failed bs ks stage octets choice))
         (s3 (bsnw-node-s3 s))
         (s4 (fn-sn-io s3 :frontier-directory :error)))
    (and (fn-sn-statep s)
         (fn-bs-store-relation bs ks *bsk5-arena*)
         (fn-bs-frontier-inputp ks stage octets)
         (not (fn-bs-lookup bs :staging stage))
         (if (equal choice :apply)
             (and (equal failed (car (nth 12 run)))
                  (equal (fn-bs-durable-frontier failed)
                         (fn-sf-frontier-candidate (fn-sn-files s3))))
           (equal (fn-bs-durable-frontier failed) (fn-bs-durable-frontier bs)))
         (fn-bs-store-relation failed (fn-sn-files s4) *bsk5-arena*)
         (equal (fn-sf-phase (fn-sn-files s4)) :fenced-frontier)
         (equal (fn-bs-durable-records failed) (list *bsk5-record*)))))
(assert-event
 (let ((s (bsnw-node)) (bs (car (bsk5-finished)))
       (stage ".allocation-k5-2") (octets (fn-bs-frontier-encode 2)))
   (and (bsnw-node-eio-okp s bs stage octets :apply)
        (bsnw-node-eio-okp s bs stage octets :drop)
        (equal (fn-bs-durable-frontier
                (bsnw-eio-failed bs (fn-sn-files s) stage octets :apply)) 2)
        (equal (fn-bs-durable-frontier
                (bsnw-eio-failed bs (fn-sn-files s) stage octets :drop)) 1))))
; Drop the input contract: the first allocation's frontier octets again.
(assert-event
 (not (fn-bs-frontier-inputp (fn-sn-files (bsnw-node)) ".allocation-k5-2"
                             (fn-bs-frontier-encode 1))))
(must-fail-checked
 (assert-event
  (bsnw-node-eio-okp (bsnw-node) (car (bsk5-finished)) ".allocation-k5-2"
                     (fn-bs-frontier-encode 1) :apply)))
; Drop the relation: the node that holds article 1 over the initial image.
(must-fail-checked
 (assert-event
  (bsnw-node-eio-okp (bsnw-node) (bsk5-initial) ".allocation-k5-2"
                     (fn-bs-frontier-encode 2) :drop)))

;;; KEYSTONE fn-bs-k0-owner-frontier-root-eio-applied-run-fences-related-state (PRF-041, row B42 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Through the owner's :store/:io callbacks, the applied root EIO run's failing cut is related to the fenced node and holds the new frontier.
;;; KEYSTONE fn-bs-k0-owner-frontier-root-eio-dropped-run-fences-related-state (PRF-041, row B45 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; The dropped root EIO run has 13 pairs, its failing cut is related to the fenced node and keeps the old frontier.
;;; KEYSTONE fn-bs-k0-owner-frontier-root-eio-choice-run-fences-related-state (PRF-041, row B47 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; For either fsync choice, the run has 13 pairs and its failing cut is related to the fenced node with the chosen frontier.
; The owner whose Store is the fixture node (article 1 retained), over
; bsk5-finished's byte state; the arena holds the fixture's two payloads.
(defun bsnw-owner ()
  (fn-ocfg-make
   (fn-own-start (bsnw-node) 2)
   (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*))
   nil nil))
(defun bsnw-owner-eio-okp (bs oc stage octets choice fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (run (fn-bs-run bs (fn-sn-files s) (fn-bs-frontier-program stage octets)
                         (fn-bs-k0-root-error-outcomes choice)
                         *bsk5-groups* *bsk5-capacity*))
         (failed (car (nth 12 run)))
         (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok)) fn-arena))
         (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok)) fn-arena))
         (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok)) fn-arena))
         (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :error)) fn-arena))
         (k3 (fn-sn-files (fn-own-store (fn-ocfg-owner oc3))))
         (k4 (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))))
    (and (fn-sn-statep s)
         (fn-bs-store-relation bs (fn-sn-files s) *bsk5-arena*)
         (fn-bs-frontier-inputp (fn-sn-files s) stage octets)
         (not (fn-bs-lookup bs :staging stage))
         (equal (len run) 13)
         (fn-bs-store-relation failed k4 *bsk5-arena*)
         (equal (fn-sf-phase k4) :fenced-frontier)
         (equal (fn-bs-durable-frontier failed)
                (if (equal choice :apply)
                    (fn-sf-frontier-candidate k3)
                  (fn-bs-durable-frontier bs)))
         (equal (fn-bs-durable-records failed) (list *bsk5-record*)))))
(include-book "arena-lift")
(bpr-lift bsnw-owner-eio-okp 5)
(assert-event
 (let ((bs (car (bsk5-finished))) (oc (bsnw-owner))
       (stage ".allocation-k5-2") (octets (fn-bs-frontier-encode 2)))
   (and (equal (fn-own-store (fn-ocfg-owner oc)) (bsnw-node))
        (fn-ocfg-statep oc)
        (in-arena-bsnw-owner-eio-okp *bsk5-arena* bs oc stage octets :apply)
        (in-arena-bsnw-owner-eio-okp *bsk5-arena* bs oc stage octets :drop)
        (equal (fn-bs-durable-frontier
                (car (nth 12 (fn-bs-run bs (fn-sn-files (bsnw-node))
                                        (fn-bs-frontier-program stage octets)
                                        (fn-bs-k0-root-error-outcomes :apply)
                                        *bsk5-groups* *bsk5-capacity*))))
               2)
        (equal (fn-bs-durable-frontier
                (car (nth 12 (fn-bs-run bs (fn-sn-files (bsnw-node))
                                        (fn-bs-frontier-program stage octets)
                                        (fn-bs-k0-root-error-outcomes :drop)
                                        *bsk5-groups* *bsk5-capacity*))))
               1))))
; Drop the absent stage: O_EXCL stops the run before the root fsync.
(must-fail-checked
 (assert-event
  (in-arena-bsnw-owner-eio-okp
   *bsk5-arena*
   (mv-let (r bs1) (fn-bs-create (car (bsk5-finished)) :staging ".allocation-k5-2" :ok)
     (declare (ignore r)) bs1)
   (bsnw-owner) ".allocation-k5-2" (fn-bs-frontier-encode 2) :apply)))

;;; KEYSTONE fn-bs-k0-served-article-prepare-to-attempted-relation (no PRF cites it, row B59 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; A reserved node that prepares a retained article row reaches a related P-RECORD attempted cut (pair 10) with the host's frame and name.
(defun bsnw-host-frame (row)
  (let ((octets (fn-store-event-encode (fn-bs-row-wire row *bsk5-arena*))))
    (append (fn-frame-store-protected octets)
            (fn-frame-trailer (fn-frame-store-protected octets)))))
(defun bsnw-attempted (bs s record stage)
  (nth 10 (fn-bs-run bs (fn-sn-files (fn-sn-prepare s record))
                     (fn-bs-record-program stage
                                           (fn-bs-txn-name (fn-store-event-sequence record))
                                           (bsnw-host-frame record))
                     nil *bsk5-groups* *bsk5-capacity*)))
(defun bsnw-b59-okp (bs s record stage)
  (let ((cut (bsnw-attempted bs s record stage)))
    (and (fn-bs-store-relation bs (fn-sn-files s) *bsk5-arena*)
         (equal (fn-sf-phase (fn-sn-files s)) :reserved)
         (equal (fn-sf-phase (fn-sn-files (fn-sn-prepare s record))) :record-staged)
         (fn-record-p (fn-bs-row-wire record *bsk5-arena*))
         (fn-bs-namep stage)
         (not (fn-bs-lookup bs :staging stage))
         (fn-bs-store-relation (car cut) (cdr cut) *bsk5-arena*))))
; The first article from the reserved fixture node, and the second article
; from the same node after it published the first: the store the second
; prepare runs over already holds article 1, and so does its attempted cut.
(assert-event
 (and (fn-record-p (fn-bs-row-wire *bsk5-row* *bsk5-arena*))
      (bsnw-b59-okp (car (car (last (bsk5-frontier-run)))) (bsnw-reserved)
                    *bsk5-row* ".stage-k5")
      (bsnw-b59-okp (car (bsk5-frontier-2)) (bsnw-node-2-reserved)
                    *bsk5-row-2* ".stage-k5-2")
      (equal (fn-bs-durable-records (car (bsk5-frontier-2))) (list *bsk5-record*))
      (equal (fn-sf-phase (cdr (bsnw-attempted (car (bsk5-frontier-2)) (bsnw-node-2-reserved)
                                               *bsk5-row-2* ".stage-k5-2")))
             :record-attempted)
      (equal (fn-bs-durable-records
              (car (bsnw-attempted (car (bsk5-frontier-2)) (bsnw-node-2-reserved)
                                   *bsk5-row-2* ".stage-k5-2")))
             (list *bsk5-record*))))
; Drop the reserved phase: the node that published article 1 is :ready, so
; its prepare stages nothing and the pair-10 cut is not related.
(assert-event (equal (fn-sf-phase (fn-sn-files (bsnw-node))) :ready))
(must-fail-checked
 (assert-event
  (let ((cut (bsnw-attempted (car (bsk5-finished)) (bsnw-node) *bsk5-row-2* ".stage-k5-2")))
    (fn-bs-store-relation (car cut) (cdr cut) *bsk5-arena*))))

;;; KEYSTONE fn-bs-k0-entry-article-arguments-are-typed-record-input (no PRF cites it, row B60 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; The staged retained row, framed through the entry's alpha fn-row-wire-of over the live arena, is a typed P-RECORD input.
; The live fn-arena holds the fixture's two payloads (sealed by the lift);
; fn-row-wire-of is read from the stobj, and the arena's logical value is
; pinned to *bsk5-arena* by its count and each payload, so the input check
; over *bsk5-arena* is the theorem's conclusion over this fn-arena.
(defun bsnw-b60-okp (ks row stage fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((w (fn-row-wire-of row fn-arena))
         (frame (append (fn-frame-store-protected (fn-store-event-encode w))
                        (fn-frame-trailer
                         (fn-frame-store-protected (fn-store-event-encode w))))))
    (and (equal (fn-arena-count fn-arena) 2)
         (equal (list (fn-arena-payload 0 fn-arena) (fn-arena-payload 1 fn-arena))
                *bsk5-arena*)
         (fn-record-p w)
         (equal (fn-sf-phase ks) :record-staged)
         (equal (fn-sf-record-candidate ks) row)
         (fn-bs-namep stage)
         (fn-bs-record-inputp ks stage (fn-bs-txn-name (fn-store-event-sequence row))
                              frame *bsk5-arena*))))
(bpr-lift bsnw-b60-okp 3)
(assert-event
 (and (in-arena-bsnw-b60-okp *bsk5-arena*
                             (fn-sn-files (fn-sn-prepare (bsnw-reserved) *bsk5-row*))
                             *bsk5-row* ".stage-k5")
      (in-arena-bsnw-b60-okp *bsk5-arena*
                             (fn-sn-files (fn-sn-prepare (bsnw-node-2-reserved) *bsk5-row-2*))
                             *bsk5-row-2* ".stage-k5-2")))
; The conclusion has teeth: the first article's frame is not a typed input
; for the second article's staged row.  (The fn-record-p premise alone is
; weak: a row whose handle the arena lacks still has a record-shaped alpha,
; (fn-record-p (fn-bs-row-wire *bsk5-row-2* (list '(65)))), with a nil payload.)
(assert-event
 (and (fn-record-p (fn-bs-row-wire *bsk5-row-2* (list '(65))))
      (not (fn-bs-record-inputp
            (fn-sn-files (fn-sn-prepare (bsnw-node-2-reserved) *bsk5-row-2*))
            ".stage-k5-2" (fn-bs-txn-name 1) (bsnw-host-frame *bsk5-row*) *bsk5-arena*))))
; Drop the arena: without the second payload the live arena is not the
; relation's arena.
(must-fail-checked
 (assert-event
  (in-arena-bsnw-b60-okp (list (car *bsk5-arena*))
                         (fn-sn-files (fn-sn-prepare (bsnw-node-2-reserved) *bsk5-row-2*))
                         *bsk5-row-2* ".stage-k5-2")))
