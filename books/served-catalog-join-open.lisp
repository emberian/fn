;; served-catalog-join-open.lisp -- the row relation at the opens (lane
; sca-join-2, 2026-09-27; E of PRF-302).
;
; The node the replay folds (books/config-physical-replay.lisp fn-cpr-loop,
; the one-record step fn-replay-apply-record) and the catalog the host loads
; from the same rows (books/served-catalog-owner.lisp fn-sca-load-held-row)
; keep fn-scj-acc-rowsp (books/served-catalog-join-number.lisp) event for
; event: an article or composite row is prepared and installed by the node
; and committed (visible or hidden) by the load; a configuration record
; grows the domain at watermark 1; every other event keeps the acceptance's
; articles, watermarks and domain and is skipped by the load.

(in-package "ACL2")

(include-book "served-catalog-join-number")

(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; The node's side of one replayed record.

(defthm fn-scj-acc-rowsp-of-same-fields
  (implies (and (equal (fn-state-articles a) (fn-state-articles b))
                (equal (fn-state-nexts a) (fn-state-nexts b))
                (equal (fn-state-groups a) (fn-state-groups b)))
           (equal (fn-scj-acc-rowsp a c) (fn-scj-acc-rowsp b c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scj-acc-rowsp))))

(defthm fn-scj-advance-txid-keeps-fields
  (let ((a (fn-node-acceptance (fn-replay-advance-txid node x))))
    (implies (consp (fn-replay-advance-txid node x))
             (and (equal (fn-state-articles a) (fn-state-articles (fn-node-acceptance node)))
                  (equal (fn-state-nexts a) (fn-state-nexts (fn-node-acceptance node)))
                  (equal (fn-state-groups a) (fn-state-groups (fn-node-acceptance node))))))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-scj-node-prepare-staged
  (implies (and (null (fn-node-stage s))
                (consp (fn-node-stage (fn-node-prepare s generation msgid payload groups
                                                       obligation-id subject evidence charge stamp))))
           (and (equal (fn-node-acceptance (fn-node-prepare s generation msgid payload groups
                                                            obligation-id subject evidence charge stamp))
                       (fn-accept-prepare (fn-node-acceptance s) generation msgid payload groups stamp))
                (not (equal (fn-accept-prepare (fn-node-acceptance s) generation msgid payload groups stamp)
                            (fn-node-acceptance s)))))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare) (fn-accept-prepare fn-retain-admissiblep fn-retain-admit)))))

(defthm fn-scj-node-complete-durable-installs
  (implies (fn-node-pending-matchesp s txid generation)
           (equal (fn-node-acceptance (fn-node-complete s txid generation :durable))
                  (fn-install-pending (fn-node-acceptance s))))
  :hints (("Goal" :in-theory (e/d (fn-node-complete fn-node-pending-matchesp fn-accept-complete fn-node-statep)
                                  (fn-install-pending)))))

(defthm fn-scj-advance-txid-unstaged
  (implies (null (fn-node-stage node))
           (null (fn-node-stage (fn-replay-advance-txid node x))))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-scj-article-arm-keeps-acc-rowsp
  (let* ((adv (fn-replay-advance-txid node x))
         (prepared (fn-node-prepare adv (fn-record-generation h) (fn-record-msgid h)
                                    (fn-record-payload h) (fn-record-groups h)
                                    oid subj ev charge (fn-record-stamp h))))
    (implies (and (null (fn-node-stage node))
                  (consp adv)
                  (fn-node-pending-matchesp prepared txid gen)
                  (fn-scj-acc-rowsp (fn-node-acceptance node) c))
             (and (fn-scj-acc-rowsp (fn-node-acceptance (fn-node-complete prepared txid gen :durable))
                                    (fn-cat-commit h c))
                  (fn-scj-acc-rowsp (fn-node-acceptance (fn-node-complete prepared txid gen :durable))
                                    (fn-cat-commit (fn-held-with-withdrawn h w) c)))))
  :hints (("Goal" :in-theory (e/d (fn-node-pending-matchesp)
                                  (fn-node-prepare fn-node-complete fn-replay-advance-txid
                                   fn-accept-prepare fn-install-pending fn-scj-acc-rowsp
                                   fn-cat-commit-is-append fn-held-with-withdrawn))
           :use ((:instance fn-scj-advance-txid-unstaged)
                 (:instance fn-scj-node-prepare-staged
                            (s (fn-replay-advance-txid node x))
                            (generation (fn-record-generation h)) (msgid (fn-record-msgid h))
                            (payload (fn-record-payload h)) (groups (fn-record-groups h))
                            (obligation-id oid) (subject subj) (evidence ev) (stamp (fn-record-stamp h)))
                 (:instance fn-scj-acc-rowsp-of-same-fields
                            (a (fn-node-acceptance (fn-replay-advance-txid node x)))
                            (b (fn-node-acceptance node)))
                 (:instance fn-scj-acc-rowsp-of-install
                            (s (fn-node-acceptance (fn-replay-advance-txid node x)))
                            (generation (fn-record-generation h)))
                 (:instance fn-scj-acc-rowsp-of-install-withdrawn
                            (s (fn-node-acceptance (fn-replay-advance-txid node x)))
                            (generation (fn-record-generation h)))))))
