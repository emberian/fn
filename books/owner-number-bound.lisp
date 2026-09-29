; owner-number-bound.lisp -- RFC 3977 section 6's article-number bound carried
; by the owner (lane join-f2-5, 2026-09-29; PKT-615's follow-up, NNT-057).
;
; This book owns the prefix `fn-onb-' (docs/prefixes.md).

(in-package "ACL2")

(include-book "owner-prepare-served")
(include-book "owner-prepare-outcome")

;; ---------------------------------------------------------------------------
;; The node: every watermark an article number, and the article in flight
;; (the acceptance's pending allocation) fits at them.

(defun-nx fn-onb-node-boundp (node)
  (let ((a (fn-node-acceptance node)))
    (and (fn-nntp-nexts-boundedp (fn-state-nexts a))
         (implies (fn-state-pending a)
                  (fn-snb-groups-fitp (fn-pending-groups (fn-state-pending a))
                                      (fn-state-nexts a))))))

(defthm fn-onb-node-boundp-of-nil
  (fn-onb-node-boundp nil)
  :hints (("Goal" :in-theory (enable fn-onb-node-boundp))))

(defthm fn-onb-groups-fitp-of-atom
  (implies (not (consp groups)) (fn-snb-groups-fitp groups nexts))
  :hints (("Goal" :in-theory (enable fn-snb-groups-fitp))))

(defthm fn-onb-advance-txid-pending
  (equal (fn-state-pending (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-pending (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (e/d (fn-replay-advance-txid) (fn-node-statep)))))

(defthm fn-onb-node-prepare-pending-fits
  (implies (and (fn-snb-groups-fitp groups (fn-state-nexts (fn-node-acceptance s)))
                (implies (fn-state-pending (fn-node-acceptance s))
                         (fn-snb-groups-fitp (fn-pending-groups (fn-state-pending (fn-node-acceptance s)))
                                             (fn-state-nexts (fn-node-acceptance s))))
                (fn-state-pending (fn-node-acceptance
                                   (fn-node-prepare s generation msgid payload groups id subject
                                                    evidence charge stamp))))
           (fn-snb-groups-fitp (fn-pending-groups
                                (fn-state-pending (fn-node-acceptance
                                                   (fn-node-prepare s generation msgid payload groups id subject
                                                                    evidence charge stamp))))
                               (fn-state-nexts (fn-node-acceptance s))))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare)
                                  (fn-node-statep fn-accept-prepare fn-retain-admissiblep fn-retain-admit
                                   fn-snb-groups-fitp))
           :use ((:instance fn-snb-accept-prepare-pending-groups
                            (s (fn-node-acceptance s)) (groups groups))))))

;; Each node step: the retention and identity-neutral steps, the completion,
;; the txid advance, the prepare of an article that fits, and so every
;; replayed record the admission let through.

(defthm fn-onb-node-boundp-of-retention-event
  (implies (fn-onb-node-boundp node)
           (fn-onb-node-boundp (fn-replay-apply-retention-event node event)))
  :hints (("Goal" :in-theory (e/d (fn-onb-node-boundp fn-replay-apply-retention-event fn-replay-complete-retention
                                   fn-replay-node-with-retention)
                                  (fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-node-statep)))))

(defthm fn-onb-node-boundp-of-identity-neutral
  (implies (fn-onb-node-boundp node)
           (fn-onb-node-boundp (fn-replay-apply-identity-neutral node event)))
  :hints (("Goal" :in-theory (e/d (fn-onb-node-boundp fn-replay-apply-identity-neutral)
                                  (fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-node-statep)))))

(defthm fn-onb-node-boundp-of-complete
  (implies (fn-onb-node-boundp node)
           (fn-onb-node-boundp (fn-node-complete node txid generation status)))
  :hints (("Goal" :in-theory (e/d (fn-onb-node-boundp fn-node-complete fn-accept-complete fn-install-pending
                                   fn-clear-pending fn-node-pending-matchesp)
                                  (fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-node-statep fn-advance-nexts
                                   fn-statep fn-pending-matchesp)))))

(defthm fn-onb-node-boundp-of-advance-txid
  (equal (fn-onb-node-boundp (fn-replay-advance-txid node txid))
         (fn-onb-node-boundp node))
  :hints (("Goal" :in-theory (e/d (fn-onb-node-boundp) (fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-replay-advance-txid)))))

(defthm fn-onb-node-boundp-of-prepare
  (implies (and (fn-onb-node-boundp s)
                (fn-snb-groups-fitp groups (fn-state-nexts (fn-node-acceptance s))))
           (fn-onb-node-boundp (fn-node-prepare s generation msgid payload groups id subject
                                                evidence charge stamp)))
  :hints (("Goal" :in-theory (e/d (fn-onb-node-boundp) (fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-node-prepare))
           :use ((:instance fn-onb-node-prepare-pending-fits)))))

(defthm fn-onb-node-boundp-of-replay-apply-record
  (implies (and (fn-onb-node-boundp node)
                (fn-snb-record-fitp node record))
           (fn-onb-node-boundp (fn-replay-apply-record node record)))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record fn-snb-record-fitp fn-snb-record-article)
                                  (fn-onb-node-boundp fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-node-prepare
                                   fn-node-complete fn-replay-advance-txid fn-replay-apply-retention-event
                                   fn-replay-apply-identity-neutral fn-node-statep fn-held-p fn-hstxa-p
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-cpe-eventp fn-th-topic-eventp
                                   fn-node-pending-matchesp)))))

(defthm fn-onb-node-boundp-of-sn-prepare-node
  (implies (and (fn-onb-node-boundp node)
                (fn-snb-groups-fitp (fn-record-groups record) (fn-state-nexts (fn-node-acceptance node))))
           (fn-onb-node-boundp (fn-sn-prepare-node node record)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare-node) (fn-onb-node-boundp fn-node-prepare fn-replay-advance-txid)))))

;; ---------------------------------------------------------------------------
;; The Store: its node.  The prepare stages only a record the admission let
;; through (books/owner-prepare-served.lisp fn-psrv-event-numberedp is
;; fn-snb-record-fitp at this node); the io steps leave the node; the finish
;; applies the completion record, which fits at the node.

(defun-nx fn-onb-store-boundp (s)
  (fn-onb-node-boundp (fn-sn-node s)))

(defthm fn-onb-store-boundp-of-prepare
  (implies (and (fn-onb-store-boundp s)
                (fn-snb-record-fitp (fn-sn-node s) record))
           (fn-onb-store-boundp (fn-sn-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-onb-store-boundp fn-sn-prepare-node fn-snb-record-fitp
                                   fn-snb-record-article)
                                  (fn-onb-node-boundp fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-node-prepare
                                   fn-replay-advance-txid fn-sf-prepare-record fn-cpe-projection-step
                                   fn-sn-statep fn-node-statep fn-sn-record-bindsp)))))

(defthm fn-onb-store-boundp-of-io
  (implies (fn-onb-store-boundp s)
           (fn-onb-store-boundp (fn-sn-io s operation result)))
  :hints (("Goal" :in-theory (e/d (fn-sn-io fn-onb-store-boundp)
                                  (fn-onb-node-boundp fn-sn-file-step fn-sn-statep)))))

(defthm fn-onb-store-boundp-of-finish
  (implies (and (fn-onb-store-boundp s)
                (fn-snb-record-fitp (fn-sn-node s) (fn-sn-completion-record s)))
           (fn-onb-store-boundp (fn-sn-finish s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-onb-store-boundp)
                                  (fn-onb-node-boundp fn-node-complete fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-sf-core-completion fn-sf-emit-success
                                   fn-cpe-projection-step fn-th-prefix-step fn-sn-statep fn-node-statep
                                   fn-sn-completion-enabledp fn-sn-completion-record fn-snb-record-fitp
                                   fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp fn-stxe-p
                                   fn-stxk-p fn-hstxa-p)))))

(defthm fn-onb-store-boundp-of-spc-prepare
  (implies (and (fn-onb-store-boundp s)
                (fn-snb-record-fitp (fn-sn-node s) record))
           (fn-onb-store-boundp (fn-spc-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare fn-onb-store-boundp fn-snb-record-fitp fn-snb-record-article)
                                  (fn-onb-node-boundp fn-sn-prepare-node fn-spc-stage-record
                                   fn-cpe-projection-step fn-sn-statep fn-node-statep fn-sn-record-bindsp
                                   fn-snb-groups-fitp)))))
(defthm fn-onb-store-boundp-of-prc-spc-prepare
  (implies (and (fn-onb-store-boundp s)
                (fn-snb-record-fitp (fn-sn-node s) record)
                (fn-prc-carryp carry)
                (fn-pidx-view-okp view))
           (fn-onb-store-boundp (fn-prc-spc-prepare s record view carry)))
  :hints (("Goal" :in-theory (disable fn-onb-store-boundp fn-prc-spc-prepare fn-spc-prepare))))

;; ---------------------------------------------------------------------------
;; The owner: its Store and its view.  The refresh reads the view's archive
;; off the Store's node (fn-ctl-visible-state-of keeps the watermarks).

(defun-nx fn-onb-boundp (o)
  (and (fn-onb-store-boundp (fn-own-store o))
       (fn-nntp-nexts-boundedp
        (fn-state-nexts (fn-own-view-archive (fn-own-view o))))))

(defthm fn-onb-boundp-of-refresh
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-refresh o)))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh fn-onb-boundp fn-onb-store-boundp fn-onb-node-boundp)
                                  (fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-visible fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-refresh-withdrawn)))))

(defthm fn-onb-boundp-of-same-store-and-view
  (implies (and (fn-onb-boundp o)
                (equal (fn-own-store o2) (fn-own-store o))
                (equal (fn-own-view o2) (fn-own-view o)))
           (fn-onb-boundp o2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-onb-boundp) (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; The admission's article prepare.  host/owner-host.lisp fn-owner-prepare-
;; buffer calls fn-pout-prepare-article, whose owner is fn-psrv-prepare's: it
;; stages only a record fn-psrv-event-numberedp admits (RFC 3977 section 6,
;; NNT-057), so the staged allocation fits at the node's watermarks.

(defthm fn-onb-boundp-of-prc-opc-owner-prepare
  (implies (and (fn-onb-boundp o)
                (fn-snb-record-fitp (fn-sn-node (fn-own-store o)) record)
                (fn-prc-carryp carry)
                (fn-pidx-view-okp (fn-own-view o)))
           (fn-onb-boundp (fn-prc-opc-owner-prepare o record carry)))
  :hints (("Goal" :in-theory (e/d (fn-prc-opc-owner-prepare)
                                  (fn-onb-store-boundp fn-prc-spc-prepare fn-own-refresh fn-onb-boundp
                                   fn-prc-opc-owner-prepare-is-pidx-opc-owner-prepare
                                   fn-prc-spc-prepare-is-pidx-spc-prepare))
           :use ((:instance fn-onb-boundp-of-refresh
                            (o (fn-own-make (fn-prc-spc-prepare (fn-own-store o) record (fn-own-view o) carry)
                                            (fn-own-view o) (fn-own-conns o)
                                            (fn-own-next-id o) (fn-own-max-conns o)
                                            (fn-own-pending o) (fn-own-ledger-field o)
                                            (fn-own-clock o) (fn-own-facts o)
                                            (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o)
                                            (fn-own-refused o))))
                 (:instance fn-onb-boundp (o (fn-own-make (fn-prc-spc-prepare (fn-own-store o) record (fn-own-view o) carry)
                                            (fn-own-view o) (fn-own-conns o)
                                            (fn-own-next-id o) (fn-own-max-conns o)
                                            (fn-own-pending o) (fn-own-ledger-field o)
                                            (fn-own-clock o) (fn-own-facts o)
                                            (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o)
                                            (fn-own-refused o))))
                 (:instance fn-onb-boundp)))))

(defthm fn-onb-boundp-of-psrv-prepare
  (implies (and (fn-onb-boundp (fn-ocfg-owner oc))
                (fn-prc-carryp carry)
                (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner oc))))
           (fn-onb-boundp (fn-ocfg-owner (fn-psrv-prepare oc record budget carry))))
  :hints (("Goal" :in-theory (e/d (fn-psrv-prepare fn-prc-sbud-prepare fn-prc-opc-prepare fn-psrv-event-numberedp)
                                  (fn-onb-boundp fn-prc-opc-owner-prepare fn-sbud-admitp
                                   fn-prc-sbud-prepare-is-pidx-sbud-prepare fn-prc-opc-prepare-is-pidx-opc-prepare
                                   fn-prc-opc-owner-prepare-is-pidx-opc-owner-prepare)))))

(defthm fn-onb-boundp-at-owner-prepare-buffer
  (implies (and (fn-onb-boundp (fn-ocfg-owner oc))
                (fn-prc-carryp carry)
                (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner oc))))
           (fn-onb-boundp (fn-ocfg-owner (mv-nth 1 (fn-pout-prepare-article oc record budget carry)))))
  :hints (("Goal" :in-theory (e/d (fn-pout-prepare-article) (fn-psrv-prepare fn-onb-boundp fn-pout-stagedp
                                                             fn-psrv-refusal-kind)))))
