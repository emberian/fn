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
;; The Store: its node, and the record in flight.  A staged or completing
;; record that is not a held row fits at the node (a held row's allocation is
;; the node's pending, which fn-onb-node-boundp carries).  The identity
;; prepare stages only a composite the admission let through
;; (books/owner-prepare-served.lisp fn-psrv-event-numberedp is
;; fn-snb-record-fitp at this node); the io steps keep the node and the
;; candidate, and the record directory's :ok makes the candidate the
;; completion record (books/config-store-steps.lisp
;; fn-cstp-completion-record-after-dir); so the finish applies a record that
;; fits.

(defun-nx fn-onb-inflight-fitp (s)
  (let* ((files (fn-sn-files s))
         (phase (fn-sf-phase files)))
    (and (implies (fn-sf-record-phasep phase)
                  (or (fn-held-p (fn-sf-record-candidate files))
                      (fn-snb-record-fitp (fn-sn-node s) (fn-sf-record-candidate files))))
         (implies (equal phase :completing)
                  (or (fn-held-p (fn-sn-completion-record s))
                      (fn-snb-record-fitp (fn-sn-node s) (fn-sn-completion-record s)))))))

(in-theory (disable fn-onb-inflight-fitp))

(defthm fn-onb-file-step-record-phase
  (implies (fn-sf-record-phasep (fn-sf-phase (fn-sn-file-step files operation result)))
           (and (fn-sf-record-phasep (fn-sf-phase files))
                (equal (fn-sf-record-candidate (fn-sn-file-step files operation result))
                       (fn-sf-record-candidate files))))
  :hints (("Goal" :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier fn-sf-frontier-file-result
                                   fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                                   fn-sf-record-file-result fn-sf-record-link-result fn-sf-record-dir-result
                                   fn-sf-recovery-barrier)
                                  (fn-sf-statep)))))
(defthm fn-onb-file-step-completing
  (implies (equal (fn-sf-phase (fn-sn-file-step files operation result)) :completing)
           (or (equal (fn-sn-file-step files operation result) files)
               (and (equal (fn-sf-phase files) :record-attempted)
                    (equal operation :record-directory)
                    (equal result :ok))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sn-file-step fn-sf-start-frontier fn-sf-frontier-file-result
                                   fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                                   fn-sf-record-file-result fn-sf-record-link-result fn-sf-record-dir-result
                                   fn-sf-recovery-barrier)
                                  (fn-sf-statep)))))
; The record-directory step completes a record; the completion record is the
; candidate only on a store state (fn-cstp-completion-record-after-dir: off
; the state the history may hold an earlier record with the same pair, and
; fn-sn-io has no identity arm since lane carrier S1).  Every other io step
; keeps the bound unconditionally.
(defthm fn-onb-inflight-fitp-of-io
  (implies (and (fn-onb-inflight-fitp s)
                (or (fn-sn-statep s) (not (equal operation :record-directory))))
           (fn-onb-inflight-fitp (fn-sn-io s operation result)))
  :hints (("Goal" :in-theory (e/d (fn-sn-io fn-onb-inflight-fitp)
                                  (fn-sn-file-step fn-sn-statep fn-snb-record-fitp fn-held-p
                                   fn-sf-record-phasep fn-cstp-completion-record-after-dir))
           :use ((:instance fn-onb-file-step-completing (files (fn-sn-files s)))
                 (:instance fn-cstp-completion-record-after-dir)))
          (and stable-under-simplificationp '(:in-theory (enable fn-sn-completion-record)))))
(defthm fn-onb-inflight-fitp-of-prepare
  (implies (fn-onb-inflight-fitp s)
           (fn-onb-inflight-fitp (fn-sn-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-onb-inflight-fitp fn-sf-prepare-record)
                                  (fn-sn-statep fn-sf-statep fn-snb-record-fitp fn-sn-prepare-node
                                   fn-sf-candidatep fn-sf-history-recoverablep fn-cpe-projection-step
                                   fn-sn-record-bindsp fn-node-statep fn-sn-completion-record)))))
(defthm fn-onb-inflight-fitp-of-spc-prepare
  (implies (fn-onb-inflight-fitp s)
           (fn-onb-inflight-fitp (fn-spc-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare fn-onb-inflight-fitp fn-spc-stage-record)
                                  (fn-sn-statep fn-sf-statep fn-snb-record-fitp fn-sn-prepare-node
                                   fn-sf-candidatep fn-cpe-projection-step
                                   fn-sn-record-bindsp fn-node-statep fn-sn-completion-record)))))
(defthm fn-onb-inflight-fitp-of-finish
  (implies (fn-sn-completion-enabledp s)
           (fn-onb-inflight-fitp (fn-sn-finish s)))
  :hints (("Goal" :in-theory (e/d (fn-onb-inflight-fitp) (fn-sn-finish fn-sn-completion-enabledp))
           :use fn-snt-finish-image)))


(defun-nx fn-onb-store-boundp (s)
  (and (fn-onb-node-boundp (fn-sn-node s))
       (fn-onb-inflight-fitp s)))


(defthm fn-onb-store-boundp-of-prepare
  (implies (and (fn-onb-store-boundp s)
                (fn-snb-record-fitp (fn-sn-node s) record))
           (fn-onb-store-boundp (fn-sn-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-onb-store-boundp fn-sn-prepare-node fn-snb-record-fitp
                                   fn-snb-record-article)
                                  (fn-onb-node-boundp fn-snb-groups-fitp fn-nntp-nexts-boundedp fn-node-prepare
                                   fn-replay-advance-txid fn-sf-prepare-record fn-cpe-projection-step
                                   fn-sn-statep fn-node-statep fn-sn-record-bindsp))
           :use ((:instance fn-onb-inflight-fitp-of-prepare)))))

(defthm fn-onb-store-boundp-of-io
  (implies (and (fn-onb-store-boundp s)
                (or (fn-sn-statep s) (not (equal operation :record-directory))))
           (fn-onb-store-boundp (fn-sn-io s operation result)))
  :hints (("Goal" :in-theory (e/d (fn-sn-io fn-onb-store-boundp)
                                  (fn-onb-node-boundp fn-sn-file-step fn-sn-statep))
           :use ((:instance fn-onb-inflight-fitp-of-io)))))

(defthm fn-onb-sn-node-of-finish
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sn-node (fn-sn-finish s))
                  (let ((record (fn-sn-completion-record s)))
                    (cond ((fn-store-retention-event-p record)
                           (fn-replay-apply-retention-event (fn-sn-node s) record))
                          ((or (fn-stxe-p record) (fn-stxk-p record) (fn-hstxa-p record)
                               (fn-cpe-eventp record) (fn-th-topic-eventp record))
                           (fn-replay-apply-record (fn-sn-node s) record))
                          (t (fn-node-complete (fn-sn-node s) (fn-record-txid record)
                                               (fn-record-generation record) :durable))))))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish)
                                  (fn-onb-node-boundp fn-node-complete fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-sf-core-completion fn-sf-emit-success
                                   fn-cpe-projection-step fn-th-prefix-step fn-sn-statep fn-node-statep
                                   fn-sn-completion-enabledp fn-sn-completion-record fn-snb-record-fitp
                                   fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp fn-stxe-p
                                   fn-stxk-p fn-hstxa-p)))))

(defthm fn-onb-enabled-is-completing
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-phase (fn-sn-files s)) :completing))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp)
                                  (fn-sn-statep fn-sn-completion-record fn-store-retention-event-p
                                   fn-replay-apply-retention-event fn-replay-apply-record fn-stxe-p
                                   fn-stxk-p fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp
                                   fn-sn-record-bindsp fn-cpe-projection-step fn-th-prefix-step)))))

(defthm fn-onb-held-record-is-no-event
  (implies (fn-held-p r)
           (and (not (fn-store-retention-event-p r)) (not (fn-stxe-p r)) (not (fn-stxk-p r))
                (not (fn-hstxa-p r)) (not (fn-cpe-eventp r)) (not (fn-th-topic-eventp r)))))

;; The finish: a held row completes its pending allocation (unconditional);
;; every other record fits, by the Store's in-flight fact.
(defthm fn-onb-store-boundp-of-finish
  (implies (fn-onb-store-boundp s)
           (fn-onb-store-boundp (fn-sn-finish s)))
  :hints (("Goal" :in-theory (e/d (fn-onb-store-boundp fn-onb-inflight-fitp)
                                  (fn-sn-finish fn-onb-node-boundp fn-node-complete fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-sn-statep fn-node-statep
                                   fn-sn-completion-enabledp fn-sn-completion-record fn-snb-record-fitp
                                   fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp fn-stxe-p
                                   fn-stxk-p fn-hstxa-p fn-held-p fn-sf-record-phasep fn-onb-inflight-fitp-of-finish))
           :cases ((fn-sn-completion-enabledp s))
           :use ((:instance fn-onb-inflight-fitp-of-finish)))
          ("Subgoal 2" :in-theory (enable fn-sn-finish))))

(defthm fn-onb-store-boundp-of-spc-prepare
  (implies (and (fn-onb-store-boundp s)
                (fn-snb-record-fitp (fn-sn-node s) record))
           (fn-onb-store-boundp (fn-spc-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-spc-prepare fn-onb-store-boundp fn-snb-record-fitp fn-snb-record-article)
                                  (fn-onb-node-boundp fn-sn-prepare-node fn-spc-stage-record
                                   fn-cpe-projection-step fn-sn-statep fn-node-statep fn-sn-record-bindsp
                                   fn-snb-groups-fitp))
           :use ((:instance fn-onb-inflight-fitp-of-spc-prepare)))))
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

;; ---------------------------------------------------------------------------
;; The identity prepare.  host/owner-host.lisp fn-owner-prepare-identity
;; calls fn-pout-prepare-identity, whose owner is fn-psrv-prepare-identity's
;; over the interned row: it stages only a composite fn-psrv-event-numberedp
;; admits, so the record in flight fits (fn-onb-inflight-fitp) through the io
;; steps to the finish.

(defthm fn-onb-inflight-fitp-of-ccar-prepare-identity
  (implies (and (fn-onb-inflight-fitp s)
                (fn-snb-record-fitp (fn-sn-node s) event))
           (fn-onb-inflight-fitp (fn-ccar-sn-prepare-identity s event)))
  :hints (("Goal" :in-theory (e/d (fn-ccar-sn-prepare-identity fn-onb-inflight-fitp fn-pcar-stage-record)
                                  (fn-sn-statep fn-sf-statep fn-snb-record-fitp fn-pcar-stage-record-is-stage-record
                                   fn-pcar-files-candidatep fn-ccar-cpe-projection-step
                                   fn-replay-apply-record fn-replay-identity-step fn-node-statep
                                   fn-sn-completion-record fn-stxe-p fn-stxk-p fn-hstxa-p fn-held-p
                                   fn-replay-composite-held fn-record-stamp fn-stxk-context-kind
                                   fn-sn-identity-context fn-record-record-vocabulary fn-record-shape-vocabulary)))))
(defthm fn-onb-store-boundp-of-ccar-prepare-identity
  (implies (and (fn-onb-store-boundp s)
                (fn-snb-record-fitp (fn-sn-node s) event))
           (fn-onb-store-boundp (fn-ccar-sn-prepare-identity s event)))
  :hints (("Goal" :in-theory (e/d (fn-onb-store-boundp fn-ccar-sn-prepare-identity)
                                  (fn-onb-node-boundp fn-sn-statep fn-snb-record-fitp fn-pcar-stage-record
                                   fn-ccar-cpe-projection-step fn-replay-apply-record fn-replay-identity-step
                                   fn-stxe-p fn-stxk-p fn-hstxa-p fn-replay-composite-held fn-record-stamp
                                   fn-stxk-context-kind fn-sn-identity-context))
           :use ((:instance fn-onb-inflight-fitp-of-ccar-prepare-identity)))))
(defthm fn-onb-boundp-of-psrv-prepare-identity
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-psrv-prepare-identity oc event))))
  :hints (("Goal" :in-theory (e/d (fn-psrv-prepare-identity fn-ccar-ocfg-prepare-identity fn-psrv-event-numberedp)
                                  (fn-onb-boundp fn-ccar-sn-prepare-identity fn-own-refresh fn-onb-store-boundp
                                   fn-psrv-event-servedp fn-snb-record-fitp))
           :use ((:instance fn-onb-boundp-of-refresh
                            (o (fn-own-make (fn-ccar-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) event)
                                            (fn-own-view (fn-ocfg-owner oc)) (fn-own-conns (fn-ocfg-owner oc))
                                            (fn-own-next-id (fn-ocfg-owner oc)) (fn-own-max-conns (fn-ocfg-owner oc))
                                            (fn-own-pending (fn-ocfg-owner oc)) (fn-own-ledger-field (fn-ocfg-owner oc))
                                            (fn-own-clock (fn-ocfg-owner oc)) (fn-own-facts (fn-ocfg-owner oc))
                                            (fn-own-config (fn-ocfg-owner oc)) (fn-own-queue (fn-ocfg-owner oc))
                                            (fn-own-inflight (fn-ocfg-owner oc)) (fn-own-feeds (fn-ocfg-owner oc))
                                            (fn-own-node-secret (fn-ocfg-owner oc)) (fn-own-refused (fn-ocfg-owner oc)))))
                 (:instance fn-onb-boundp (o (fn-own-make (fn-ccar-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) event)
                                            (fn-own-view (fn-ocfg-owner oc)) (fn-own-conns (fn-ocfg-owner oc))
                                            (fn-own-next-id (fn-ocfg-owner oc)) (fn-own-max-conns (fn-ocfg-owner oc))
                                            (fn-own-pending (fn-ocfg-owner oc)) (fn-own-ledger-field (fn-ocfg-owner oc))
                                            (fn-own-clock (fn-ocfg-owner oc)) (fn-own-facts (fn-ocfg-owner oc))
                                            (fn-own-config (fn-ocfg-owner oc)) (fn-own-queue (fn-ocfg-owner oc))
                                            (fn-own-inflight (fn-ocfg-owner oc)) (fn-own-feeds (fn-ocfg-owner oc))
                                            (fn-own-node-secret (fn-ocfg-owner oc)) (fn-own-refused (fn-ocfg-owner oc)))))
                 (:instance fn-onb-boundp (o (fn-ocfg-owner oc)))))))

(defthm fn-onb-boundp-at-owner-prepare-identity
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (mv-nth 1 (fn-pout-prepare-identity oc w h)))))
  :hints (("Goal" :in-theory (e/d (fn-pout-prepare-identity fn-oiis-prepare-identity)
                                  (fn-psrv-prepare-identity fn-onb-boundp fn-pout-stagedp
                                   fn-pout-identity-refusal-kind fn-oiis-prepare-identity-unfolds fn-oii-identity-row)))))

;; ---------------------------------------------------------------------------
;; THE OPEN (coordinator decision, 2026-09-29).  A reopened Store's numbers
;; come from disk, so the open establishes the bound once: host/owner-host.lisp
;; fn-owner-install-extended calls fn-onb-open-okp on the recovered owner
;; before it installs it, and refuses the Store BY NAME
;; (:article-numbers-damaged; a damaged store, never absence) when a
;; watermark is past RFC 3977 section 6's bound or the owner opens inside a
;; transaction.  The test reads the node's per-group watermarks, the pending
;; allocation's groups and the view's watermarks: O(groups), never the
;; history.  A store 6.6.0 wrote never fails it (every admitted article is
;; fn-psrv-event-numberedp).  Once open, the bound is carried
;; (fn-onb-boundp's preservation above), never revalidated.

(defun fn-onb-open-okp (o)
  (declare (xargs :guard t))
  (let* ((s (fn-own-store o))
         (phase (fn-sf-phase (fn-sn-files s)))
         (a (fn-node-acceptance (fn-sn-node s))))
    (and (not (fn-sf-record-phasep phase))
         (not (equal phase :completing))
         (fn-nntp-nexts-boundedp (fn-state-nexts a))
         (or (not (fn-state-pending a))
             (fn-snb-groups-fitp (fn-pending-groups (fn-state-pending a))
                                 (fn-state-nexts a)))
         (fn-nntp-nexts-boundedp
          (fn-state-nexts (fn-own-view-archive (fn-own-view o)))))))
(defthm fn-onb-boundp-when-open-okp
  (implies (fn-onb-open-okp o)
           (fn-onb-boundp o))
  :hints (("Goal" :in-theory (e/d (fn-onb-boundp fn-onb-store-boundp fn-onb-node-boundp fn-onb-inflight-fitp)
                                  (fn-nntp-nexts-boundedp fn-snb-groups-fitp fn-sf-record-phasep)))))
(defthm fn-onb-open-okp-is-boundp-outside-a-transaction
  (implies (and (not (fn-sf-record-phasep (fn-sf-phase (fn-sn-files (fn-own-store o)))))
                (not (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :completing)))
           (equal (fn-onb-open-okp o) (fn-onb-boundp o)))
  :hints (("Goal" :in-theory (e/d (fn-onb-boundp fn-onb-store-boundp fn-onb-node-boundp fn-onb-inflight-fitp)
                                  (fn-nntp-nexts-boundedp fn-snb-groups-fitp fn-sf-record-phasep)))))
