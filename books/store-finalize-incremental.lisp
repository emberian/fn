; store-finalize-incremental.lisp -- the Store's open/swap finalize over a
; suffix, from the carried verdict (row A9; lane incremental-finalize, PRF-946).
;
; The served open (host/store-node-host.lisp fn-store-sn-recover-rows and
; fn-store-sn-recover-from-checkpoint) extends a capture E over the records
; after it and finalizes the extension: fn-rii-sco-extend-open
; (books/replay-identity-index.lisp section 7b).  Its finalize walks the WHOLE
; record list (fn-rii-observed-historyp: fn-sf-record-listp over P ++ Q) and
; the identity fold's whole verdict and snapshot lists, at every open and at
; every online-reclaim swap (online-reclaim-3's delta).  This book carries
; E's verdict instead: when E finalized :ok at some frontier f0, the finalize
; of E ++ Q at f1 is decided from Q alone -- Q's records walked once from the
; sequence |P| and the transaction bound P left (fn-sf-next-lower), the
; frontier compared once with that bound -- and the opened Store's recognizer
; is what its construction does not establish by theorem: the configuration
; it serves and three naturals.
;
; KEYSTONE fn-sfi-extend-open-is-rii-extend-open: for every base E that
; finalized :ok at any frontier f0, every configuration list, every suffix Q
; and every frontier f1, (fn-sfi-extend-open E configs Q f1 next)
; with next = (fn-sf-next-lower (fn-sco-records E) 0) IS
; (fn-rii-sco-extend-open E configs Q f1): the extension and its classified
; open, which by fn-rii-sco-extend-open-is-extend-then-open and
; fn-rii-classified-open-is-classified-open is (fn-sco-extend E configs Q)
; and (fn-sopc-classified-open ...) of it.  The corollary in the shape
; online-reclaim asked for (build/coordinator/lanedumps/online-reclaim-3.md):
; fn-sfi-extend-open-finalizes-the-extension, the open's second component
; is (fn-sco-finalize (fn-sco-extend E configs Q) configs f1).
;
; The two carried quantities are O(1) for both callers: the swap has the
; rebuild's count and last transaction id; the open has the checkpoint's
; count (fn-sco-freeze-of-capture-carries-the-count) and its last record.
; Cost of fn-sfi-extend-open beyond the folds' resume: O(|Q|) record checks
; + O(configuration) + O(1), plus the opened Store's two row folds over every
; retained record: fn-sn-update-replayed's verdicts (fn-sn-row-verdicts) and
; the statement index of the frozen row deltas (fn-sn-index-of-rows), which
; the configured twin installs too.  (Until 2026-10-01 this open installed
; the EMPTY index, correct only while a reopened Store had no keyring; the
; reopen now derives its keyring from the retained snapshots, and the empty
; index diverged from the twin.)  Neither fold parses a payload.  Not changed here
; (named in the lane's record): the resume's check of the paused node and
; the tries it rebuilds (fn-rii-sco-cpr-resume), inherited from section 7 of
; the twin book; and the one node check the empty-suffix path keeps
; (fn-sco-cpr-finish), because a guard does not cross a host call.

(in-package "ACL2")

(include-book "replay-identity-index")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Section 1.  The record-list walk over the suffix only.
;
; fn-sf-record-listp threads the sequence and the next admissible transaction
; id through the list, so the walk over P ++ Q splits at |P| with the bound P
; leaves (fn-sfi-sf-record-listp-append), and a prefix valid at f0 is valid at
; f1 exactly when that bound is at most f1 (fn-sfi-sf-record-listp-refrontier:
; the transaction ids ascend, so the last one decides).

(defun fn-sfi-historyp-extend (count next frontier suffix)
  (declare (xargs :guard (and (natp count) (natp next))))
  (and (fn-record-uint32p frontier)
       (<= next frontier)
       (fn-rii-sf-record-listp suffix count next frontier)))

(defthm fn-sfi-historyp-extend-frontier
  (implies (fn-sfi-historyp-extend count next frontier suffix)
           (fn-record-uint32p frontier))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sfi-historyp-extend))))

(defthm fn-sfi-next-lower-lower-bound
  (implies (fn-sf-record-listp p sequence lower frontier)
           (<= lower (fn-sf-next-lower p lower)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-sf-record-listp p sequence lower frontier))))

(defthm fn-sfi-sf-record-listp-append
  (implies (and (true-listp p) (natp sequence) (natp lower))
           (equal (fn-sf-record-listp (append p q) sequence lower frontier)
                  (and (fn-sf-record-listp p sequence lower frontier)
                       (fn-sf-record-listp q (+ sequence (len p))
                                           (fn-sf-next-lower p lower)
                                           frontier))))
  :hints (("Goal" :induct (fn-sf-record-listp p sequence lower frontier))))

(defthm fn-sfi-sf-record-listp-refrontier
  (implies (and (fn-sf-record-listp p sequence lower f0)
                (natp lower) (natp f1) (<= lower f1))
           (equal (fn-sf-record-listp p sequence lower f1)
                  (<= (fn-sf-next-lower p lower) f1)))
  :hints (("Goal" :induct (fn-sf-record-listp p sequence lower f0))))

; The suffix walk decides the whole history's recognizer at the new frontier
; from the prefix's verdict at the old one.
(defthm fn-sfi-historyp-extend-is-observed-historyp
  (implies (and (fn-sn-observed-historyp f0 p) (true-listp p))
           (equal (fn-sfi-historyp-extend (len p) (fn-sf-next-lower p 0) f1 q)
                  (fn-sn-observed-historyp f1 (append p q))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sfi-sf-record-listp-append
                            (sequence 0) (lower 0) (frontier f1))
                 (:instance fn-sfi-sf-record-listp-refrontier
                            (sequence 0) (lower 0)))
           :in-theory (e/d (fn-sn-observed-historyp fn-sfi-historyp-extend
                            fn-record-uint32p
                            fn-rii-sf-record-listp-is-sf-record-listp)
                           (fn-sf-record-listp fn-sf-next-lower
                            fn-sfi-sf-record-listp-append
                            fn-sfi-sf-record-listp-refrontier)))))

; -----------------------------------------------------------------------------
; Section 2.  What the opened Store's construction establishes by theorem.
;
; fn-rii-sn-statep-carried (the twin book's recognizer without the node and
; the history walk) still walks the identity fold's verdict pairs and keyring
; snapshots, both as long as the history's identity records.  Every verdict
; pair is well-formed because every verdict event is (Lemma V); the snapshot
; list is kept by every identity step, so the fold over Q keeps it (Lemma S);
; the recovering file state is a carried file state by construction; the
; keyring is the empty one.  What remains is fn-sfi-sn-statep-carried.

(defthm fn-sfi-verdict-pairs-are-verdicts
  (fn-sn-verdict-listp (fn-replay-verdict-pairs xs))
  :hints (("Goal" :in-theory (enable fn-replay-verdict-pairs fn-sn-verdict-listp
                                     fn-stx-make-verdict fn-stx-verdict-token
                                     fn-stx-verdict-generation fn-stxe-tokenp
                                     fn-record-msgidp fn-record-uint32p))))

(defthm fn-sfi-snapshots-of-context
  (equal (fn-stxk-context-snapshots
          (fn-stxk-context kind next snapshots verdicts generation tail))
         snapshots)
  :hints (("Goal" :in-theory (enable fn-stxk-context fn-stxk-context-snapshots))))

(defthm fn-sfi-fault-keeps-snapshots
  (equal (fn-stxk-context-snapshots (fn-stxk-fault ctx reason))
         (fn-stxk-context-snapshots ctx))
  :hints (("Goal" :in-theory (enable fn-stxk-fault fn-stxk-context
                                     fn-stxk-context-snapshots))))

(defthm fn-sfi-apply-verdict-keeps-snapshots
  (equal (fn-stxk-context-snapshots (fn-stxk-apply-verdict ctx e))
         (fn-stxk-context-snapshots ctx))
  :hints (("Goal" :in-theory (e/d (fn-stxk-apply-verdict fn-stxk-fault
                                   fn-stxk-context fn-stxk-context-snapshots)
                                  (fn-stxe-p fn-stxk-find)))))

(defthm fn-sfi-identity-step-keeps-snapshots
  (implies (fn-sn-keyring-snapshot-listp (fn-stxk-context-snapshots ctx))
           (fn-sn-keyring-snapshot-listp
            (fn-stxk-context-snapshots (fn-replay-identity-step ctx event))))
  :hints (("Goal" :in-theory (e/d (fn-replay-identity-step fn-stxk-apply-snapshot
                                   fn-replay-apply-carried-verdict
                                   fn-replay-apply-revoked-verdict
                                   fn-replay-identity-advance)
                                  (fn-stxk-p fn-stxe-p fn-stxa-p
                                   fn-stxk-apply-verdict fn-stxk-fault
                                   fn-stxk-context fn-stxk-context-snapshots)))))

(defthm fn-sfi-identity-loop-keeps-snapshots
  (implies (fn-sn-keyring-snapshot-listp (fn-stxk-context-snapshots ctx))
           (fn-sn-keyring-snapshot-listp
            (fn-stxk-context-snapshots (fn-replay-identity-loop records ctx))))
  :hints (("Goal" :induct (fn-replay-identity-loop records ctx)
           :in-theory (e/d (fn-replay-identity-loop)
                           (fn-replay-identity-step fn-store-event-p fn-stxk-fault
                            fn-stxk-context fn-stxk-context-snapshots)))))

(defthm fn-sfi-recovering-files-carried
  (implies (fn-record-uint32p frontier)
           (fn-rii-sf-statep-carried
            (fn-sf-make :recovering frontier nil events nil nil nil 0)))
  :hints (("Goal" :in-theory (enable fn-rii-sf-statep-carried fn-sf-phase-shapep
                                     fn-sf-success-listp))))

; The fields of the opened Store the finalize builds, read off its
; construction (the twin book's fn-rii-opened-node-and-files gives the node
; and the files).
(defthm fn-sfi-opened-fields
  (let ((opened (fn-sn-with-event-index
                 (fn-sn-with-topic
                  (fn-sn-with-consumer
                   (fn-cpo-install
                    (fn-sn-update-replayed
                     (fn-sn-observed-seed groups capacity frontier events)
                     files advanced index identity)
                    (fn-cnode-make advanced config) configs)
                   consumer)
                  topic)
                 event-index)))
    (and (fn-sn-shapep opened)
         (equal (fn-sn-files opened) files)
         (equal (fn-sn-keyring opened)
                (fn-ssk-keyring-of-snapshots (fn-stxk-context-snapshots identity)))
         (equal (fn-sn-verdicts opened) (fn-sn-row-verdicts (fn-sf-records files)))
         (equal (fn-sn-keyring-snapshots opened)
                (fn-stxk-context-snapshots identity))
         (equal (fn-sn-identity-next opened) (fn-stxk-context-next identity))
         (equal (fn-sn-keyring-generation opened)
                (fn-ssk-generation (fn-stxk-context-snapshots identity)))))
  :hints (("Goal" :in-theory (e/d (fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-cpo-install
                                   fn-sn-update-replayed fn-sn-observed-seed
                                   fn-sn-make fn-sn-make-v6 fn-sn-with-configuration
                                   fn-sn-shapep fn-sn-files fn-sn-keyring
                                   fn-sn-verdicts fn-sn-keyring-snapshots
                                   fn-sn-identity-next fn-sn-keyring-generation
                                   fn-sn-groups fn-sn-capacity fn-sn-node fn-sn-index
                                   fn-sn-config-history fn-sn-consumer fn-sn-topic
                                   fn-sn-event-index)
                                  (fn-replay-verdict-pairs fn-sf-make
                                   fn-ssk-keyring-of-snapshots fn-ssk-generation
                                   fn-sn-row-verdicts fn-sf-records
                                   fn-node-initial-state fn-cnode-make fn-cnode-node
                                   fn-cnode-config fn-cnode-domain-of
                                   fn-cfg-capacity fn-cfg-value)))))

(defun fn-sfi-sn-statep-carried (s)
  (declare (xargs :guard t))
  (and (fn-string-listp (fn-sn-groups s))
       (fn-no-duplicatesp (fn-sn-groups s))
       (natp (fn-sn-capacity s))
       (natp (fn-sn-keyring-generation s))
       (natp (fn-sn-identity-next s))))

(defthm fn-sfi-sn-statep-carried-is-rii-sn-statep-carried
  (implies (and (fn-sn-shapep s)
                (fn-rii-sf-statep-carried (fn-sn-files s))
                (fn-prin-keyringp (fn-sn-keyring s))
                (fn-sn-verdict-listp (fn-sn-verdicts s))
                (fn-sn-keyring-snapshot-listp (fn-sn-keyring-snapshots s)))
           (equal (fn-sfi-sn-statep-carried s) (fn-rii-sn-statep-carried s)))
  :hints (("Goal" :in-theory (e/d (fn-sfi-sn-statep-carried
                                   fn-rii-sn-statep-carried)
                                  (fn-rii-sf-statep-carried fn-prin-keyringp
                                   fn-sn-verdict-listp fn-sn-keyring-snapshot-listp
                                   fn-sn-shapep fn-string-listp fn-no-duplicatesp)))))

; -----------------------------------------------------------------------------
; Section 3.  The finalize from the carried verdict, and the fused entry.

; fn-rii-sco-finalize-configured with the suffix walk in place of the history
; walk, fn-sfi-sn-statep-carried in place of fn-rii-sn-statep-carried and the
; empty index in place of the parse of every payload.
; COUNT and NEXT are the prefix's length and the transaction bound it left.
(defun fn-sfi-finalize-carried (replayed c configs count next suffix frontier)
  (declare (xargs :guard (and (natp count) (natp next)
                              (or (not (equal (fn-replay-result-kind replayed) :ok))
                                  (fn-cnode-statep (fn-replay-result-node replayed))))
                  :verify-guards nil))
  (let ((events (fn-sco-records c)))
    (if (or (null configs)
            (not (fn-sfi-historyp-extend count next frontier suffix)))
        (fn-sn-open-error :history)
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-sn-open-error :replay)
        (let* ((cn (fn-replay-result-node replayed))
               (node (fn-cnode-node cn)))
          (if (not (fn-rii-advance-idlep node frontier))
              (fn-sn-open-error :frontier)
            (let* ((advanced (fn-replay-advance-txid node frontier))
                   (config (fn-cnode-config cn))
                   (identity (fn-sco-identity c))
                   (consumer (fn-sco-consumer c))
                   (topic (fn-sco-topic c))
                   (files (fn-sf-make :recovering frontier nil events
                                      nil nil nil 0))
                   (seed (fn-sn-observed-seed
                          (fn-cnode-domain-of config)
                          (fn-cfg-capacity (fn-cfg-value config))
                          frontier events))
                   (opened (fn-sn-with-event-index
                            (fn-sn-with-topic
                             (fn-sn-with-consumer
                              (fn-cpo-install
                               (fn-sn-update-replayed
                                seed files advanced
                                ; the frozen row deltas, as the configured
                                ; finalize installs them: no payload is
                                ; reinterned under the reopened keyring
                                (fn-sn-index-of-rows events)
                                identity)
                               (fn-cnode-make advanced config) configs)
                              (fn-cp-nth 1 consumer))
                             topic)
                            nil)))
              (if (and (equal (fn-stxk-context-kind identity) :ok)
                       (consp consumer) (eq (car consumer) :ok)
                       (eq (fn-th-at 0 topic) :ok)
                       (fn-sfi-sn-statep-carried opened))
                  (fn-sn-open-ok opened)
                (fn-sn-open-error :identity)))))))))

(defthm fn-sfi-cnode-statep-has-node-statep
  (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cnode-statep))))

(verify-guards fn-sfi-finalize-carried
  :hints (("Goal" :in-theory (e/d (fn-sfi-cnode-statep-has-node-statep)
                                  (fn-cnode-statep fn-node-statep fn-cpr-replay
                                   fn-cpr-loop fn-sco-cpr-finish
                                   fn-sco-cpr-prefix)))))

; Under the two carried facts the finalize is the twin book's.
; The opened Store's verdicts are fn-sn-row-verdicts of its records: each row
; contributes a well-formed verdict pair or nothing.
(local (defthm fn-sfi-held-msgid-stringp
  (implies (fn-held-p row) (stringp (fn-record-msgid row)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-p-fields fn-record-msgidp)))))
(local (defthm fn-sfi-held-verdict-valid
  (implies (fn-held-p row)
           (and (member-equal (fn-stx-verdict-token (fn-hc-verdict (fn-held-context row)))
                              *fn-stx-verdicts*)
                (natp (fn-stx-verdict-generation (fn-hc-verdict (fn-held-context row))))))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-p-fields fn-hc-p fn-hc-p-fields
                                     fn-hc-verdictp fn-stx-verdict-token
                                     fn-stx-verdict-generation)))))
(local (defthm fn-sfi-replay-verdict-pair-valid
  (implies (fn-stxe-p e)
           (let ((p (fn-replay-verdict-pair e)))
             (implies p (and (consp p) (stringp (car p))
                             (member-equal (fn-stx-verdict-token (cdr p)) *fn-stx-verdicts*)
                             (natp (fn-stx-verdict-generation (cdr p)))))))
  :hints (("Goal" :in-theory (enable fn-replay-verdict-pair fn-stx-make-verdict
                                     fn-stx-verdict-token fn-stx-verdict-generation
                                     fn-stxe-tokenp fn-record-msgidp)))))
(local (defthm fn-sfi-row-verdict-pair-valid
  (let ((p (fn-sn-row-verdict-pair row)))
    (implies p (and (consp p) (stringp (car p))
                    (member-equal (fn-stx-verdict-token (cdr p)) *fn-stx-verdicts*)
                    (natp (fn-stx-verdict-generation (cdr p))))))
  :hints (("Goal" :in-theory (e/d (fn-sn-row-verdict-pair)
                                  (fn-held-p fn-hstxa-p fn-stxe-p fn-stmt-okp fn-stmt-value
                                   fn-stxe-decode-exact fn-replay-verdict-pair fn-record-msgid
                                   fn-hc-verdict fn-held-context fn-stx-verdict-token
                                   fn-stx-verdict-generation))
           :use ((:instance fn-sfi-replay-verdict-pair-valid
                            (e (fn-stmt-value (fn-stxe-decode-exact
                                               (fn-stxa-verdict-event (fn-hstxa-stxa row)))))))))))
(local (defthm fn-sfi-row-verdicts-fold-valid
  (implies (fn-sn-verdict-listp verdicts)
           (fn-sn-verdict-listp (fn-sn-row-verdicts-fold rows verdicts)))
  :hints (("Goal" :induct (fn-sn-row-verdicts-fold rows verdicts)
                  :in-theory (e/d (fn-sn-row-verdicts-fold fn-sn-verdict-listp)
                                  (fn-sn-row-verdict-pair fn-stx-verdict-token
                                   fn-stx-verdict-generation))))))
(local (defthm fn-sfi-row-verdicts-valid
  (fn-sn-verdict-listp (fn-sn-row-verdicts rows))
  :hints (("Goal" :in-theory (enable fn-sn-row-verdicts fn-sn-verdict-listp)))))

(defthm fn-sfi-finalize-carried-is-finalize-configured
  (implies (and (equal (fn-sfi-historyp-extend count next frontier suffix)
                       (fn-rii-observed-historyp frontier (fn-sco-records c)))
                (fn-sn-keyring-snapshot-listp
                 (fn-stxk-context-snapshots (fn-sco-identity c))))
           (equal (fn-sfi-finalize-carried replayed c configs count next
                                           suffix frontier)
                  (fn-rii-sco-finalize-configured replayed c configs frontier)))
  :hints (("Goal" :in-theory (e/d (fn-sfi-finalize-carried
                                   fn-rii-sco-finalize-configured
                                   fn-stx-index-of-store-without-a-keyring)
                                  (fn-sfi-historyp-extend fn-rii-observed-historyp
                                   fn-rii-observed-historyp-is-observed-historyp
                                   fn-sfi-sn-statep-carried fn-rii-sn-statep-carried
                                   fn-rii-sf-statep-carried fn-sn-with-event-index
                                   fn-sn-with-topic fn-sn-with-consumer fn-cpo-install
                                   fn-sn-update-replayed fn-sn-observed-seed
                                   fn-stx-index-of-store fn-replay-advance-txid
                                   fn-rii-advance-idlep fn-sf-make
                                   fn-replay-verdict-pairs fn-sn-shapep
                                   fn-prin-keyringp fn-sn-verdict-listp
                                   fn-sn-keyring-snapshot-listp fn-cnode-statep
                                   fn-stx-store fn-cnode-domain-of fn-cfg-capacity
                                   fn-cfg-value fn-cp-nth fn-th-at)))))

; What a base's :ok verdict gives: its history at that frontier and the
; snapshot list its identity fold left.
(defthm fn-sfi-carried-verdict-facts
  (implies (equal (fn-sn-open-kind (fn-sco-finalize e configs f0)) :ok)
           (and (fn-sn-observed-historyp f0 (fn-sco-records e))
                (fn-sn-keyring-snapshot-listp
                 (fn-stxk-context-snapshots (fn-sco-identity e)))))
  :hints (("Goal" :in-theory (e/d (fn-sco-finalize fn-sn-open-kind fn-sn-open-ok
                                   fn-sn-open-error fn-sn-statep)
                                  (fn-sn-observed-historyp fn-sco-cpr-finish
                                   fn-cnode-statep fn-replay-advance-okp
                                   fn-replay-advance-txid fn-sn-with-event-index
                                   fn-sn-with-topic fn-sn-with-consumer fn-cpo-install
                                   fn-sn-update-replayed fn-sn-observed-seed
                                   fn-stx-index-empty fn-sf-make fn-sf-statep
                                   fn-node-statep fn-prin-keyringp fn-sn-verdict-listp
                                   fn-sn-keyring-snapshot-listp fn-sn-shapep
                                   fn-string-listp fn-no-duplicatesp
                                   fn-replay-verdict-pairs fn-cnode-domain-of
                                   fn-cfg-capacity fn-cfg-value fn-cp-nth fn-th-at)))))

; The fused entry: fn-rii-sco-extend-open with the count read once from the
; extension and the finalize taken from the carried verdict.  NEXT is
; (fn-sf-next-lower (fn-sco-records c) 0), the prefix's transaction bound.
; A paused fold after a non-empty suffix has a configured node
; (fn-rii-sco-cpr-resume-paused-node-is-configured), so its drain skips the
; node check; the empty suffix drains through fn-sco-cpr-finish, whose one
; node check a guard cannot carry across the host call.
(defun fn-sfi-extend-open (c configs suffix frontier next)
  (declare (xargs :guard (natp next) :verify-guards nil))
  (let* ((records (true-list-fix (fn-sco-records c)))
         (count (len records))
         (e (fn-sco-make (append records suffix)
                         (fn-rii-sco-cpr-resume (fn-sco-cpr c) configs suffix)
                         (fn-replay-identity-loop suffix (fn-sco-identity c))
                         (fn-sco-consumer-resume (fn-sco-consumer c) suffix count)
                         (fn-th-prefix-loop (fn-sco-topic c) suffix)
                         (fn-cei-build-aux suffix count (fn-sco-event-index c))))
         (refusal (fn-sopc-open-refusal e))
         (r (fn-sco-cpr e)))
    (list e
          (cond (refusal refusal)
                ((fn-sco-pausedp r)
                 (let ((replayed (if (consp suffix)
                                     (fn-rii-sco-cpr-finish-configured r configs)
                                   (fn-sco-cpr-finish r configs))))
                   (list replayed
                         (fn-sfi-finalize-carried replayed e configs count next
                                                  suffix frontier))))
                (t (fn-rii-sco-store-open e configs frontier))))))

(verify-guards fn-sfi-extend-open
  :hints (("Goal" :in-theory (e/d (fn-sfi-cnode-statep-has-node-statep
                                   fn-rii-sco-cpr-finish-configured-is-finish)
                                  (fn-rii-sco-cpr-resume fn-sco-cpr-resume
                                   fn-sco-pausedp fn-cnode-statep fn-node-statep
                                   fn-cpr-loop fn-sopc-open-refusal
                                   fn-rii-sco-store-open fn-sfi-finalize-carried
                                   fn-sco-cpr-finish fn-rii-sco-cpr-finish-configured
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux))
           :use ((:instance fn-rii-sco-cpr-resume-paused-node-is-configured
                            (r (fn-sco-cpr c)))
                 (:instance fn-rii-sco-cpr-finish-ok-is-configured
                            (r (fn-sco-cpr-resume (fn-sco-cpr c) configs suffix)))))))

(local
 (defthm fn-sfi-true-list-fix-of-true-list
   (implies (true-listp x) (equal (true-list-fix x) x))))

; KEYSTONE (PRF-946).  f0 is free: any frontier at which the base finalized.
; No hypothesis on the suffix: an improper one is refused alike by both.
(defthm fn-sfi-extend-open-is-rii-extend-open
  (implies (and (equal (fn-sn-open-kind (fn-sco-finalize c configs f0)) :ok)
                (equal next (fn-sf-next-lower (fn-sco-records c) 0)))
           (equal (fn-sfi-extend-open c configs suffix frontier next)
                  (fn-rii-sco-extend-open c configs suffix frontier)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sfi-carried-verdict-facts (e c))
                 (:instance fn-sfi-historyp-extend-is-observed-historyp
                            (p (fn-sco-records c)) (f1 frontier) (q suffix))
                 (:instance fn-sfi-identity-loop-keeps-snapshots
                            (records suffix) (ctx (fn-sco-identity c))))
           :in-theory (e/d (fn-sfi-extend-open fn-rii-sco-extend-open
                            fn-rii-sco-extend fn-rii-sco-store-open-resumed
                            fn-rii-sco-store-open fn-sco-make fn-sco-records
                            fn-sco-cpr fn-sco-identity fn-sco-consumer fn-sco-topic
                            fn-sco-event-index fn-sco-at fn-sn-observed-historyp
                            fn-rii-observed-historyp-is-observed-historyp)
                           (fn-sfi-historyp-extend fn-rii-observed-historyp
                            fn-sfi-carried-verdict-facts
                            fn-sfi-historyp-extend-is-observed-historyp
                            fn-sfi-identity-loop-keeps-snapshots
                            fn-sfi-finalize-carried fn-rii-sco-finalize-configured
                            fn-rii-sco-finalize-from fn-rii-sco-cpr-resume
                            fn-replay-identity-loop fn-sco-consumer-resume
                            fn-th-prefix-loop fn-cei-build-aux fn-sopc-open-refusal
                            fn-sco-pausedp fn-rii-sco-cpr-finish-configured
                            fn-sco-cpr-finish fn-cnode-statep fn-sf-record-listp
                            fn-sf-next-lower fn-sco-finalize fn-sn-open-kind)))))

; The statement online-reclaim asked for: the open's second component is the
; finalize of the extension (the classified open reaches the store open
; whenever the pre-C1 refusal is absent).
(defthm fn-sfi-extend-open-finalizes-the-extension
  (implies (and (equal (fn-sn-open-kind (fn-sco-finalize c configs f0)) :ok)
                (equal next (fn-sf-next-lower (fn-sco-records c) 0))
                (not (fn-sopc-open-refusal (fn-sco-extend c configs suffix))))
           (equal (cadr (cadr (fn-sfi-extend-open c configs suffix frontier next)))
                  (fn-sco-finalize (fn-sco-extend c configs suffix)
                                   configs frontier)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sfi-extend-open-is-rii-extend-open)
                 (:instance fn-rii-sco-extend-open-is-extend-then-open)
                 (:instance fn-rii-classified-open-is-classified-open
                            (e (fn-sco-extend c configs suffix))))
           :in-theory (e/d (fn-sopc-classified-open fn-sco-store-open
                            fn-rii-sco-extend-is-sco-extend)
                           (fn-sfi-extend-open fn-rii-sco-extend-open
                            fn-rii-classified-open
                            fn-sfi-extend-open-is-rii-extend-open
                            fn-rii-sco-extend-open-is-extend-then-open
                            fn-rii-classified-open-is-classified-open
                            fn-sco-finalize fn-sco-extend fn-sopc-open-refusal
                            fn-sco-cpr-finish fn-sco-finalize-from
                            fn-sco-finalize-from-unfolds fn-sco-cpr
                            fn-sn-open-kind)))))

(in-theory (disable fn-sfi-historyp-extend fn-sfi-sn-statep-carried
                    fn-sfi-finalize-carried fn-sfi-extend-open))

; -----------------------------------------------------------------------------
; Section 4.  The carried resume (PRF-968): the paused fold with its tries.
;
; fn-rii-sco-cpr-resume (books/replay-identity-index.lisp) checks the paused
; node (fn-cnode-statep) and rebuilds its tries (fn-rii-ix-of) at every
; extension: two whole-node passes before the first suffix record, under the
; swap's mutex.  Both are facts the previous extension established and its
; pause dropped.  A carried pause keeps them: the paused fold with the tries
; beside it, under fn-sfi-cpr-carriedp (the paused node configured, the
; tries in fn-rii-okp with it), established once (fn-sfi-carry: the open's
; one node pass) and re-established by every extension
; (fn-sfi-extend-open-carried-keeps-carried).  The Message-ID trie carried
; is the trie a rebuild would make (fn-sfi-carried-msgid-trie-is-the-rebuilt-
; trie); the id trie is related to the rebuilt one by fn-rii-known-okp, a
; defun-sk, not equal to it.
;
; The invariant is the entries' guard: verified, and not executable (the
; defun-sk), exactly as the twin fold's own guard fn-rii-okp is.  So it is
; an obligation the caller keeps, as PRF-946's NEXT and verdict are: the
; pair (E, IX) comes only from fn-sfi-carry (the open's one node pass) or
; the previous fn-sfi-extend-open-carried, and the host, in :program mode,
; calls the entries raw, as the served image does.  An abstract stobj whose
; recognizer is the invariant would make ACL2 hold it instead; ACL2 refuses
; one here (stobj-attachment-restrictions: fn-cnode-statep reaches
; fn-digest, attached in books/crypto-attach.lisp), so that route needs an
; attachment-free node recognizer first.  A test drives the entries through
; a :program wrapper, the served path: there a wrong trie changes the
; outcome, while in the logic the twin's inner mbe :logic sides answer from
; the node -- the invariant is what makes the :exec path the :logic path,
; and it is carried into the keystones from the twin's own
; fn-rii-sco-cpr-prefix-is-sco-cpr-prefix, not removed here.
;
; What the extension still copies is the record list itself, `append' and
; `len' over (fn-sco-records c): O(|P|) list work, no node work.  The D27
; representation of the records (rows in the arena, the count in the
; checkpoint header) removes it; the fold does not.

(defun fn-sfi-cpr-carriedp (r ix)
  (declare (xargs :guard t))
  (and (fn-sco-pausedp r)
       (fn-cnode-statep (fn-sco-at 1 r))
       (fn-rii-okp ix (fn-cnode-node (fn-sco-at 1 r)))))

; fn-rii-sco-cpr-prefix keeping the tries: (RESULT . IX), RESULT the fold's
; and IX the tries at its pause (at a fault, the tries where it stopped).
(defun fn-sfi-cpr-prefix-carried (cn configs events config-sequence event-sequence ix)
  (declare (xargs :guard (and (fn-cnode-statep cn)
                              (fn-rii-okp ix (fn-cnode-node cn)))
                  :verify-guards nil
                  :measure (+ (len configs) (len events))))
  (if (not (consp events))
      (cons (fn-sco-paused cn config-sequence event-sequence) ix)
    (let ((position (+ (nfix config-sequence) (nfix event-sequence))))
      (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
          (cons (fn-replay-fault cn position :invalid-node) ix)
        (if (fn-cpr-config-firstp configs events)
            (let* ((record (car configs))
                   (txid (fn-cfg-record-txid record))
                   (node (fn-cnode-node cn)))
              (cond ((not (fn-cfg-recordp record))
                     (cons (fn-replay-fault cn position :invalid-config-record) ix))
                    ((not (equal (fn-cfg-record-sequence record) config-sequence))
                     (cons (fn-replay-fault cn position :config-sequence) ix))
                    ((not (fn-replay-advance-okp node txid))
                     (cons (fn-replay-fault cn position :config-txid) ix))
                    (t (let ((at (fn-cnode-make
                                  (fn-replay-advance-txid node txid)
                                  (fn-cnode-config cn))))
                         (if (mbe :logic (not (fn-cnode-statep at)) :exec nil)
                             (cons (fn-replay-fault cn position :invalid-node) ix)
                           (if (not (mbe :logic (fn-cnode-record-acceptablep
                                              at record (fn-cnode-line-ceiling))
                                         :exec (fn-cnode-carried-acceptablep
                                                at record (fn-cnode-line-ceiling))))
                               (cons (fn-replay-fault cn position :config-refusal) ix)
                             (let ((next (fn-cnode-apply-config
                                          at record (fn-cnode-line-ceiling))))
                               (fn-sfi-cpr-prefix-carried
                                next (cdr configs) events
                                (+ 1 (nfix config-sequence)) event-sequence
                                (fn-rii-ix-next ix node (fn-cnode-node next)
                                                nil)))))))))
          (let ((event (car events)))
            (cond ((not (fn-store-event-p event))
                   (cons (fn-replay-fault cn position :invalid-event) ix))
                  ((not (equal (fn-store-event-sequence event) event-sequence))
                   (cons (fn-replay-fault cn position :event-sequence) ix))
                  (t (let ((next (fn-rii-cpr-apply-event cn event ix)))
                       (if (mbe :logic (not (fn-cnode-statep next))
                                :exec (not (consp next)))
                           (cons (fn-replay-fault cn position :event-refusal) ix)
                         (fn-sfi-cpr-prefix-carried
                          next configs (cdr events)
                          config-sequence (+ 1 (nfix event-sequence))
                          (fn-rii-ix-next ix (fn-cnode-node cn)
                                          (fn-cnode-node next) event))))))))))))

; The fold's result is the twin fold's, with no hypothesis.
(defthm fn-sfi-cpr-prefix-carried-car
  (equal (car (fn-sfi-cpr-prefix-carried cn configs events cs es ix))
         (fn-rii-sco-cpr-prefix cn configs events cs es ix))
  :hints (("Goal" :induct (fn-sfi-cpr-prefix-carried cn configs events cs es ix)
           :in-theory (e/d (fn-rii-sco-cpr-prefix)
                           (fn-cnode-statep fn-cpr-config-firstp
                            fn-rii-cpr-apply-event fn-cpr-apply-event
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cnode-carried-acceptablep fn-cfg-recordp
                            fn-store-event-p fn-replay-advance-okp
                            fn-replay-advance-txid fn-rii-ix-next
                            fn-replay-fault fn-sco-paused)))))

; One step keeps the relation (fn-rii-ix-next-keeps-okp at each step's shape).
(local
 (defthm fn-sfi-not-release-of-nil
   (not (fn-rii-release-event-p nil))
   :hints (("Goal" :in-theory (enable fn-rii-release-event-p)))))

(local
 (defthm fn-sfi-event-step-keeps-okp
   (implies (and (fn-cnode-statep cn)
                 (fn-rii-okp ix (fn-cnode-node cn))
                 (consp (fn-cpr-apply-event cn event)))
            (fn-rii-okp (fn-rii-ix-next ix (fn-cnode-node cn)
                                        (fn-cnode-node (fn-cpr-apply-event cn event))
                                        event)
                        (fn-cnode-node (fn-cpr-apply-event cn event))))
   :hints (("Goal" :in-theory (e/d (fn-cpr-apply-event)
                                   (fn-cnode-statep fn-node-statep fn-store-event-p
                                    fn-cpr-event-servedp fn-replay-apply-record
                                    fn-rii-ix-next fn-rii-okp))))))

; PRESERVATION: from a configured node under the relation, the pause the
; fold reaches is configured and its tries are under the relation.
(defthm fn-sfi-cpr-prefix-carried-keeps-carried
  (implies (and (fn-cnode-statep cn)
                (fn-rii-okp ix (fn-cnode-node cn))
                (fn-sco-pausedp
                 (car (fn-sfi-cpr-prefix-carried cn configs events cs es ix))))
           (fn-sfi-cpr-carriedp
            (car (fn-sfi-cpr-prefix-carried cn configs events cs es ix))
            (cdr (fn-sfi-cpr-prefix-carried cn configs events cs es ix))))
  :hints (("Goal" :induct (fn-sfi-cpr-prefix-carried cn configs events cs es ix)
           :in-theory (e/d (fn-sfi-cpr-carriedp fn-sco-at fn-sco-paused
                            fn-replay-fault fn-cnode-apply-config-preserves-state)
                           (fn-cnode-statep fn-node-statep fn-cpr-config-firstp
                            fn-rii-cpr-apply-event fn-cpr-apply-event
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cnode-carried-acceptablep fn-cfg-recordp
                            fn-store-event-p fn-replay-apply-record
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-rii-ix-next fn-rii-okp)))))

(local
 (defthm fn-sfi-config-firstp-has-config
   (implies (fn-cpr-config-firstp configs events) (consp configs))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cpr-config-firstp)))))

(verify-guards fn-sfi-cpr-prefix-carried
  :hints (("Goal"
           :use ((:instance fn-cpr-apply-event-statep-iff-consp
                            (event (car events)))
                 (:instance fn-cnode-advanced-node-is-configured
                            (txid (fn-cfg-record-txid (car configs))))
                 (:instance fn-cnode-record-acceptablep-is-the-carried-check
                            (cn (fn-cnode-make
                                 (fn-replay-advance-txid
                                  (fn-cnode-node cn)
                                  (fn-cfg-record-txid (car configs)))
                                 (fn-cnode-config cn)))
                            (record (car configs))
                            (ceiling (fn-cnode-line-ceiling))))
           :in-theory (e/d (fn-cnode-apply-config-preserves-state)
                           (fn-cnode-statep fn-node-statep fn-cpr-config-firstp
                            fn-cpr-apply-event fn-cnode-apply-config
                            fn-cnode-record-acceptablep fn-cfg-recordp
                            fn-store-event-p fn-replay-apply-record
                            fn-rii-ix-next fn-rii-okp)))))

; The resume from a carried pause: no node check, no trie rebuild.  The
; empty suffix re-makes the pause as fn-sco-cpr-resume does.
(defun fn-sfi-cpr-resume-carried (r configs events ix)
  (declare (xargs :guard (fn-sfi-cpr-carriedp r ix) :verify-guards nil))
  (let ((cs (fn-sco-at 2 r)) (cn (fn-sco-at 1 r)) (es (fn-sco-at 3 r)))
    (if (not (consp events))
        (cons (fn-sco-paused cn cs es) ix)
      (fn-sfi-cpr-prefix-carried cn (fn-sco-nthcdr (nfix cs) configs) events
                                 cs es ix))))

(verify-guards fn-sfi-cpr-resume-carried
  :hints (("Goal" :in-theory (e/d (fn-sfi-cpr-carriedp)
                                  (fn-cnode-statep fn-rii-okp fn-sco-at
                                   fn-sco-nthcdr)))))

; KEYSTONE (PRF-968).  Under the carried invariant the resume is the
; checkpoint's resume, for every configuration list and suffix.
(defthm fn-sfi-cpr-resume-carried-is-sco-cpr-resume
  (implies (fn-sfi-cpr-carriedp r ix)
           (equal (car (fn-sfi-cpr-resume-carried r configs events ix))
                  (fn-sco-cpr-resume r configs events)))
  :hints (("Goal" :in-theory (e/d (fn-sfi-cpr-resume-carried fn-sfi-cpr-carriedp
                                   fn-sco-cpr-resume)
                                  (fn-cnode-statep fn-rii-okp fn-sco-at
                                   fn-sco-nthcdr fn-sfi-cpr-prefix-carried
                                   fn-rii-sco-cpr-prefix))
           :expand ((:free (cf cs es)
                     (fn-sco-cpr-prefix (fn-sco-at 1 r) cf events cs es))))))

; The invariant survives the resume: the next extension skips both passes too.
(defthm fn-sfi-cpr-resume-carried-keeps-carried
  (implies (and (fn-sfi-cpr-carriedp r ix)
                (fn-sco-pausedp (car (fn-sfi-cpr-resume-carried r configs events ix))))
           (fn-sfi-cpr-carriedp
            (car (fn-sfi-cpr-resume-carried r configs events ix))
            (cdr (fn-sfi-cpr-resume-carried r configs events ix))))
  :hints (("Goal" :in-theory (e/d (fn-sfi-cpr-resume-carried fn-sfi-cpr-carriedp
                                   fn-sco-at fn-sco-paused)
                                  (fn-cnode-statep fn-rii-okp fn-sco-nthcdr
                                   fn-sfi-cpr-prefix-carried))
           :use ((:instance fn-sfi-cpr-prefix-carried-keeps-carried
                            (cn (fn-sco-at 1 r))
                            (configs (fn-sco-nthcdr (nfix (fn-sco-at 2 r)) configs))
                            (cs (fn-sco-at 2 r)) (es (fn-sco-at 3 r)))))))

; The Message-ID trie carried is the one a rebuild makes.
(defthm fn-sfi-carried-msgid-trie-is-the-rebuilt-trie
  (implies (fn-rii-okp ix node)
           (equal (car ix) (car (fn-rii-ix-of node))))
  :hints (("Goal" :in-theory (e/d (fn-rii-okp fn-rii-ix-of)
                                  (fn-rii-known-okp fn-midx-build fn-mxc-build
                                   fn-rii-kbuild)))))

; The one node pass, at the open: the tries built from the decoded
; checkpoint's paused node, or NIL where there is no configured pause.
(defun fn-sfi-carry (c)
  (declare (xargs :guard t))
  (let ((r (fn-sco-cpr c)))
    (if (and (fn-sco-pausedp r) (fn-cnode-statep (fn-sco-at 1 r)))
        (fn-rii-ix-of (fn-cnode-node (fn-sco-at 1 r)))
      nil)))

(defthm fn-sfi-carry-is-carried
  (implies (fn-sfi-carry c)
           (fn-sfi-cpr-carriedp (fn-sco-cpr c) (fn-sfi-carry c)))
  :hints (("Goal" :in-theory (e/d (fn-sfi-carry fn-sfi-cpr-carriedp)
                                  (fn-cnode-statep fn-rii-ix-of fn-sco-at fn-sco-cpr
                                   fn-rii-okp)))))

; -----------------------------------------------------------------------------
; The bound, as a step count.  The steps twin walks the fold's path and counts
; its iterations; the bound names the suffix and the configuration list only.
; What an iteration costs is the trie step (fn-rii-ix-next: the changed
; articles and one id) and the node step -- never the node's size: the test
; book checks that the executed path (the :exec side of every mbe) of the
; carried resume reaches neither fn-cnode-statep nor a trie builder.

(defun fn-sfi-cpr-prefix-carried-steps (cn configs events cs es ix)
  (declare (xargs :guard t :verify-guards nil
                  :measure (+ (len configs) (len events))))
  (if (not (consp events))
      0
    (if (not (fn-cnode-statep cn))
        1
      (if (fn-cpr-config-firstp configs events)
          (let* ((record (car configs))
                 (txid (fn-cfg-record-txid record))
                 (node (fn-cnode-node cn)))
            (if (or (not (fn-cfg-recordp record))
                    (not (equal (fn-cfg-record-sequence record) cs))
                    (not (fn-replay-advance-okp node txid)))
                1
              (let ((at (fn-cnode-make (fn-replay-advance-txid node txid)
                                       (fn-cnode-config cn))))
                (if (or (not (fn-cnode-statep at))
                        (not (fn-cnode-record-acceptablep at record (fn-cnode-line-ceiling))))
                    1
                  (let ((next (fn-cnode-apply-config at record (fn-cnode-line-ceiling))))
                    (+ 1 (fn-sfi-cpr-prefix-carried-steps
                          next (cdr configs) events (+ 1 (nfix cs)) es
                          (fn-rii-ix-next ix node (fn-cnode-node next) nil))))))))
        (let ((event (car events)))
          (if (or (not (fn-store-event-p event))
                  (not (equal (fn-store-event-sequence event) es)))
              1
            (let ((next (fn-rii-cpr-apply-event cn event ix)))
              (if (not (fn-cnode-statep next))
                  1
                (+ 1 (fn-sfi-cpr-prefix-carried-steps
                      next configs (cdr events) cs (+ 1 (nfix es))
                      (fn-rii-ix-next ix (fn-cnode-node cn) (fn-cnode-node next)
                                      event)))))))))))

(defthm fn-sfi-cpr-prefix-carried-steps-bounded
  (<= (fn-sfi-cpr-prefix-carried-steps cn configs events cs es ix)
      (+ (len configs) (len events)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-sfi-cpr-prefix-carried-steps cn configs events cs es ix)
           :in-theory (disable fn-cnode-statep fn-cpr-config-firstp
                               fn-rii-cpr-apply-event fn-cnode-apply-config
                               fn-cnode-record-acceptablep fn-cfg-recordp
                               fn-store-event-p fn-replay-advance-okp
                               fn-replay-advance-txid fn-rii-ix-next))))

(defun fn-sfi-cpr-resume-carried-steps (r configs events ix)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (consp events))
      0
    (fn-sfi-cpr-prefix-carried-steps
     (fn-sco-at 1 r) (fn-sco-nthcdr (nfix (fn-sco-at 2 r)) configs) events
     (fn-sco-at 2 r) (fn-sco-at 3 r) ix)))

(local
 (defthm fn-sfi-len-nthcdr-bound
   (<= (len (nthcdr n x)) (len x))
   :rule-classes :linear))

; THE BOUND (PRF-968): the carried resume's steps are bounded by the suffix
; and the configuration list; no term of the bound names the node.
(defthm fn-sfi-cpr-resume-carried-steps-bounded
  (<= (fn-sfi-cpr-resume-carried-steps r configs events ix)
      (+ (len configs) (len events)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-sfi-cpr-resume-carried-steps fn-sco-nthcdr)
                                  (fn-sfi-cpr-prefix-carried-steps fn-sco-at))
           :use ((:instance fn-sfi-cpr-prefix-carried-steps-bounded
                            (cn (fn-sco-at 1 r))
                            (configs (nthcdr (nfix (fn-sco-at 2 r)) configs))
                            (cs (fn-sco-at 2 r)) (es (fn-sco-at 3 r)))))))

; -----------------------------------------------------------------------------
; The fused entry from a carried pause: fn-sfi-extend-open with the resume
; above, COUNT the prefix's length carried beside NEXT, and both drains
; through the configured drain (the carried node is configured with or
; without a suffix).  (E' IX' RESULT): the extension, its carried tries, and
; fn-rii-sco-extend-open's result.

(defun fn-sfi-extend-open-carried (c ix configs suffix frontier count next)
  (declare (xargs :guard (and (natp count) (natp next)
                              (fn-sfi-cpr-carriedp (fn-sco-cpr c) ix))
                  :verify-guards nil))
  (let* ((records (true-list-fix (fn-sco-records c)))
         (resumed (fn-sfi-cpr-resume-carried (fn-sco-cpr c) configs suffix ix))
         (r (car resumed))
         (e (fn-sco-make (append records suffix)
                         r
                         (fn-replay-identity-loop suffix (fn-sco-identity c))
                         (fn-sco-consumer-resume (fn-sco-consumer c) suffix count)
                         (fn-th-prefix-loop (fn-sco-topic c) suffix)
                         (fn-cei-build-aux suffix count (fn-sco-event-index c))))
         (refusal (fn-sopc-open-refusal e)))
    (list e
          (cdr resumed)
          (cond (refusal refusal)
                ((fn-sco-pausedp r)
                 (let ((replayed (fn-rii-sco-cpr-finish-configured r configs)))
                   (list replayed
                         (fn-sfi-finalize-carried replayed e configs count next
                                                  suffix frontier))))
                (t (fn-rii-sco-store-open e configs frontier))))))

(verify-guards fn-sfi-extend-open-carried
  :hints (("Goal" :in-theory (e/d (fn-sfi-cnode-statep-has-node-statep
                                   fn-rii-sco-cpr-finish-configured-is-finish
                                   fn-sfi-cpr-carriedp)
                                  (fn-sfi-cpr-resume-carried fn-sco-cpr-resume
                                   fn-sco-pausedp fn-cnode-statep fn-node-statep
                                   fn-cpr-loop fn-sopc-open-refusal
                                   fn-rii-sco-store-open fn-sfi-finalize-carried
                                   fn-sco-cpr-finish fn-rii-sco-cpr-finish-configured
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux))
           :use ((:instance fn-sfi-cpr-resume-carried-keeps-carried
                            (r (fn-sco-cpr c)) (events suffix))
                 (:instance fn-sfi-cpr-resume-carried-is-sco-cpr-resume
                            (r (fn-sco-cpr c)) (events suffix))
                 (:instance fn-rii-sco-cpr-finish-ok-is-configured
                            (r (fn-sco-cpr-resume (fn-sco-cpr c) configs suffix)))))))

(local
 (defthm fn-sfi-len-of-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

; The carried entry is the carried-verdict entry with the resume swapped.
(defthm fn-sfi-extend-open-carried-is-extend-open
  (implies (and (fn-sfi-cpr-carriedp (fn-sco-cpr c) ix)
                (equal count (len (fn-sco-records c))))
           (equal (fn-sfi-extend-open-carried c ix configs suffix frontier count next)
                  (list (car (fn-sfi-extend-open c configs suffix frontier next))
                        (cdr (fn-sfi-cpr-resume-carried (fn-sco-cpr c) configs suffix ix))
                        (cadr (fn-sfi-extend-open c configs suffix frontier next)))))
  :hints (("Goal" :in-theory (e/d (fn-sfi-extend-open-carried fn-sfi-extend-open
                                   fn-rii-sco-cpr-finish-configured-is-finish
                                   fn-sco-make fn-sco-cpr fn-sco-at)
                                  (fn-sfi-cpr-resume-carried fn-rii-sco-cpr-resume
                                   fn-sco-cpr-resume fn-sfi-cpr-carriedp fn-sco-pausedp
                                   fn-cnode-statep fn-sopc-open-refusal
                                   fn-rii-sco-store-open fn-sfi-finalize-carried
                                   fn-rii-sco-store-open-is-sco-store-open
                                   fn-sco-store-open fn-sco-finalize-from
                                   fn-sco-finalize-from-unfolds
                                   fn-sco-cpr-finish fn-rii-sco-cpr-finish-configured
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux
                                   fn-sco-records fn-sco-identity
                                   fn-sco-consumer fn-sco-topic fn-sco-event-index)))))

; KEYSTONE (PRF-968).  Under the carried invariant, the carried verdict and
; the carried count and bound, the entry is the extension, its tries and the
; classified open of the extension -- the host's fn-rii-sco-extend-open, with
; neither whole-node pass.  f0 is free.
(defthm fn-sfi-extend-open-carried-is-rii-extend-open
  (implies (and (fn-sfi-cpr-carriedp (fn-sco-cpr c) ix)
                (equal (fn-sn-open-kind (fn-sco-finalize c configs f0)) :ok)
                (equal count (len (fn-sco-records c)))
                (equal next (fn-sf-next-lower (fn-sco-records c) 0)))
           (equal (fn-sfi-extend-open-carried c ix configs suffix frontier count next)
                  (list (fn-sco-extend c configs suffix)
                        (cdr (fn-sfi-cpr-resume-carried (fn-sco-cpr c) configs suffix ix))
                        (fn-rii-classified-open (fn-sco-extend c configs suffix)
                                                configs frontier))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sfi-extend-open-carried-is-extend-open)
                 (:instance fn-sfi-extend-open-is-rii-extend-open)
                 (:instance fn-rii-sco-extend-open-is-extend-then-open))
           :in-theory '(fn-rii-sco-extend-is-sco-extend car-cons cdr-cons))))

; The statement for the swap (online-reclaim): the third component's second
; element is the finalize of the extension whenever the pre-C1 refusal is
; absent.
(defthm fn-sfi-extend-open-carried-finalizes-the-extension
  (implies (and (fn-sfi-cpr-carriedp (fn-sco-cpr c) ix)
                (equal (fn-sn-open-kind (fn-sco-finalize c configs f0)) :ok)
                (equal count (len (fn-sco-records c)))
                (equal next (fn-sf-next-lower (fn-sco-records c) 0))
                (not (fn-sopc-open-refusal (fn-sco-extend c configs suffix))))
           (equal (cadr (caddr (fn-sfi-extend-open-carried c ix configs suffix
                                                           frontier count next)))
                  (fn-sco-finalize (fn-sco-extend c configs suffix)
                                   configs frontier)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sfi-extend-open-carried-is-rii-extend-open)
                 (:instance fn-rii-classified-open-is-classified-open
                            (e (fn-sco-extend c configs suffix))))
           :in-theory (e/d (fn-sopc-classified-open fn-sco-store-open)
                           (fn-sfi-extend-open-carried fn-rii-classified-open
                            fn-sfi-cpr-resume-carried fn-sfi-cpr-carriedp
                            fn-sfi-extend-open-carried-is-rii-extend-open
                            fn-rii-classified-open-is-classified-open
                            fn-sco-finalize fn-sco-extend fn-sopc-open-refusal
                            fn-sco-cpr-finish fn-sco-finalize-from
                            fn-sco-finalize-from-unfolds fn-sco-cpr
                            fn-sco-records fn-sf-next-lower fn-sn-open-kind)))))

; What the next round carries, each in O(|Q|): the invariant over the
; extension's pause and tries, the count, and the bound.  The verdict is the
; result itself (fn-sfi-extend-open-carried-finalizes-the-extension at :ok).
(defthm fn-sfi-extend-open-carried-keeps-carried
  (implies (and (fn-sfi-cpr-carriedp (fn-sco-cpr c) ix)
                (fn-sco-pausedp
                 (fn-sco-cpr (car (fn-sfi-extend-open-carried c ix configs suffix
                                                              frontier count next)))))
           (fn-sfi-cpr-carriedp
            (fn-sco-cpr (car (fn-sfi-extend-open-carried c ix configs suffix
                                                         frontier count next)))
            (cadr (fn-sfi-extend-open-carried c ix configs suffix frontier count next))))
  :hints (("Goal" :in-theory (e/d (fn-sfi-extend-open-carried fn-sco-make fn-sco-cpr
                                   fn-sco-at)
                                  (fn-sfi-cpr-resume-carried fn-sfi-cpr-carriedp
                                   fn-sco-pausedp fn-sopc-open-refusal
                                   fn-rii-sco-store-open fn-sfi-finalize-carried
                                   fn-rii-sco-cpr-finish-configured
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux fn-sco-records
                                   fn-sco-identity fn-sco-consumer fn-sco-topic
                                   fn-sco-event-index))
           :use ((:instance fn-sfi-cpr-resume-carried-keeps-carried
                            (r (fn-sco-cpr c)) (events suffix))))))

(local
 (defthm fn-sfi-next-lower-of-append
   (equal (fn-sf-next-lower (append p q) lower)
          (fn-sf-next-lower q (fn-sf-next-lower p lower)))))

(local
 (defthm fn-sfi-next-lower-of-true-list-fix
   (equal (fn-sf-next-lower (true-list-fix p) lower)
          (fn-sf-next-lower p lower))))

(local
 (defthm fn-sfi-len-of-append
   (equal (len (append p q)) (+ (len p) (len q)))))

(defthm fn-sfi-extend-open-carried-count-and-bound
  (implies (equal count (len (fn-sco-records c)))
           (let ((e (car (fn-sfi-extend-open-carried c ix configs suffix frontier
                                                     count next))))
             (and (equal (len (fn-sco-records e)) (+ count (len suffix)))
                  (equal (fn-sf-next-lower (fn-sco-records e) 0)
                         (fn-sf-next-lower suffix
                                           (fn-sf-next-lower (fn-sco-records c) 0))))))
  :hints (("Goal" :in-theory (e/d (fn-sfi-extend-open-carried fn-sco-make fn-sco-records
                                   fn-sco-at)
                                  (fn-sfi-cpr-resume-carried fn-sopc-open-refusal
                                   fn-rii-sco-store-open fn-sfi-finalize-carried
                                   fn-rii-sco-cpr-finish-configured fn-sf-next-lower
                                   fn-replay-identity-loop fn-sco-consumer-resume
                                   fn-th-prefix-loop fn-cei-build-aux fn-sco-cpr
                                   fn-sco-identity fn-sco-consumer fn-sco-topic
                                   fn-sco-event-index)))))

(in-theory (disable fn-sfi-cpr-carriedp fn-sfi-cpr-prefix-carried
                    fn-sfi-cpr-resume-carried fn-sfi-carry
                    fn-sfi-cpr-prefix-carried-steps fn-sfi-cpr-resume-carried-steps
                    fn-sfi-extend-open-carried))

; -----------------------------------------------------------------------------
; The bound for any decoded record list: fn-sf-next-lower's guard asks
; fn-sf-record-valuesp; the open's caller computes NEXT from bytes.
(defun fn-sfi-next-lower-total (records lower)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-sfi-next-lower-total (cdr records)
                               (+ 1 (fix (fn-store-event-txid (car records)))))
    lower))

(defthm fn-sfi-next-lower-total-is-next-lower
  (equal (fn-sfi-next-lower-total records lower)
         (fn-sf-next-lower records lower)))

(in-theory (disable fn-sfi-next-lower-total))
