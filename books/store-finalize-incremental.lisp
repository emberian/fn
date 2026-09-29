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
; + O(configuration) + O(1).  Also dropped: the twin's fn-stx-index-of-store
; over the opened store, which parses every retained article's payload
; against the empty keyring for the index that
; fn-stx-index-of-store-without-a-keyring proves empty.  Not changed here
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
         (equal (fn-sn-keyring opened) nil)
         (equal (fn-sn-verdicts opened)
                (fn-replay-verdict-pairs (fn-stxk-context-verdicts identity)))
         (equal (fn-sn-keyring-snapshots opened)
                (fn-stxk-context-snapshots identity))
         (equal (fn-sn-identity-next opened) (fn-stxk-context-next identity))
         (equal (fn-sn-keyring-generation opened) 0)))
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
                                ; the open has no keyring: its index IS the
                                ; empty one (fn-stx-index-of-store-without-a-
                                ; keyring), so no article payload is parsed
                                (fn-stx-index-empty)
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
