; fn: a signed POST's (identity event's) retention admission from the carried
; obligation-id trie (Q5b's residual, served-costs-3).
;
; The profile of the signed POST at N = 100,000 stored articles (sb-sprof on
; the prof image, planning/evidence/served-costs-3-2026-09-29/) put 35
; percent of the owner's samples under fn-retain-known-id-scanp, all of it
; from fn-replay-apply-record -> fn-node-prepare: an identity event (a
; composite signed article) is staged and gated by applying its record to the
; store's node three times per POST (fn-ccar-sn-prepare-identity, and the
; completion's fn-ccar-completion-core-enabledp and fn-ccar-sn-finish-enabled),
; and each application's fn-node-prepare scans every pin and release twice
; (fn-retain-admissiblep, then fn-retain-admit's own test).  The unsigned POST
; already answers that admission from the carried trie
; (books/post-retain-carried.lisp fn-prc-node-prepare).  This book is the
; same substitution for the record application: fn-irc-node-prepare is
; fn-node-prepare with the admission through fn-prc-admissiblep and the admit
; built directly, and fn-irc-apply-record is fn-replay-apply-record with it.
; Each is proved EQUAL to its reference under (fn-prc-carryp carry), the
; carry's only premise, which names no owner state.

(in-package "ACL2")
(include-book "post-retain-carried")
(include-book "owner-refresh-indexed")
(include-book "owner-prepare-outcome")

(defun fn-irc-node-prepare (s generation msgid payload groups
                              obligation-id subject evidence charge stamp carry)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-node-statep s)) :exec nil)
      s
    (let ((retention (fn-node-retention s)))
      (if (not (fn-prc-admissiblep retention obligation-id subject :archive
                                   evidence charge carry))
          s
        (let ((next-acceptance
               (fn-accept-prepare (fn-node-acceptance s)
                                  generation msgid payload groups stamp)))
          (if (equal next-acceptance (fn-node-acceptance s))
              s
            (fn-node-make-state
             next-acceptance
             retention
             (fn-node-make-stage
              msgid generation obligation-id subject evidence charge
              (fn-retain-make-state
               (fn-retain-capacity retention)
               (+ (fn-retain-reserved retention) charge)
               (cons (fn-retain-make-obligation obligation-id subject :archive
                                                evidence charge)
                     (fn-retain-pins retention))
               (fn-retain-releases retention)))
             (fn-node-bindings s))))))))

(encapsulate ()
  (local (in-theory (enable (tau-system)))) ; tau-cost: as fn-prc-node-prepare's
  (verify-guards fn-irc-node-prepare
    :hints (("Goal" :in-theory (enable fn-node-statep)))))

(defthm fn-irc-node-prepare-is-node-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-node-prepare s generation msgid payload groups
                                       obligation-id subject evidence charge
                                       stamp carry)
                  (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge stamp)))
  :hints (("Goal" :in-theory (e/d (fn-irc-node-prepare fn-node-prepare
                                   fn-retain-admit)
                                  (fn-node-statep fn-retain-admissiblep
                                   fn-accept-prepare fn-retain-make-state
                                   fn-retain-make-obligation)))))

;; The retention record's application (books/replay.lisp
;; fn-replay-apply-retention-event) with the undertaking's admission through
;; the carry: a retention completion (and the retention branch of every
;; record application below) no longer scans the ledger's ids.
(defun fn-irc-apply-retention-event (node event carry)
  (declare (xargs :guard (and (fn-node-statep node)
                              (fn-store-retention-event-p event)
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (let* ((advanced (fn-replay-advance-txid node (fn-store-event-txid event)))
         (retention (fn-node-retention advanced))
         (id (fn-store-event-obligation-id event))
         (subject (fn-store-event-subject event))
         (evidence (fn-store-event-evidence event)))
    (if (or (not (mbt (fn-node-statep advanced)))
            (not (equal (fn-state-next-txid (fn-node-acceptance advanced))
                        (fn-store-event-txid event)))
            (not (null (fn-node-stage advanced)))
            (member-equal id (fn-node-binding-ids (fn-node-bindings advanced))))
        nil
      (if (equal (fn-store-event-kind event) :undertake)
          (if (not (fn-prc-admissiblep retention id subject :forward evidence
                                       (fn-store-event-charge event) carry))
              nil
            (fn-replay-complete-retention
             advanced (fn-retain-admit retention id subject :forward evidence
                                       (fn-store-event-charge event)) event))
        (let ((pin (fn-retain-find-id id (fn-retain-pins retention))))
          (if (not (fn-retain-matching-releasep pin id subject :forward evidence))
              nil
            (fn-replay-complete-retention
             advanced (fn-retain-release retention id subject :forward evidence)
             event)))))))

(defthm fn-irc-apply-retention-event-is-reference
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-apply-retention-event node event carry)
                  (fn-replay-apply-retention-event node event)))
  :hints (("Goal" :in-theory (e/d (fn-irc-apply-retention-event
                                   fn-replay-apply-retention-event
                                   fn-prc-admissiblep-is-admissiblep)
                                  (fn-retain-admissiblep fn-retain-admit
                                   fn-replay-advance-txid fn-node-statep
                                   fn-replay-complete-retention fn-retain-release
                                   fn-retain-find-id fn-retain-matching-releasep)))))

(verify-guards fn-irc-apply-retention-event
  :hints (("Goal" :use ((:guard-theorem fn-replay-apply-retention-event))
                  :in-theory (e/d (fn-prc-admissiblep-is-admissiblep)
                                  (fn-retain-admissiblep fn-retain-admit
                                   fn-replay-advance-txid fn-node-statep
                                   fn-prc-carryp fn-prc-admissiblep
                                   fn-replay-complete-retention fn-retain-release
                                   fn-retain-find-id fn-retain-matching-releasep)))))

(in-theory (disable fn-irc-apply-retention-event))

(defun fn-irc-apply-record (node record carry)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record)
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (fn-store-retention-event-p record)
      (fn-irc-apply-retention-event node record carry)
    (if (or (fn-stxe-p record) (fn-stxk-p record) (fn-cpe-eventp record)
            (fn-th-topic-eventp record))
        (if (and (or (fn-cpe-eventp record) (fn-th-topic-eventp record))
                 (not (null (fn-node-stage node))))
            nil
          (fn-replay-apply-identity-neutral node record))
      ; Unreachable-in-composition: journal replay enters with no pending
      ; transaction.  A standalone article step refuses a staged node, lest a
      ; record with matching coordinates complete that different article.
      (if (not (null (fn-node-stage node)))
          nil
      (let* ((article (if (fn-hstxa-p record)
                          (fn-replay-composite-held record)
                        record))
             (advanced (fn-replay-advance-txid node (fn-store-event-txid record))))
      (if (not (equal (fn-state-next-txid (fn-node-acceptance advanced))
                      (fn-store-event-txid record)))
          nil
        (if (not (fn-held-p article)) nil
          (let ((prepared
               (fn-irc-node-prepare advanced
                                (fn-record-generation article)
                                (fn-record-msgid article)
                                (fn-record-payload article)
                                (fn-record-groups article)
                                (fn-record-obligation-id article)
                                (fn-record-content-subject article)
                                (fn-record-release-evidence article)
                                (fn-record-charge article)
                                (fn-record-stamp article)
                                carry)))
          (if (not (fn-node-pending-matchesp
                    prepared
                    (fn-record-txid article)
                    (fn-record-generation article)))
              nil
            (fn-node-complete prepared
                              (fn-record-txid article)
                              (fn-record-generation article)
                              :durable))))))))))

(defthm fn-irc-apply-record-is-replay-apply-record
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-apply-record node record carry)
                  (fn-replay-apply-record node record)))
  :hints (("Goal" :in-theory (e/d (fn-irc-apply-record fn-replay-apply-record
                                   fn-irc-apply-retention-event-is-reference)
                                  (fn-irc-node-prepare fn-node-prepare
                                   fn-irc-apply-retention-event
                                   fn-store-event-p fn-record-p fn-stxe-p
                                   fn-stxk-p fn-stxa-p fn-store-retention-event-p
                                   fn-cpe-eventp fn-th-topic-eventp
                                   fn-replay-apply-retention-event
                                   fn-replay-apply-identity-neutral
                                   fn-replay-advance-txid fn-node-complete
                                   fn-node-pending-matchesp fn-held-p)))))

(verify-guards fn-irc-apply-record
  :hints (("Goal" :in-theory (disable fn-store-event-p fn-record-p fn-stxe-p
                                      fn-stxk-p fn-stxa-p
                                      fn-store-retention-event-p fn-cpe-eventp
                                      fn-replay-composite-record))))

(in-theory (disable fn-irc-node-prepare fn-irc-apply-record))

; -----------------------------------------------------------------------------
; The Store's completion gate and finish with the record application through
; the carry (books/owner-commit-carried.lisp fn-ccar-completion-core-enabledp,
; fn-ccar-completion-enabledp, fn-ccar-sn-finish-enabled): a signed POST's
; composite, a keyring snapshot, a consumer or topic event completes through
; fn-irc-apply-record; each is its reference under fn-prc-carryp.

(defun fn-irc-completion-core-enabledp (s carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry))
                  :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (let ((record (fn-ccar-completion-record s)))
         (and record
              (cond ((fn-evc-retentionp record)
                     (consp (fn-irc-apply-retention-event (fn-sn-node s) record carry)))
                    ((or (fn-evc-stxep record) (fn-evc-stxkp record)
                         (fn-evc-stxap record))
                     (and (consp (fn-irc-apply-record (fn-sn-node s) record carry))
                          (equal (fn-stxk-context-kind
                                  (fn-replay-identity-step
                                   (fn-sn-identity-context s) record)) :ok)))
                    ((or (fn-evc-consumerp record) (fn-evc-topicp record))
                     (consp (fn-irc-apply-record (fn-sn-node s) record carry)))
                    (t (and (fn-ccar-sn-record-bindsp (fn-sn-node s) record)
                            (equal (fn-hc-generation (fn-held-context record))
                                   (fn-sn-keyring-generation s)))))
              (equal (fn-sf-completion (fn-sn-files s))
                     (cons (fn-evc-sequence record) (fn-evc-txid record)))))))

(defthm fn-irc-completion-core-enabledp-is-ccar
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-completion-core-enabledp s carry)
                  (fn-ccar-completion-core-enabledp s)))
  :hints (("Goal" :in-theory '(fn-irc-completion-core-enabledp
                               fn-ccar-completion-core-enabledp
                               fn-irc-apply-record-is-replay-apply-record
                               fn-irc-apply-retention-event-is-reference))))

(verify-guards fn-irc-completion-core-enabledp
  :hints (("Goal" :use ((:guard-theorem fn-ccar-completion-core-enabledp))
                  :in-theory (e/d (fn-sn-statep fn-evc-carried-definitions)
                                  (fn-ccar-completion-record-is-completion-record
                                   fn-ccar-completion-record-is-a-store-event
                                   fn-sf-statep fn-node-statep fn-prc-carryp
                                   fn-record-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p fn-store-event-p
                                   fn-cpe-eventp fn-th-topic-eventp)))))

(defun fn-irc-completion-enabledp (s carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry))
                  :verify-guards nil))
  (and (fn-irc-completion-core-enabledp s carry)
       (let ((record (fn-ccar-completion-record s)))
         (and (eq (car (fn-ccar-cpe-projection-step
                        (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok)
              (eq (fn-th-at 0 (fn-ccar-th-prefix-step (fn-sn-topic s) record)) :ok)))))

(defthm fn-irc-completion-enabledp-is-ccar
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-completion-enabledp s carry)
                  (fn-ccar-completion-enabledp s)))
  :hints (("Goal" :in-theory '(fn-irc-completion-enabledp
                               fn-ccar-completion-enabledp
                               fn-irc-completion-core-enabledp-is-ccar))))

(verify-guards fn-irc-completion-enabledp
  :hints (("Goal" :use ((:guard-theorem fn-ccar-completion-enabledp))
                  :in-theory (union-theories
                              '(fn-irc-completion-core-enabledp-is-ccar)
                              (theory 'ground-zero)))))

(defun fn-irc-sn-finish-enabled (s carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry)
                              (fn-ccar-completion-enabledp s))
                  :verify-guards nil))
  (let* ((record (fn-ccar-completion-record s))
         (retentionp (fn-evc-retentionp record))
         (consumerp (fn-evc-consumerp record))
         (topicp (fn-evc-topicp record))
         (identityp (or (fn-evc-stxep record) (fn-evc-stxkp record)
                        (fn-evc-stxap record)))
         (sequence (fn-evc-sequence record))
         (txid (fn-evc-txid record))
         (projection (fn-ccar-cpe-projection-step
                      (fn-sn-consumer s) record (fn-sn-identity-next s)))
         (topic-projection (fn-ccar-th-prefix-step (fn-sn-topic s) record))
         (node (cond (retentionp
                      (fn-irc-apply-retention-event (fn-sn-node s) record carry))
                     ((or identityp consumerp topicp)
                      (fn-irc-apply-record (fn-sn-node s) record carry))
                     (t
                      (fn-node-complete (fn-sn-node s) (fn-record-txid record)
                                        (fn-record-generation record) :durable))))
         (files (fn-sf-core-completion (fn-sn-files s) sequence txid)))
    (fn-sn-with-topic
     (fn-sn-with-consumer
      (if (or retentionp consumerp topicp)
          (fn-sn-advance-identity-next
           (fn-sn-update-indexed
            s (fn-sf-emit-success files sequence txid)
            node (fn-sn-index s)))
        (if identityp
            (fn-sn-finish-identity
             s (fn-sf-emit-success files sequence txid)
             record node)
          (fn-sn-advance-identity-next
           (fn-sn-update-accepted
            s (fn-sf-emit-success files sequence txid)
            node
            (fn-stx-index-add (fn-sn-index s) (fn-ccar-accepted-delta s))
            (fn-record-msgid record)
            (fn-hc-verdict (fn-held-context record))))))
      (fn-cp-nth 1 projection))
     topic-projection)))

(defthm fn-irc-sn-finish-enabled-is-ccar
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-sn-finish-enabled s carry)
                  (fn-ccar-sn-finish-enabled s)))
  :hints (("Goal" :in-theory '(fn-irc-sn-finish-enabled
                               fn-ccar-sn-finish-enabled
                               fn-irc-apply-record-is-replay-apply-record
                               fn-irc-apply-retention-event-is-reference))))

(verify-guards fn-irc-sn-finish-enabled
  :hints (("Goal" :use ((:guard-theorem fn-ccar-sn-finish-enabled))
                  :in-theory (e/d (fn-irc-apply-record-is-replay-apply-record)
                                  (fn-sn-statep fn-sf-statep fn-node-statep
                                   fn-prc-carryp fn-ccar-completion-enabledp
                                   fn-ccar-completion-record
                                   fn-node-pending-matchesp fn-sf-core-completion
                                   fn-store-event-p fn-record-p
                                   fn-sn-identity-context fn-replay-identity-step
                                   fn-replay-apply-retention-event fn-replay-apply-record
                                   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-record-record-vocabulary fn-record-shape-vocabulary)))))

(in-theory (disable fn-irc-completion-core-enabledp fn-irc-completion-enabledp
                    fn-irc-sn-finish-enabled))

; -----------------------------------------------------------------------------
; The completions the host calls (books/owner-refresh-indexed.lisp
; fn-rix-own-complete-enabled, fn-rix-own-complete, fn-rix-ocfg-complete),
; with the finish through the carry.  host/owner-host.lisp
; fn-owner-finish-synced calls fn-irc-rix-ocfg-complete.

(defun fn-irc-rix-own-complete-enabled (o fn-hist carry)
  (declare (xargs :stobjs fn-hist
                  :guard (and (fn-sn-statep (fn-own-store o)) (fn-prc-carryp carry)
                              (fn-ccar-completion-enabledp (fn-own-store o)))
                  :verify-guards nil))
  (let ((s (fn-own-store o)))
    (fn-own-refresh-ix
     (fn-own-make (fn-irc-sn-finish-enabled s carry) (fn-own-view o) (fn-own-conns o)
                  (fn-own-next-id o) (fn-own-max-conns o) nil
                  (fn-sl-snoc (fn-own-ledger-field o) (fn-sf-completion (fn-sn-files s)))
                  (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                  (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                  (fn-own-node-secret o) (fn-own-refused o)) fn-hist)))

(defthm fn-irc-rix-own-complete-enabled-is-rix
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-rix-own-complete-enabled o fn-hist carry)
                  (fn-rix-own-complete-enabled o fn-hist)))
  :hints (("Goal" :in-theory '(fn-irc-rix-own-complete-enabled
                               fn-rix-own-complete-enabled
                               fn-irc-sn-finish-enabled-is-ccar))))

(verify-guards fn-irc-rix-own-complete-enabled
  :hints (("Goal" :use ((:guard-theorem fn-rix-own-complete-enabled))
                  :in-theory (e/d (fn-irc-sn-finish-enabled-is-ccar)
                                  (fn-sn-statep fn-prc-carryp fn-own-refresh-ix
                                   fn-ccar-completion-enabledp fn-ccar-sn-finish-enabled)))))

(defun fn-irc-rix-own-complete (o fn-hist carry)
  (declare (xargs :stobjs fn-hist
                  :guard (and (fn-sn-statep (fn-own-store o)) (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (fn-irc-completion-enabledp (fn-own-store o) carry)
      (fn-irc-rix-own-complete-enabled o fn-hist carry)
    o))

(defthm fn-irc-rix-own-complete-is-rix
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-rix-own-complete o fn-hist carry)
                  (fn-rix-own-complete o fn-hist)))
  :hints (("Goal" :in-theory '(fn-irc-rix-own-complete fn-rix-own-complete
                               fn-irc-completion-enabledp-is-ccar
                               fn-irc-rix-own-complete-enabled-is-rix))))

(verify-guards fn-irc-rix-own-complete
  :hints (("Goal" :in-theory (e/d (fn-irc-completion-enabledp-is-ccar)
                                  (fn-sn-statep fn-prc-carryp
                                   fn-ccar-completion-enabledp)))))

(defun fn-irc-rix-ocfg-complete (oc fn-hist carry)
  (declare (xargs :stobjs fn-hist
                  :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))))
  (let ((record (fn-ocfg-staged oc)))
    (if record
        (fn-ocfg-make
         (fn-ocfg-owner oc)
         (fn-ocfg-published-config (fn-ocfg-config oc) record)
         (fn-ocfg-pins oc) nil)
      (fn-ocfg-make (fn-irc-rix-own-complete (fn-ocfg-owner oc) fn-hist carry)
                    (fn-ocfg-config oc) (fn-ocfg-pins oc) nil))))

(defthm fn-irc-rix-ocfg-complete-is-rix
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-rix-ocfg-complete oc fn-hist carry)
                  (fn-rix-ocfg-complete oc fn-hist)))
  :hints (("Goal" :in-theory '(fn-irc-rix-ocfg-complete fn-rix-ocfg-complete
                               fn-irc-rix-own-complete-is-rix))))

; KEYSTONE (host line): host/owner-host.lisp fn-owner-finish-synced calls the
; left-hand side with the carry refreshed to the Store node's ledger; it is
; the configured owner's (:complete) on every owner whose Store carries its
; event index (fn-rix-ocfg-complete-is-ccar-ocfg-complete,
; fn-ccar-ocfg-complete-is-ocfg-step-complete), for every carry the host
; holds (fn-prc-carryp-of-refresh).
(defthm fn-irc-rix-ocfg-complete-of-refresh-unfolds
  (implies (and (fn-prc-carryp carry)
                (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-irc-rix-ocfg-complete oc fn-hist (fn-prc-refresh carry ledger))
                  (fn-ocfg-step oc '(:complete) fn-arena)))
  :hints (("Goal" :in-theory '(fn-irc-rix-ocfg-complete-is-rix
                               fn-prc-carryp-of-refresh
                               fn-rix-ocfg-complete-is-ccar-ocfg-complete
                               fn-ccar-ocfg-complete-is-ocfg-step-complete))))

(in-theory (disable fn-irc-rix-own-complete-enabled fn-irc-rix-own-complete
                    fn-irc-rix-ocfg-complete))

; -----------------------------------------------------------------------------
; The identity prepare the host calls (books/owner-commit-carried.lisp
; fn-ccar-sn-prepare-identity, fn-ccar-ocfg-prepare-identity;
; books/owner-prepare-served.lisp fn-psrv-prepare-identity;
; books/owner-identity-served.lisp fn-oiis-prepare-identity;
; books/owner-prepare-outcome.lisp fn-pout-prepare-identity) with the gate's
; record application through the carry.  host/owner-host.lisp
; fn-owner-prepare-identity calls fn-irc-pout-prepare-identity.

(defun fn-irc-sn-prepare-identity (s event carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (or (fn-stxe-p event) (fn-stxk-p event) (fn-hstxa-p event))
           (eq (car (fn-ccar-cpe-projection-step
                     (fn-sn-consumer s) event (fn-sn-identity-next s))) :ok)
           (or (not (fn-hstxa-p event))
               (not (equal (fn-record-stamp (fn-replay-composite-held event))
                           :legacy)))
           (consp (fn-irc-apply-record (fn-sn-node s) event carry))
           (equal (fn-stxk-context-kind
                   (fn-replay-identity-step (fn-sn-identity-context s) event))
                  :ok))
      (let ((files (fn-pcar-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

(defthm fn-irc-sn-prepare-identity-is-ccar
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-sn-prepare-identity s event carry)
                  (fn-ccar-sn-prepare-identity s event)))
  :hints (("Goal" :in-theory '(fn-irc-sn-prepare-identity
                               fn-ccar-sn-prepare-identity
                               fn-irc-apply-record-is-replay-apply-record))))

(verify-guards fn-irc-sn-prepare-identity
  :hints (("Goal" :use ((:guard-theorem fn-ccar-sn-prepare-identity))
                  :in-theory (e/d (fn-irc-apply-record-is-replay-apply-record)
                                  (fn-sn-statep fn-sf-statep fn-node-statep
                                   fn-prc-carryp fn-store-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-replay-apply-record fn-replay-identity-step
                                   fn-replay-composite-record fn-spc-stage-record
                                   fn-pcar-stage-record)))))

(defun fn-irc-ocfg-prepare-identity (oc event carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (let ((o (fn-ocfg-owner oc)))
    (fn-ocfg-with-owner
     oc
     (fn-own-refresh
      (fn-own-make (fn-irc-sn-prepare-identity (fn-own-store o) event carry)
                   (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
                   (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
                   (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                   (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                   (fn-own-node-secret o) (fn-own-refused o))))))

(defthm fn-irc-ocfg-prepare-identity-is-ccar
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-ocfg-prepare-identity oc event carry)
                  (fn-ccar-ocfg-prepare-identity oc event)))
  :hints (("Goal" :in-theory '(fn-irc-ocfg-prepare-identity
                               fn-ccar-ocfg-prepare-identity
                               fn-irc-sn-prepare-identity-is-ccar))))

(verify-guards fn-irc-ocfg-prepare-identity
  :hints (("Goal" :use ((:guard-theorem fn-ccar-ocfg-prepare-identity))
                  :in-theory (e/d (fn-irc-sn-prepare-identity-is-ccar)
                                  (fn-sn-statep fn-prc-carryp fn-own-refresh
                                   fn-ccar-sn-prepare-identity)))))

(defun fn-irc-psrv-prepare-identity (oc event carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))))
  (if (and (fn-psrv-event-servedp (fn-ocfg-config oc) event)
           (fn-psrv-event-numberedp oc event))
      (fn-irc-ocfg-prepare-identity oc event carry)
    oc))

(defthm fn-irc-psrv-prepare-identity-is-psrv
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-psrv-prepare-identity oc event carry)
                  (fn-psrv-prepare-identity oc event)))
  :hints (("Goal" :in-theory '(fn-irc-psrv-prepare-identity
                               fn-psrv-prepare-identity
                               fn-irc-ocfg-prepare-identity-is-ccar))))

(defun fn-irc-oiis-prepare-identity (oc w h carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (natp h) (fn-prc-carryp carry))
                  :verify-guards nil))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-irc-psrv-prepare-identity
     oc (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) h)
     carry)))
(verify-guards fn-irc-oiis-prepare-identity
  :hints (("Goal" :in-theory (enable fn-sn-statep))))

(defthm fn-irc-oiis-prepare-identity-is-oiis
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-oiis-prepare-identity oc w h carry)
                  (fn-oiis-prepare-identity oc w h)))
  :hints (("Goal" :in-theory '(fn-irc-oiis-prepare-identity
                               fn-oiis-prepare-identity
                               fn-irc-psrv-prepare-identity-is-psrv))))

(defun fn-irc-pout-prepare-identity (oc w h carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc)) (natp h)
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (let ((next (fn-irc-oiis-prepare-identity oc w h carry)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          (fn-pout-identity-refusal-kind oc w h))
        next)))
; Guard-verified (lane depth-debt-7, row K2): the entry the host calls runs
; compiled, not as *1* code (the *1* class of bp-remainder-3's finding).
(verify-guards fn-irc-pout-prepare-identity
  :hints (("Goal" :in-theory (enable fn-sn-statep fn-sbud-oc-store))))

; KEYSTONE (host line): host/owner-host.lisp fn-owner-prepare-identity calls
; the left-hand side with the carry refreshed to the Store node's ledger; its
; word and owner are fn-pout-prepare-identity's, for every carry the host
; holds.
(defthm fn-irc-pout-prepare-identity-of-refresh-is-pout
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-pout-prepare-identity oc w h (fn-prc-refresh carry ledger))
                  (fn-pout-prepare-identity oc w h)))
  :hints (("Goal" :in-theory '(fn-irc-pout-prepare-identity
                               fn-pout-prepare-identity
                               fn-prc-carryp-of-refresh
                               fn-irc-oiis-prepare-identity-is-oiis))))

(in-theory (disable fn-irc-sn-prepare-identity fn-irc-ocfg-prepare-identity
                    fn-irc-psrv-prepare-identity fn-irc-oiis-prepare-identity
                    fn-irc-pout-prepare-identity))

;; A peer's transfer decision (books/peer-inbound.lisp fn-peer-decide-transfer,
;; the owner's fn-owner-transit-decide for every IHAVE/TAKETHIS and BP transit
;; article) with its capacity arm's admission through the carry: the one arm
;; of the decision that scanned every pin and release (Q5a-2).  Every other
;; arm is the reference's, term for term.
(defun fn-irc-peer-decide-transfer (node cfg peer msgid octets clock id subject
                                         carry)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil))
  (let* ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg))))
         (parsed (fn-article-parse octets))
         (article (if (and (fn-article-result-okp parsed)
                           (true-listp parsed))
                      (fn-article-result-article parsed)
                    nil))
         (okp (and article (fn-article-syntax-p article)))
         (check (if okp (fn-af-relayed-article-check article) nil)))
    (cond ((not record) (fn-peer-decision :refuse :not-a-peer))
          ((null (fn-cfg-peer-inbound record))
           (fn-peer-decision :refuse :no-inbound))
          ((not (fn-af-message-idp msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ((< (fn-cfg-peer-inbound-max-octets record) (len octets))
           (fn-peer-decision :refuse :oversize))
          ((fn-peer-intrinsic-refusal-of msgid okp article check
                                         (fn-peer-parse-limitp parsed octets))
           (fn-peer-decision :refuse
                             (fn-peer-intrinsic-refusal-of msgid okp article
                                                           check
                                                           (fn-peer-parse-limitp parsed octets))))
          ((fn-peer-date-futurep article cfg clock)
           (fn-peer-decision :refuse :date-future))
          ((fn-peer-path-missingp article cfg)
           (fn-peer-decision :refuse :no-path))
          ((fn-peer-history-hasp (fn-record-octets-string msgid) node)
           (fn-peer-decision :have :history))
          ((fn-path-names-p (fn-af-path-field-value article)
                            (fn-peer-local-identity cfg))
           (fn-peer-decision :refuse :loop))
          ((null (fn-peer-scope-groups (fn-peer-check-groups check) record cfg))
           (fn-peer-decision :refuse :out-of-scope))
          ((and (fn-peer-moderated-namesp
                 (fn-peer-scope-groups (fn-peer-check-groups check) record cfg)
                 (fn-cfg-value cfg) (fn-cfg-generation cfg))
                (fn-inj-absentp article *fn-mod-approved-name*))
           (fn-peer-decision :refuse :unapproved-moderated))
          ((not (fn-article-result-okp
                 (fn-article-parse (fn-peer-relayed-octets cfg peer octets))))
           (fn-peer-decision :refuse :oversize))
          ((fn-peer-stagedp (fn-record-octets-string msgid) node)
           (fn-peer-decision :defer :staged))
          ((consp (fn-node-stage node)) (fn-peer-decision :defer :busy))
          ((equal (fn-state-fenced (fn-node-acceptance node)) t)
           (fn-peer-decision :defer :fenced))
          ((not (fn-prc-admissiblep
                 (fn-node-retention node) id subject
                 :archive (fn-peer-evidence peer cfg)
                 (fn-charge-for-payload
                  (len (fn-peer-relayed-octets cfg peer octets)))
                 carry))
           (fn-peer-decision :refuse :capacity))
          (t (fn-peer-decision :want nil)))))

(defthm fn-irc-peer-decide-transfer-is-reference
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-peer-decide-transfer node cfg peer msgid octets clock
                                               id subject carry)
                  (fn-peer-decide-transfer node cfg peer msgid octets clock id
                                           subject)))
  :hints (("Goal" :in-theory '(fn-irc-peer-decide-transfer
                               fn-peer-decide-transfer
                               fn-prc-admissiblep-is-admissiblep))))

(verify-guards fn-irc-peer-decide-transfer
  :hints (("Goal" :use ((:guard-theorem fn-peer-decide-transfer))
                  :in-theory (disable (:d fn-node-statep) (:d fn-statep)
                                      (:d fn-retain-statep)
                                      (:d fn-node-state-shapep)
                                      (:d fn-cfgp) (:d fn-cfg-peer-find)
                                      (:d fn-af-message-idp)
                                      (:d fn-peer-history-hasp)
                                      (:d fn-peer-stagedp)
                                      (:d fn-retain-admissiblep)
                                      (:d fn-prc-admissiblep)
                                      (:d fn-peer-evidence)
                                      (:d fn-record-octets-string)
                                      (:d fn-cfg-peer-inbound)
                                      (:d fn-cfg-peer-inbound-groups)
                                      (:d fn-cfg-peer-inbound-max-octets)
                                      (:d fn-cfg-peer-inbound-max-inflight)
                                      (:d fn-cfg-ag-car) (:d fn-cfg-ag-cdr)))))

;; The host-called form: fn-peer-decide-transfer-under with the carry.
(defun fn-irc-peer-decide-transfer-under
    (node cfg peer msgid octets clock id subject limits carry)
  (declare (xargs :guard (fn-node-statep node)))
  (let ((d (fn-irc-peer-decide-transfer node cfg peer msgid octets clock id
                                        subject carry)))
    (if (member-equal (fn-peer-decision-kind d) '(:want :defer))
        (let ((limit (fn-peer-header-limit-refusal cfg peer octets limits)))
          (if limit (fn-peer-decision :refuse limit) d))
      d)))

;; KEYSTONE (the host's call, fn-owner-transit-decide and
;; fn-owner-bp-transit-submit's refusal reason): with the carry refreshed to
;; the Store node's ledger, the decision is fn-peer-decide-transfer-under's
;; for every carry the host holds.
(defthm fn-irc-peer-decide-transfer-under-of-refresh-is-reference
  (implies (fn-prc-carryp carry)
           (equal (fn-irc-peer-decide-transfer-under
                   node cfg peer msgid octets clock id subject limits
                   (fn-prc-refresh carry ledger))
                  (fn-peer-decide-transfer-under node cfg peer msgid octets
                                                 clock id subject limits)))
  :hints (("Goal" :in-theory '(fn-irc-peer-decide-transfer-under
                               fn-peer-decide-transfer-under
                               fn-prc-carryp-of-refresh
                               fn-irc-peer-decide-transfer-is-reference))))

(in-theory (disable fn-irc-peer-decide-transfer
                    fn-irc-peer-decide-transfer-under))

; -----------------------------------------------------------------------------
; The retention and topic prepares the host calls (host/owner-host.lisp
; fn-owner-prepare-retention: every BP undertake/release commit;
; fn-owner-prepare-topic) with the gate's record application through the
; carry (Q5a-2): books/store-node.lisp fn-sn-prepare-retention and
; fn-sn-prepare-topic, reached through fn-ocfg-step's (:store ...) arm and
; fn-psrv-prepare-topic, and books/owner-prepare-outcome.lisp's words.

(defun fn-irc-sn-prepare-retention (s event carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-store-retention-event-p event)
           (eq (car (fn-ccar-cpe-projection-step
                     (fn-sn-consumer s) event (fn-sn-identity-next s))) :ok)
           (consp (fn-irc-apply-retention-event (fn-sn-node s) event carry)))
      (let ((files (fn-pcar-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

(local
 (defthm fn-irc-retention-record-applies-as-retention-event
   (implies (fn-store-retention-event-p event)
            (equal (fn-replay-apply-record node event)
                   (fn-replay-apply-retention-event node event)))
   :hints (("Goal" :in-theory '(fn-replay-apply-record)))))

(local
 (defthm fn-irc-retention-event-is-a-store-event
   (implies (fn-store-retention-event-p event)
            (and (fn-store-event-p event) (true-listp event)))
   :hints (("Goal" :in-theory (enable fn-store-retention-event-p
                                      fn-store-event-p)))))

; KEYSTONE (sn level): the retention prepare with the admission through the
; carry and the appended-history replay carried by the relation, as
; fn-ccar-sn-prepare-identity's (fn-spc-related-identity-candidate-is-recoverable
; holds of any event the live node applies): fn-sn-prepare-retention's on
; every store fn-snt-relation admits, for every fn-prc-carryp carry.
(defthm fn-irc-sn-prepare-retention-is-reference
  (implies (and (fn-prc-carryp carry) (fn-snt-relation s))
           (equal (fn-irc-sn-prepare-retention s event carry)
                  (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-snt-typed-store-components)
                 (:instance fn-spc-related-identity-candidate-is-recoverable))
           :in-theory (union-theories
                       '(fn-irc-sn-prepare-retention fn-sn-prepare-retention
                         fn-sf-prepare-record fn-spc-stage-record
                         fn-pcar-stage-record-is-stage-record
                         fn-evc-carried-definitions
                         fn-ccar-cpe-projection-step-is-cpe-projection-step
                         fn-irc-apply-retention-event-is-reference
                         fn-irc-retention-record-applies-as-retention-event
                         fn-irc-retention-event-is-a-store-event)
                       (theory 'minimal-theory)))))

(verify-guards fn-irc-sn-prepare-retention
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-irc-retention-event-is-a-store-event)
                                  (fn-sf-statep fn-node-statep fn-store-event-p
                                   fn-store-retention-event-p fn-prc-carryp
                                   fn-replay-apply-retention-event
                                   fn-irc-apply-retention-event
                                   fn-spc-stage-record fn-pcar-stage-record)))))

(defun fn-irc-ocfg-prepare-retention (oc event carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (let ((o (fn-ocfg-owner oc)))
    (fn-ocfg-with-owner
     oc
     (fn-own-refresh
      (fn-own-make (fn-irc-sn-prepare-retention (fn-own-store o) event carry)
                   (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
                   (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
                   (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                   (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                   (fn-own-node-secret o) (fn-own-refused o))))))

(defthm fn-irc-ocfg-prepare-retention-is-ocfg-step
  (implies (and (fn-prc-carryp carry) (fn-snt-relation (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-irc-ocfg-prepare-retention oc event carry)
                  (fn-ocfg-step oc (list :store (list :prepare-retention event))
                                fn-arena)))
  :hints (("Goal"
           :in-theory (union-theories
                       '(fn-irc-ocfg-prepare-retention fn-ocfg-step
                         fn-ocfg-pass fn-own-step fn-own-store-step
                         fn-snrt-step
                         fn-irc-sn-prepare-retention-is-reference)
                       (theory 'ground-zero)))))

(verify-guards fn-irc-ocfg-prepare-retention
  :hints (("Goal" :in-theory (e/d (fn-irc-sn-prepare-retention-is-reference)
                                  (fn-sn-statep fn-prc-carryp fn-own-refresh
                                   fn-sn-prepare-retention
                                   fn-irc-sn-prepare-retention)))))

(defun fn-irc-pout-prepare-retention (oc e carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (let ((next (fn-irc-ocfg-prepare-retention oc e carry)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          :refused)
        next)))

(verify-guards fn-irc-pout-prepare-retention
  :hints (("Goal" :in-theory (e/d (fn-sbud-oc-store)
                                  (fn-sn-statep fn-prc-carryp
                                   fn-irc-ocfg-prepare-retention)))))

; KEYSTONE (host line): host/owner-host.lisp fn-owner-prepare-retention calls
; the left-hand side with the carry refreshed to the Store node's ledger; its
; word and owner are fn-pout-prepare-retention's, for every carry the host
; holds, on every owner whose Store the maintained store relation admits
; (fn-snt-relation, which fn-own-relation conjoins: the identity prepare's
; premise, fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation): no
; appended-history replay and no ledger scan.
(defthm fn-irc-pout-prepare-retention-of-refresh-is-pout
  (implies (and (fn-prc-carryp carry) (fn-snt-relation (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-irc-pout-prepare-retention oc e (fn-prc-refresh carry ledger))
                  (fn-pout-prepare-retention oc e fn-arena)))
  :hints (("Goal" :in-theory '(fn-irc-pout-prepare-retention
                               fn-pout-prepare-retention
                               fn-prc-carryp-of-refresh
                               fn-irc-ocfg-prepare-retention-is-ocfg-step))))

(in-theory (disable fn-irc-sn-prepare-retention fn-irc-ocfg-prepare-retention
                    fn-irc-pout-prepare-retention))

(defun fn-irc-sn-prepare-topic (s event carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-th-topic-eventp event)
           (not (fn-th-topic-v1-anchorp event))
           (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) event)) :ok)
           (consp (fn-irc-apply-record (fn-sn-node s) event carry)))
      (let ((files (fn-pcar-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

(local
 (defthm fn-irc-topic-event-is-a-store-event
   (implies (fn-th-topic-eventp event)
            (and (fn-store-event-p event) (true-listp event)))
   :hints (("Goal" :in-theory (enable fn-th-topic-eventp fn-store-event-p)))))

; KEYSTONE (sn level): the topic prepare with the appended-history replay
; carried by the relation (fn-spc-related-identity-candidate-is-recoverable),
; fn-sn-prepare-topic's on every store fn-snt-relation admits.
(defthm fn-irc-sn-prepare-topic-is-reference
  (implies (and (fn-prc-carryp carry) (fn-snt-relation s))
           (equal (fn-irc-sn-prepare-topic s event carry)
                  (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :use (fn-snt-relation-implies-structural-state
                 (:instance fn-snt-typed-store-components)
                 (:instance fn-spc-related-identity-candidate-is-recoverable))
           :in-theory (union-theories
                       '(fn-irc-sn-prepare-topic fn-sn-prepare-topic
                         fn-sf-prepare-record fn-spc-stage-record
                         fn-pcar-stage-record-is-stage-record
                         fn-evc-carried-definitions
                         fn-irc-apply-record-is-replay-apply-record
                         fn-irc-topic-event-is-a-store-event)
                       (theory 'minimal-theory)))))

(verify-guards fn-irc-sn-prepare-topic
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-irc-topic-event-is-a-store-event)
                                  (fn-sf-statep fn-node-statep fn-store-event-p
                                   fn-th-topic-eventp fn-prc-carryp
                                   fn-replay-apply-record fn-irc-apply-record
                                   fn-spc-stage-record fn-pcar-stage-record)))))

(defun fn-irc-psrv-prepare-topic (oc event carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o)))
    (if (and (fn-store-event-p event)
             (eq (car (fn-ccar-cpe-projection-step
                       (fn-sn-consumer s) event (fn-sn-identity-next s)))
                 :ok))
        (fn-ocfg-with-owner
         oc
         (fn-own-refresh
          (fn-own-make (fn-irc-sn-prepare-topic s event carry)
                       (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
                       (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
                       (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                       (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                       (fn-own-node-secret o) (fn-own-refused o))))
      oc)))

(defthm fn-irc-psrv-prepare-topic-is-psrv
  (implies (and (fn-prc-carryp carry) (fn-snt-relation (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-irc-psrv-prepare-topic oc event carry)
                  (fn-psrv-prepare-topic oc event)))
  :hints (("Goal" :in-theory '(fn-irc-psrv-prepare-topic
                               fn-psrv-prepare-topic
                               fn-irc-sn-prepare-topic-is-reference))))

(verify-guards fn-irc-psrv-prepare-topic
  :hints (("Goal" :use ((:guard-theorem fn-psrv-prepare-topic))
                  :in-theory (e/d (fn-irc-sn-prepare-topic-is-reference)
                                  (fn-sn-statep fn-prc-carryp fn-own-refresh
                                   fn-sn-prepare-topic fn-irc-sn-prepare-topic)))))

(defun fn-irc-pout-prepare-topic (oc e carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (let ((next (fn-irc-psrv-prepare-topic oc e carry)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          :refused)
        next)))

(verify-guards fn-irc-pout-prepare-topic
  :hints (("Goal" :in-theory (e/d (fn-sbud-oc-store)
                                  (fn-sn-statep fn-prc-carryp
                                   fn-irc-psrv-prepare-topic)))))

; KEYSTONE (host line): host/owner-host.lisp fn-owner-prepare-topic calls the
; left-hand side with the carry refreshed to the Store node's ledger; its word
; and owner are fn-pout-prepare-topic's, for every carry the host holds, on
; every owner whose Store fn-snt-relation admits: no appended-history replay.
(defthm fn-irc-pout-prepare-topic-of-refresh-is-pout
  (implies (and (fn-prc-carryp carry) (fn-snt-relation (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-irc-pout-prepare-topic oc e (fn-prc-refresh carry ledger))
                  (fn-pout-prepare-topic oc e)))
  :hints (("Goal" :in-theory '(fn-irc-pout-prepare-topic
                               fn-pout-prepare-topic
                               fn-prc-carryp-of-refresh
                               fn-irc-psrv-prepare-topic-is-psrv))))

(in-theory (disable fn-irc-sn-prepare-topic fn-irc-psrv-prepare-topic
                    fn-irc-pout-prepare-topic))
