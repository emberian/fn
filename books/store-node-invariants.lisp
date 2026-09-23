; Correspondence for actual live node/file completion, without a trusted reply.
(in-package "ACL2")
(include-book "store-node")
(include-book "records-seam")
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-shape-vocabulary)))

; The core definitions these correspondence proofs open (the core exports
; keystones only, docs/proof-style.md s2); local, named once.
(local (deftheory fn-snx-core-definitions
         (union-theories (union-theories '(fn-articlep fn-pendingp fn-statep fn-initial-state fn-install-pending
            fn-clear-pending fn-accept-prepare fn-accept-complete fn-accept-recover
            fn-pending-matchesp
            fn-retain-obligationp fn-retain-releasep fn-retain-statep
            fn-retain-initial-state fn-retain-admissiblep fn-retain-admit
            fn-retain-release
            fn-node-stagep fn-node-bindingp fn-node-statep fn-node-initial-state
            fn-node-pending-matchesp fn-node-prepare fn-node-complete fn-node-recover
            fn-replay-okp fn-replay-advance-okp fn-replay-advance-txid) (theory 'fn-acceptance-invariants-vocabulary)) (theory 'fn-node-invariants-vocabulary))))

; The composed definitions and the kernel steps these proofs open are
; enabled locally (docs/proof-style.md s2); the records stay opaque.
(local (in-theory (e/d (fn-sn-statep fn-sn-initial fn-sn-pending-record
                        fn-sn-record-bindsp fn-sn-prepare-node fn-sn-prepare
                        fn-sn-completion-record fn-sn-completion-enabledp
                        fn-sn-finish fn-sn-file-step fn-sn-io fn-sn-crash
                        fn-sn-recover fn-sn-fence-node fn-sn-resolve-node
                        fn-sf-initial-state fn-sf-history-recoverablep
                        fn-sf-replay-node fn-sf-refuse-reservation
                        fn-sf-prepublish-abort fn-sf-abort-completion
                        fn-sf-lose-success fn-sf-recover fn-sf-crash-imagep
                        fn-replay-apply-record fn-replay-okp fn-replay-faultp
                        fn-replay-advance-okp fn-node-pending-matchesp
                        fn-store-files-invariants-vocabulary)
                       (fn-node-statep fn-sf-statep fn-record-p
                        fn-node-prepare fn-node-complete fn-node-recover
                        fn-replay-advance-txid fn-replay fn-replay-loop
                        fn-retain-statep fn-node-initial-state fn-sf-prepare-record
                        fn-sf-start-frontier fn-sf-frontier-file-result
                        fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                        fn-sf-record-file-result fn-sf-record-link-result
                        fn-sf-record-dir-result fn-sf-recovery-barrier
                        fn-sf-core-completion fn-sf-emit-success
                        fn-sf-crash))))

(defthm fn-sn-initial-is-state
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-sn-statep (fn-sn-initial groups capacity))))

(defthm fn-sn-prepare-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-prepare s record))))

(defthm fn-sn-file-step-preserves-state
  (implies (fn-sf-statep files)
           (fn-sf-statep (fn-sn-file-step files operation result)))
  :hints (("Goal" :in-theory (disable fn-sf-start-frontier
    fn-sf-frontier-file-result fn-sf-frontier-replace-result
    fn-sf-frontier-dir-result fn-sf-record-file-result
    fn-sf-record-link-result fn-sf-record-dir-result fn-sf-recovery-barrier))))

(defthm fn-sn-io-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-io s operation result)))
  :hints (("Goal" :in-theory (disable fn-sn-file-step ))))

(local (defthm fn-sn-record-p-implies-string-msgid
         (implies (fn-record-p record)
                  (stringp (fn-record-msgid record)))
         :hints (("Goal" :in-theory (enable fn-record-p)))))

; The identity branch appends the verdict pairs the identity fold produced to
; the ones the state already holds.  Both conjuncts of `fn-sn-verdict-listp'
; for a produced pair come from `fn-stxe-p': the Message-ID field is a string,
; the token is one of `*fn-stx-verdicts*' and the keyring generation is a
; uint32.  Stated here so the branch does not need the record codec to see it.
(local
 (defthm fn-sn-verdict-listp-of-replay-verdict-pairs
   (fn-sn-verdict-listp (fn-replay-verdict-pairs events))
   :hints (("Goal" :induct (fn-replay-verdict-pairs events)
            :in-theory (e/d (fn-replay-verdict-pairs fn-sn-verdict-listp
                             fn-stx-make-verdict fn-stx-verdict-token
                             fn-stx-verdict-generation fn-stxe-tokenp)
                            (fn-record-shape-vocabulary)
                            (fn-record-msgidp))))))

(local
 (defthm fn-sn-verdict-listp-of-append
   (implies (and (fn-sn-verdict-listp a) (fn-sn-verdict-listp b))
            (fn-sn-verdict-listp (append a b)))
   :hints (("Goal" :induct (fn-sn-verdict-listp a)
            :in-theory (enable fn-sn-verdict-listp)))))

; The retention branch of `fn-sn-finish' calls `fn-replay-apply-retention-event'
; directly, so the exported fact about `fn-replay-apply-record' does not reach
; it by rewriting; this is that fact restricted to the branch, with the record
; codec closed while it is proved.
(local
 (defthm fn-sn-retention-event-preserves-node
   (implies (and (fn-node-statep node)
                 (fn-store-retention-event-p event)
                 (consp (fn-replay-apply-retention-event node event)))
            (fn-node-statep (fn-replay-apply-retention-event node event)))
   :hints (("Goal"
            :use ((:instance fn-replay-apply-record-non-nil-is-node-state
                             (record event)))
            :in-theory (e/d (fn-replay-apply-record fn-store-event-p)
                            (fn-record-shape-vocabulary
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-replay-apply-retention-event))))))

; ---------------------------------------------------------------------------
; The two conjuncts of `fn-sn-statep' that the identity replay context carries
; into the state: the keyring snapshot list and the next identity sequence
; number.  `fn-sn-finish' (through fn-sn-finish-identity) and `fn-sn-recover'
; (through fn-replay-identity) both hand a context's third and second fields
; straight to `fn-sn-make-v2', so the invariant on them is whatever the
; identity machine left there.  Neither field is ever the record codec's
; business, which is why these are stated rather than reached by unfolding --
; with the codec open the composed goals grow a term instead of proving.
;
; They are stated over `caddr' and `cadr' rather than over
; `fn-stxk-context-snapshots' and `fn-stxk-context-next' because those two are
; `mbe' definitions whose :logic bodies are exactly those calls and they are
; enabled here, so the goals carry the `car'/`cdr' nest and a rule stated over
; the accessor would have nothing to match.  The `next' facts are stated as
; the two conjuncts `fn-sn-statep' asks for rather than as `natp' for the same
; reason.  The theorems below open `fn-stxk-context' and `fn-stxk-fault' (a
; six-element list and a repack of one) so the contexts reduce to their fields.

(local
 (defthm fn-sn-keyring-snapshot-listp-of-fn-stxk-apply-snapshot
   (implies (and (fn-sn-keyring-snapshot-listp (caddr ctx))
                 (fn-stxk-p e))
            (fn-sn-keyring-snapshot-listp
             (caddr (fn-stxk-apply-snapshot ctx e))))
   :hints (("Goal"
            :in-theory (e/d (fn-stxk-apply-snapshot fn-stxk-fault
                             fn-stxk-context fn-sn-keyring-snapshot-listp)
                            (fn-record-shape-vocabulary
                             fn-stxk-p fn-stxe-p fn-stxa-p
                             fn-stxk-find fn-stxk-same-snapshotp))))))

(local
 (defthm fn-sn-identity-next-of-fn-stxk-apply-snapshot
   (implies (and (integerp (cadr ctx)) (<= 0 (cadr ctx)))
            (and (integerp (cadr (fn-stxk-apply-snapshot ctx e)))
                 (<= 0 (cadr (fn-stxk-apply-snapshot ctx e)))))
   :hints (("Goal"
            :in-theory (e/d (fn-stxk-apply-snapshot fn-stxk-fault
                             fn-stxk-context)
                            (fn-record-shape-vocabulary
                             fn-stxk-p fn-stxe-p fn-stxa-p
                             fn-stxk-find fn-stxk-same-snapshotp))))))

; `fn-stxk-apply-verdict' conses onto the verdicts and never onto the
; snapshots; it advances the same sequence number the snapshot step does.
(local
 (defthm fn-sn-keyring-snapshot-listp-of-fn-stxk-apply-verdict
   (implies (fn-sn-keyring-snapshot-listp (caddr ctx))
            (fn-sn-keyring-snapshot-listp
             (caddr (fn-stxk-apply-verdict ctx e))))
   :hints (("Goal"
            :in-theory (e/d (fn-stxk-apply-verdict fn-stxk-fault
                             fn-stxk-context fn-sn-keyring-snapshot-listp)
                            (fn-record-shape-vocabulary
                             fn-stxk-p fn-stxe-p fn-stxa-p
                             fn-stxk-find fn-stxk-same-snapshotp))))))

(local
 (defthm fn-sn-identity-next-of-fn-stxk-apply-verdict
   (implies (and (integerp (cadr ctx)) (<= 0 (cadr ctx)))
            (and (integerp (cadr (fn-stxk-apply-verdict ctx e)))
                 (<= 0 (cadr (fn-stxk-apply-verdict ctx e)))))
   :hints (("Goal"
            :in-theory (e/d (fn-stxk-apply-verdict fn-stxk-fault
                             fn-stxk-context)
                            (fn-record-shape-vocabulary
                             fn-stxk-p fn-stxe-p fn-stxa-p
                             fn-stxk-find fn-stxk-same-snapshotp))))))

; One step of the identity replay, over every arm of its dispatch: the two
; apply functions above, the sequence fault, the composite fault and the
; `fn-replay-identity-advance' arm for a record the identity machine does not
; own.
(local
 (defthm fn-sn-identity-fields-of-fn-replay-identity-step
   (implies (and (fn-sn-keyring-snapshot-listp (caddr ctx))
                 (integerp (cadr ctx)) (<= 0 (cadr ctx)))
            (and (fn-sn-keyring-snapshot-listp
                  (caddr (fn-replay-identity-step ctx event)))
                 (integerp (cadr (fn-replay-identity-step ctx event)))
                 (<= 0 (cadr (fn-replay-identity-step ctx event)))))
   :hints (("Goal"
            :in-theory (e/d (fn-replay-identity-step
                             fn-replay-identity-advance
                             fn-stxk-fault fn-stxk-context)
                            (fn-record-shape-vocabulary
                             fn-stxk-p fn-stxe-p fn-stxa-p fn-store-event-p
                             fn-stxk-apply-snapshot fn-stxk-apply-verdict
                             fn-stxk-find fn-stxk-same-snapshotp))))))

; And the fold `fn-sn-recover' runs over the replayed records.
(local
 (defthm fn-sn-identity-fields-of-fn-replay-identity-loop
   (implies (and (fn-sn-keyring-snapshot-listp (caddr ctx))
                 (integerp (cadr ctx)) (<= 0 (cadr ctx)))
            (and (fn-sn-keyring-snapshot-listp
                  (caddr (fn-replay-identity-loop records ctx)))
                 (integerp (cadr (fn-replay-identity-loop records ctx)))
                 (<= 0 (cadr (fn-replay-identity-loop records ctx)))))
   :hints (("Goal"
            :induct (fn-replay-identity-loop records ctx)
            :in-theory (e/d (fn-replay-identity-loop fn-stxk-fault
                             fn-stxk-context)
                            (fn-record-shape-vocabulary
                             fn-stxk-p fn-stxe-p fn-stxa-p fn-store-event-p
                             fn-replay-identity-step
                             fn-stxk-apply-snapshot fn-stxk-apply-verdict
                             fn-stxk-find fn-stxk-same-snapshotp))))))

(defthm fn-sn-finish-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-finish s)))
  ; The record codec stays closed here.  This book enables
  ; `fn-record-shape-vocabulary' at the top for its field lemmas, and that
  ; theory carries (:d fn-record-p), (:d fn-record-encode) and
  ; (:d fn-record-decode-exact); `fn-sn-finish' reads the completion record
  ; through four accessors and dispatches on four recognizers, so with the
  ; codec open this goal grows a term instead of proving and does not leave
  ; Goal'' (measured 2026-09-22, hbox certify-20260922T060312Z-2712514 and
  ; certify-20260922T064054Z-2733885).  The three node facts the branches need
  ; come in by `:use' instead of by unfolding.
  :hints (("Goal"
           :use ((:instance fn-sn-record-p-implies-string-msgid
                            (record (fn-sn-completion-record s)))
                 (:instance fn-replay-apply-record-non-nil-is-node-state
                            (node (fn-sn-node s))
                            (record (fn-sn-completion-record s)))
                 (:instance fn-node-complete-preserves-state
                            (s (fn-sn-node s))
                            (txid (fn-record-txid (fn-sn-completion-record s)))
                            (generation
                             (fn-record-generation (fn-sn-completion-record s)))
                            (completion-status :durable)))
           :in-theory (e/d (fn-stxk-context fn-stxk-fault
                            ; withdrawn at store-node's export since
                            ; 2026-09-23; the identity arm's snapshot list
                            ; is read through it.
                            fn-sn-identity-context)
                           (fn-record-shape-vocabulary
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-th-topic-eventp fn-th-prefix-step
                            fn-th-local-admin-eventp
                            fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-node-complete
                            fn-sf-core-completion
                            fn-sf-emit-success)))))

; Keystone for the host-called acceptance subject.  host/store-node-host.lisp
; `fn-store-sn-finish' calls fn-sn-finish; on its enabled durable acceptance
; branch the cheap retrieval query returns exactly the verdict computed over
; the accepted record under the then-current keyring generation.
;
; The three hypotheses after the enabling one ARE that branch.  `fn-sn-finish'
; dispatches on `retentionp' and on `identityp', and only its third arm calls
; `fn-sn-update-accepted', which is the one site that installs a
; `(msgid . verdict)' pair.  Until 2026-09-22 this theorem carried only
; `fn-sn-completion-enabledp' and claimed the equation on all three arms; it
; was submitted on 2026-09-21 (6e992351) into a book that has not certified
; since 2026-09-21 01:20, so it was never proved, and on the retention arm it
; is false: that arm keeps `(fn-sn-verdicts s)' exactly, while the right-hand
; side is a `fn-stx-make-verdict' triple that is never NIL
; (fn-stx-verdict-of-octets, books/stx-lace.lisp).  The branch the sentence
; above always named is now the branch the statement names.  What the other
; two arms do to this query is stated next; nothing here says a retention or
; identity completion records an acceptance verdict, because it does not.
(defthm fn-sn-finish-records-the-acceptance-verdict
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                (not (fn-stxe-p (fn-sn-completion-record s)))
                (not (fn-stxk-p (fn-sn-completion-record s)))
                (not (fn-stxa-p (fn-sn-completion-record s)))
                (not (fn-cpe-eventp (fn-sn-completion-record s)))
                (not (fn-th-topic-eventp (fn-sn-completion-record s))))
           (equal
            (fn-sn-verdict-lookup
             (fn-sn-finish s)
             (fn-record-msgid (fn-sn-completion-record s)))
            (fn-stx-verdict-of-octets
             (fn-record-payload (fn-sn-completion-record s))
             (fn-sn-keyring s)
             (fn-sn-keyring-generation s))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-verdict-lookup fn-sn-verdict-lookup-list)
                           (fn-record-shape-vocabulary
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-th-topic-eventp fn-th-prefix-step
                            fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-node-complete
                            fn-sf-core-completion
                            fn-sf-emit-success)))))

; The retention arm of the same dispatch, which is what the hypotheses above
; exclude: it advances the identity sequence and reindexes, and it does not
; touch the acceptance evidence, so this query answers exactly as it did
; before the completion, for every Message-ID.
(defthm fn-sn-finish-of-a-retention-event-keeps-the-verdicts
  (implies (fn-store-retention-event-p (fn-sn-completion-record s))
           (equal (fn-sn-verdict-lookup (fn-sn-finish s) msgid)
                  (fn-sn-verdict-lookup s msgid)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-verdict-lookup fn-sn-verdict-lookup-list
                            fn-sn-advance-identity-next fn-sn-update-indexed)
                           (fn-record-shape-vocabulary
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-replay-apply-record
                            fn-replay-apply-retention-event
                            fn-node-complete
                            fn-sf-core-completion
                            fn-sf-emit-success)))))

; Key rotation changes current trust and its generation, but it cannot
; rewrite the acceptance observation that the retrieval path exposes.
(defthm fn-sn-set-keyring-preserves-recorded-verdict
  (equal (fn-sn-verdict-lookup (fn-sn-set-keyring s keyring) msgid)
         (fn-sn-verdict-lookup s msgid))
  :hints (("Goal" :in-theory (enable fn-sn-verdict-lookup
                                      fn-sn-set-keyring))))

(defthm fn-sn-crash-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal" :in-theory (disable fn-sf-crash))))

(defthm fn-sn-successful-replay-node-is-state
  (implies (fn-sf-history-recoverablep groups capacity records frontier)
           (fn-node-statep (fn-sf-replay-node groups capacity records frontier)))
  :hints (("Goal" :in-theory (disable fn-sf-replay-node))))

; The successes conjunct is what `fn-sn-recover' needs to see that the file
; state it builds to refuse a composed recovery is built out of one state's
; own history: `fn-sf-recover' carries the emitted successes across both of
; its arms exactly as it carries the records and the frontier.
(defthm fn-sn-file-recovery-retains-history
  (and (equal (fn-sf-records (fn-sf-recover files groups capacity))
              (fn-sf-records files))
       (equal (fn-sf-frontier (fn-sf-recover files groups capacity))
              (fn-sf-frontier files))
       (equal (fn-sf-successes (fn-sf-recover files groups capacity))
              (fn-sf-successes files))))

(defthm fn-sn-file-recovery-produces-valid-replay
  (implies (and (fn-sf-statep files)
                (equal (fn-sf-phase files) :replaying)
                (equal (fn-sf-phase (fn-sf-recover files groups capacity))
                       :recovering))
           (fn-node-statep (fn-sf-replay-node groups capacity
                              (fn-sf-records files) (fn-sf-frontier files))))
  :hints (("Goal" :in-theory (disable fn-sf-replay-node))))

; `fn-sn-recover' refuses the composed recovery by rebuilding the file state
; in :fault out of the history it just replayed (books/store-node.lisp, added
; by 40bb3f74 on 2026-09-21, which did not update this book).  That rebuild is
; the else-branch of `fn-sf-recover' written out at the composed level, so it
; is a file state whenever its argument is: the :fault arm of
; `fn-sf-phase-shapep' asks only that the two candidates and the completion
; are absent, and the frontier, the records and the successes cross unchanged.
; `fn-sf-statep' is withdrawn in this book, so the conjecture below has no way
; to see that without the rule.
(local
 (defthm fn-sf-statep-of-the-composed-recovery-fault
   (implies (fn-sf-statep files)
            (fn-sf-statep (fn-sf-make :fault (fn-sf-frontier files) nil
                                      (fn-sf-records files) nil nil
                                      (fn-sf-successes files) 0)))
   :hints (("Goal" :in-theory (enable fn-sf-statep fn-sf-phase-shapep)))))

(defthm fn-sn-recover-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-recover s)))
  :hints (("Goal" :use ((:instance fn-sn-file-recovery-produces-valid-replay
                                   (files (fn-sn-files s))
                                   (groups (fn-sn-groups s))
                                   (capacity (fn-sn-capacity s))))
           :in-theory (disable fn-sf-replay-node fn-sf-recover))))

; Every portable record value is equal to its counterpart in the actual staged
; acceptance/retention transaction, not merely to a sequence/txid reply string.
(defthm fn-sn-record-binds-pending-fields
  (implies (fn-sn-record-bindsp node record)
           (let ((p (fn-state-pending (fn-node-acceptance node)))
                 (stage (fn-node-stage node)))
             (and (equal (fn-record-txid record) (fn-pending-txid p))
                  (equal (fn-record-generation record) (fn-pending-generation p))
                  (equal (fn-record-msgid record) (fn-pending-msgid p))
                  (equal (fn-record-payload record) (fn-pending-payload p))
                  (equal (fn-record-groups record) (fn-pending-groups p))
                  (equal (fn-record-obligation-id record) (fn-node-stage-id stage))
                  (equal (fn-record-content-subject record) (fn-node-stage-subject stage))
                  (equal (fn-record-release-evidence record) (fn-node-stage-evidence stage))
                  (equal (fn-record-charge record) (fn-node-stage-charge stage))
                  (equal (fn-record-stamp record) (fn-pending-stamp p)))))
  :rule-classes nil)

(defun fn-sn-committed-recordp (node record)
  (let* ((article (fn-find-article (fn-record-msgid record)
                                  (fn-state-articles (fn-node-acceptance node))))
         (binding (fn-node-find-binding (fn-record-msgid record)
                                         (fn-node-bindings node)))
         (pin (fn-retain-find-id (fn-record-obligation-id record)
                                 (fn-retain-pins (fn-node-retention node)))))
    (and (consp article)
         (equal (fn-article-msgid article) (fn-record-msgid record))
         (equal (fn-article-payload article) (fn-record-payload record))
         (equal (fn-article-groups article) (fn-record-groups record))
         (equal (fn-article-stamp article) (fn-record-stamp record))
         (equal (fn-article-pin article) t)
         (equal binding (fn-node-make-binding
                         (fn-record-msgid record) (fn-record-content-subject record)
                         (fn-record-obligation-id record)))
         (equal pin (fn-retain-make-obligation
                     (fn-record-obligation-id record)
                     (fn-record-content-subject record) :archive
                     (fn-record-release-evidence record) (fn-record-charge record))))))

(defthm fn-sn-actual-durable-completion-installs-record
  (implies (fn-sn-record-bindsp node record)
           (fn-sn-committed-recordp
            (fn-node-complete node (fn-record-txid record)
                              (fn-record-generation record) :durable)
            record))
  :hints (("Goal" :use fn-sn-record-binds-pending-fields
           :in-theory (enable fn-node-complete fn-node-statep fn-statep fn-snx-core-definitions))))

; -by-definition: the else branch of fn-sn-finish with its test negated.
(defthm fn-sn-finish-disabled-is-no-op
  (implies (not (fn-sn-completion-enabledp s))
           (equal (fn-sn-finish s) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-sn-completion-enabledp))))

; THE THREE ARMS OF `fn-sn-finish'.  Until 2026-09-21 this function had one
; arm and the theorems below said so.  `6ab2c783' (12:43) gave it a retention
; arm whose node is `fn-replay-apply-retention-event', and `4bb7bb3d' (13:24)
; an identity arm whose node is `fn-replay-apply-record'; this book has not
; certified since 2026-09-21 01:20, so neither commit's consequences were ever
; proved here and these statements have been false on the two new arms since.
; Each one below now names the arm it is about.  What the other two arms do is
; not weakened away: `fn-sn-completion-enabledp' already carries the condition
; each arm must meet (books/store-node.lisp), and the success keystone below
; keeps that conjunct at full strength for all three.
(local
 (defthm fn-snx-completion-projection-ok-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-cpe-eventp (fn-sn-completion-record s)))
            (eq (car (fn-cpe-projection-step
                      (fn-sn-consumer s) (fn-sn-completion-record s)
                      (fn-sn-identity-next s))) :ok))
   :hints (("Goal" :in-theory (enable fn-sn-completion-enabledp)))))
(defthm fn-sn-finish-is-actual-durable-completion
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                (not (fn-stxe-p (fn-sn-completion-record s)))
                (not (fn-stxk-p (fn-sn-completion-record s)))
                (not (fn-stxa-p (fn-sn-completion-record s)))
                (not (fn-cpe-eventp (fn-sn-completion-record s)))
                (not (fn-th-topic-eventp (fn-sn-completion-record s))))
           (equal (fn-sn-node (fn-sn-finish s))
                  (fn-node-complete (fn-sn-node s)
                    (fn-record-txid (fn-sn-completion-record s))
                    (fn-record-generation (fn-sn-completion-record s))
                    :durable)))
  ; The record codec stays closed, as it does for `fn-sn-finish-preserves-
  ; state': with it open the three-arm dispatch unfolds the codec on every
  ; branch and this goal split into 5121 subgoals (hbox
  ; certify-20260922T080951Z-2784602).  On the arm named above the node
  ; component is the `fn-node-complete' call itself, so nothing here needs to
  ; look inside a record.
  :hints (("Goal" :in-theory (disable fn-sn-completion-enabledp
                                      fn-sn-completion-record
                                      fn-record-shape-vocabulary
                                      fn-stxe-p fn-stxk-p fn-stxa-p
                                      fn-th-topic-eventp
                                      fn-replay-apply-record
                                      fn-replay-apply-retention-event
                                      fn-node-complete
                                      fn-sf-core-completion
                                      fn-sf-emit-success))))

(defthm fn-sn-finish-installs-exact-article-and-archive-pin
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                (not (fn-stxe-p (fn-sn-completion-record s)))
                (not (fn-stxk-p (fn-sn-completion-record s)))
                (not (fn-stxa-p (fn-sn-completion-record s)))
                (not (fn-cpe-eventp (fn-sn-completion-record s)))
                (not (fn-th-topic-eventp (fn-sn-completion-record s))))
           (fn-sn-committed-recordp (fn-sn-node (fn-sn-finish s))
                                    (fn-sn-completion-record s)))
  :hints (("Goal" :use (fn-sn-finish-is-actual-durable-completion
                         (:instance fn-sn-actual-durable-completion-installs-record
                          (node (fn-sn-node s))
                          (record (fn-sn-completion-record s))))
           ; The codec stays closed: the four branch hypotheses this shares
           ; with the theorem it uses are `fn-stxe-p', `fn-stxk-p',
           ; `fn-stxa-p' and `fn-store-retention-event-p' calls, and with the
           ; codec open they unfold on both sides instead of cancelling.
           :in-theory (disable fn-sn-finish fn-sn-committed-recordp
                               fn-sn-record-bindsp fn-sn-completion-record
                               fn-record-shape-vocabulary
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-identity-step
                               fn-sn-identity-context
                               fn-node-complete
                               fn-sf-core-completion fn-sf-emit-success))))

(defthm fn-sn-finish-acknowledges-exact-pair
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-successes (fn-sn-files (fn-sn-finish s)))
                  (append (fn-sf-successes (fn-sn-files s))
                          (list (fn-sf-completion (fn-sn-files s))))))
  ; All three arms of `fn-sn-finish' hand the same file state on: the core
  ; completion and the emitted success are computed once, above the dispatch,
  ; from the composed `fn-store-event-sequence' and `fn-store-event-txid' --
  ; which is what this `:use' instantiates.  The record codec stays closed for
  ; the same reason it does two theorems above: the dispatch would otherwise
  ; unfold it on every arm.
  :hints (("Goal"
           :use ((:instance fn-sf-core-completion-preserves-state
                    (s (fn-sn-files s))
                    (sequence (fn-store-event-sequence
                               (fn-sn-completion-record s)))
                    (txid (fn-store-event-txid (fn-sn-completion-record s)))))
           :in-theory (e/d (fn-sf-core-completion fn-sf-emit-success)
                            (fn-sn-record-bindsp fn-sn-completion-record
                             fn-record-shape-vocabulary
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-replay-apply-record
                             fn-replay-apply-retention-event
                             fn-node-complete)))))

; The success keystone.  Its first conjunct is the one that carries the
; safety property and it is stated for all three arms at full strength: no
; acknowledgement appears unless the completion was enabled, and
; `fn-sn-completion-enabledp' is what makes each arm's node transition actual
; (the retention arm demands a non-nil `fn-replay-apply-retention-event', the
; identity arm a non-nil `fn-replay-apply-record' under an :ok identity
; context, the acceptance arm `fn-sn-record-bindsp').  The article-specific
; conclusions hold on the acceptance arm, which is where an article record is
; what was completed; see the note above `fn-sn-finish-is-actual-durable-
; completion'.
(defthm fn-sn-new-success-requires-actual-matching-durable-node-completion
  (implies (not (equal (fn-sf-successes (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-successes (fn-sn-files s))))
           (and (fn-sn-completion-enabledp s)
                (implies
                 (and (not (fn-store-retention-event-p
                            (fn-sn-completion-record s)))
                      (not (fn-stxe-p (fn-sn-completion-record s)))
                      (not (fn-stxk-p (fn-sn-completion-record s)))
                      (not (fn-stxa-p (fn-sn-completion-record s)))
                      (not (fn-cpe-eventp (fn-sn-completion-record s)))
                      (not (fn-th-topic-eventp
                            (fn-sn-completion-record s))))
                 (and (fn-sn-record-bindsp (fn-sn-node s)
                                           (fn-sn-completion-record s))
                      (equal (fn-sn-node (fn-sn-finish s))
                             (fn-node-complete (fn-sn-node s)
                               (fn-record-txid (fn-sn-completion-record s))
                               (fn-record-generation
                                (fn-sn-completion-record s))
                               :durable))
                      (fn-sn-committed-recordp (fn-sn-node (fn-sn-finish s))
                                               (fn-sn-completion-record s))))))
  :hints (("Goal" :use (fn-sn-finish-is-actual-durable-completion
                         fn-sn-finish-installs-exact-article-and-archive-pin
                         fn-sn-finish-disabled-is-no-op)
           :cases ((fn-sn-completion-enabledp s))
           :in-theory (disable fn-record-shape-vocabulary
                               fn-stxe-p fn-stxk-p fn-stxa-p
                               fn-th-topic-eventp
                               fn-replay-apply-record
                               fn-replay-apply-retention-event
                               fn-replay-identity-step
                               fn-sn-identity-context
                               fn-node-complete
                               fn-sf-core-completion fn-sf-emit-success
                               fn-sn-finish fn-sn-completion-record
                               fn-sn-record-bindsp fn-sn-committed-recordp))))

; A matching live proposal has exactly the same durable meaning as a record
; interpreted by replay.  This is equality of the entire node: watermarks,
; memberships, articles, retention accounting, archive pins, bindings and txid.
; An article record is none of the other four store events, by length alone:
; `fn-record' has ten fields, a retention event nine, `fn-stxe' and `fn-stxa'
; eight and `fn-stxk' six (books/defrecord.lisp writes the shape as a `len'
; check).  `fn-replay-apply-record' tests the other four first, so this is
; what says a record reaches its article arm.
(local
 (defthm fn-sn-an-article-record-is-no-other-store-event
   (implies (fn-record-p record)
            (and (not (fn-store-retention-event-p record))
                 (not (fn-stxe-p record))
                 (not (fn-stxk-p record))
                 (not (fn-stxa-p record))
                 (not (fn-th-topic-eventp record))
                 (not (fn-cpe-eventp record))))
   :hints (("Goal"
            :in-theory (e/d ((:d fn-record-p) (:d fn-record-shapep)
                             (:d fn-store-retention-event-p)
                             (:d fn-stxe-p) (:d fn-stxe-shapep)
                             (:d fn-stxk-p) (:d fn-stxk-shapep)
                             (:d fn-stxa-p) (:d fn-stxa-shapep)
                             (:d fn-cpe-eventp)
                             (:d fn-th-topic-eventp)
                             (:d fn-th-local-admin-eventp))
                            ((:d fn-stxe-bounded-octetsp)
                             (:d fn-record-uint32p) (:d fn-record-msgidp)
                             (:d fn-record-payloadp)
                             (:d fn-record-groups-validp)
                             (:d fn-record-metadata-bytes-p)))))))

; And on that arm the composed accessors are the record's own.
(local
 (defthm fn-sn-store-event-fields-of-an-article-record
   (implies (fn-record-p record)
            (and (equal (fn-store-event-kind record) :article)
                 (equal (fn-store-event-sequence record)
                        (fn-record-sequence record))
                 (equal (fn-store-event-txid record) (fn-record-txid record))
                 (equal (fn-store-event-generation record)
                        (fn-record-generation record))))
   :hints (("Goal" :in-theory (enable fn-store-event-kind
                                      fn-store-event-sequence
                                      fn-store-event-txid
                                      fn-store-event-generation)))))

; The hypothesis `(fn-record-p record)' is the arm of `fn-replay-apply-record'
; this equation is about.  That function grew a retention arm (6ab2c783) and
; an identity arm (4bb7bb3d) on 2026-09-21 and this book has not certified
; since, so the unrestricted statement was never proved: on the retention arm
; the left side is `fn-replay-apply-retention-event' and the right side still
; names `fn-node-complete'.  Both callers below already carry the hypothesis.
(defthm fn-sn-replay-is-actual-live-durable-completion
  (implies (and (fn-record-p record)
                (fn-replay-advance-okp node (fn-record-txid record))
                (fn-node-pending-matchesp
                 (fn-sn-prepare-node node record)
                 (fn-record-txid record) (fn-record-generation record)))
           (equal (fn-replay-apply-record node record)
                  (fn-node-complete (fn-sn-prepare-node node record)
                                    (fn-record-txid record)
                                    (fn-record-generation record) :durable)))
  :hints (("Goal" :use ((:instance fn-replay-advance-reconstructs-recorded-txid
                                   (recorded-txid (fn-record-txid record)))))))

; unreachable-in-composition: fn-sn-fence-node and fn-sn-resolve-node have
; no host caller (see store-node.lisp).  The two correspondence theorems below
; are retained as documentation of the in-process resolution primitives; the
; host-relevant statement of the same fact is fn-snt-pending-linkp in
; store-node-traces.lisp, which relates the pending node to replay.
(defthm fn-sn-indeterminate-committed-resolution-equals-durable
  (implies (fn-node-pending-matchesp node (fn-record-txid record)
                                         (fn-record-generation record))
           (equal (fn-sn-resolve-node (fn-sn-fence-node node record) record t)
                  (fn-node-complete node (fn-record-txid record)
                                    (fn-record-generation record) :durable)))
  :hints (("Goal" :in-theory (enable fn-node-complete fn-node-recover
                                      fn-node-statep fn-statep fn-snx-core-definitions))))

(defthm fn-sn-indeterminate-absent-resolution-equals-abort
  (implies (fn-node-pending-matchesp node (fn-record-txid record)
                                         (fn-record-generation record))
           (equal (fn-sn-resolve-node (fn-sn-fence-node node record) record nil)
                  (fn-node-complete node (fn-record-txid record)
                                    (fn-record-generation record) :aborted)))
  :hints (("Goal" :in-theory (enable fn-node-complete fn-node-recover
                                      fn-node-statep fn-statep fn-snx-core-definitions))))

(defthm fn-sn-file-steps-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-file-step files operation result))
         (fn-sf-successes files))
  :hints (("Goal" :in-theory (enable fn-sf-start-frontier
    fn-sf-frontier-file-result fn-sf-frontier-replace-result
    fn-sf-frontier-dir-result fn-sf-record-file-result
    fn-sf-record-link-result fn-sf-record-dir-result fn-sf-recovery-barrier))))

(defthm fn-sn-io-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-io s operation result)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal" :in-theory (disable fn-sn-file-step ))))

(defthm fn-sn-prepare-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-prepare s record)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal" :in-theory (enable fn-sf-prepare-record))))

(defthm fn-sn-crash-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files
                          (fn-sn-crash s frontier-choice record-choice)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal" :in-theory (enable fn-sf-crash))))

(defthm fn-sn-recovery-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-recover s)))
         (fn-sf-successes (fn-sn-files s))))

; The composed crash is exactly the kernel crash on the file component with
; the configuration retained and the live node discarded.
(defthm fn-sn-crash-files-are-kernel-crash
  (implies (and (fn-sn-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (and (equal (fn-sn-files (fn-sn-crash s frontier-choice record-choice))
                       (fn-sf-crash (fn-sn-files s) frontier-choice record-choice))
                (equal (fn-sn-groups (fn-sn-crash s frontier-choice record-choice))
                       (fn-sn-groups s))
                (equal (fn-sn-capacity (fn-sn-crash s frontier-choice record-choice))
                       (fn-sn-capacity s))))
  :hints (("Goal" :in-theory (e/d (fn-sn-crash fn-sn-update )
                                  (fn-sn-statep fn-sf-crash fn-sf-crash-choicep)))))

(defthm fn-sn-prepare-installs-bound-candidate
  (implies (not (equal (fn-sn-prepare s record) s))
           (and (fn-sn-record-bindsp (fn-sn-node (fn-sn-prepare s record)) record)
                (equal (fn-sf-record-candidate
                        (fn-sn-files (fn-sn-prepare s record))) record)
                (equal (fn-record-sequence record)
                       (len (fn-sf-records (fn-sn-files s))))
                (equal (fn-record-generation record) (fn-record-txid record))
                (equal (1+ (fn-record-txid record))
                       (fn-sf-frontier (fn-sn-files s)))))
  :hints (("Goal" :in-theory (e/d (fn-sf-prepare-record)
                                  (fn-sn-record-bindsp fn-sn-prepare-node)))))

; Replay concatenation is a semantic composition theorem, not an assumption
; that a live node happens to equal a freshly replayed node.
(defthm fn-sn-replay-loop-append
  (implies (true-listp prefix)
           (equal (fn-replay-loop node (append prefix suffix) sequence)
                  (let ((first (fn-replay-loop node prefix sequence)))
                    (if (equal (fn-replay-result-kind first) :ok)
                        (fn-replay-loop (fn-replay-result-node first) suffix
                                         (fn-replay-result-sequence first))
                      first))))
  :hints (("Goal" :induct (fn-replay-loop node prefix sequence)
           :in-theory (e/d (fn-replay-loop)
                            (fn-replay-apply-record)))))

(defthm fn-sn-replay-singleton-is-live-completion
  (implies (and (fn-node-statep node)
                (fn-record-p record)
                (equal (fn-record-sequence record) sequence)
                (fn-replay-advance-okp node (fn-record-txid record))
                (fn-node-pending-matchesp
                 (fn-sn-prepare-node node record)
                 (fn-record-txid record) (fn-record-generation record)))
           (equal (fn-replay-loop node (list record) sequence)
                  (fn-replay-ok
                   (fn-node-complete (fn-sn-prepare-node node record)
                                     (fn-record-txid record)
                                     (fn-record-generation record) :durable)
                   (1+ sequence))))
  :hints (("Goal" :use fn-sn-replay-is-actual-live-durable-completion
           :in-theory (e/d (fn-replay-loop)
                            (fn-replay-apply-record fn-sn-prepare-node
                             fn-node-pending-matchesp)))))

; Starting from any successfully replayed prefix, extending the history by one
; admitted record yields exactly the live durable node, including allocator
; gaps reconstructed by fn-replay-advance-txid.
(defthm fn-sn-extended-history-equals-live-completion
  (let ((base (fn-replay-result-node (fn-replay groups capacity history)))
        (sequence (fn-replay-result-sequence (fn-replay groups capacity history))))
    (implies
     (and (true-listp history)
          (fn-replay-okp (fn-replay groups capacity history))
          (fn-record-p record)
          (equal (fn-record-sequence record) sequence)
          (fn-replay-advance-okp base (fn-record-txid record))
          (fn-node-pending-matchesp
           (fn-sn-prepare-node base record)
           (fn-record-txid record) (fn-record-generation record)))
     (equal (fn-replay groups capacity (append history (list record)))
            (fn-replay-ok
             (fn-node-complete (fn-sn-prepare-node base record)
                               (fn-record-txid record)
                               (fn-record-generation record) :durable)
             (1+ sequence)))))
  :hints (("Goal" :in-theory (e/d (fn-replay)
                                  (fn-replay-loop fn-replay-apply-record
                                   fn-sn-prepare-node
                                   fn-node-pending-matchesp)))))

; Mixed-trace semantic preparation and frontier foundation.
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable fn-node-statep fn-sf-statep fn-record-p
                           fn-node-prepare fn-node-complete fn-node-recover
                           fn-replay-advance-txid fn-replay fn-replay-loop
                           fn-sf-replay-node fn-sn-prepare-node
                           fn-retain-statep fn-node-initial-state)))

; Constructor-of-accessors for the two core records this book rebuilds
; (fn-replay-advance-txid rebuilds the acceptance state and the node).  The
; core records are opaque; these open them once, here, under their shapes.
(defthm fn-snt-node-reconstruct
  (implies (fn-node-state-shapep node)
           (equal (fn-node-make-state (fn-node-acceptance node)
                    (fn-node-retention node) (fn-node-stage node)
                    (fn-node-bindings node)) node))
  :hints (("Goal" :in-theory (enable len fn-node-state-shapep fn-node-make-state
                                     fn-node-acceptance fn-node-retention
                                     fn-node-stage fn-node-bindings)
           :expand ((len node) (len (cdr node)) (len (cddr node))
                    (len (cdddr node)) (len (cddddr node)))
           :do-not-induct t)))
(defthm fn-snt-acceptance-reconstruct
  (implies (fn-state-shapep a)
           (equal (fn-make-state (fn-state-groups a) (fn-state-nexts a)
                    (fn-state-articles a) (fn-state-next-txid a)
                    (fn-state-pending a) (fn-state-fenced a)) a))
  :hints (("Goal" :in-theory (enable len fn-state-shapep fn-make-state
                                     fn-state-groups fn-state-nexts
                                     fn-state-articles fn-state-next-txid
                                     fn-state-pending fn-state-fenced)
           :expand ((len a) (len (cdr a)) (len (cddr a))
                    (len (cdddr a)) (len (cddddr a))
                    (len (cdr (cddddr a))) (len (cddr (cddddr a))))
           :do-not-induct t)))

(defthm fn-snt-valid-node-is-consp
  (implies (fn-node-statep node) (consp node))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-node-statep fn-node-state-shapep))))
(defthm fn-snt-advanced-node-is-consp
  (implies (fn-node-statep node)
           (consp (fn-replay-advance-txid node frontier)))
  :hints (("Goal" :use ((:instance fn-replay-advance-preserves-node-statep
                                    (recorded-txid frontier))))))

; Raising an already recovered idle frontier is compositional and changes no
; semantic content.  These facts cover unused reservations and allocator gaps.
(defthm fn-snt-advance-is-idle
  (implies (fn-replay-advance-okp node frontier)
           (and (equal (fn-node-stage (fn-replay-advance-txid node frontier)) nil)
                (equal (fn-state-pending (fn-node-acceptance
                        (fn-replay-advance-txid node frontier))) nil)
                (equal (fn-state-fenced (fn-node-acceptance
                        (fn-replay-advance-txid node frontier))) nil)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-snt-advance-at-current-is-identity
  (implies (and (fn-replay-advance-okp node frontier)
                (equal (fn-state-next-txid (fn-node-acceptance node)) frontier))
           (equal (fn-replay-advance-txid node frontier) node))
  :hints (("Goal" :use (fn-snt-node-reconstruct
                                (:instance fn-snt-acceptance-reconstruct
                                 (a (fn-node-acceptance node))))
           :in-theory (enable fn-replay-advance-txid
                               fn-node-statep fn-statep fn-snx-core-definitions))))

(defthm fn-snt-advance-twice
  (implies (and (fn-replay-advance-okp node first)
                (natp second) (<= first second))
           (equal (fn-replay-advance-txid
                   (fn-replay-advance-txid node first) second)
                  (fn-replay-advance-txid node second)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid
                                      fn-node-statep fn-statep fn-snx-core-definitions))))

(local (in-theory (disable  fn-state-next-txid
                             )))

(defthm fn-snt-history-recoverable-monotone
  (implies (and (fn-sf-history-recoverablep groups capacity records first)
                (natp second) (<= first second))
           (fn-sf-history-recoverablep groups capacity records second))
  :hints (("Goal" :in-theory (enable fn-sf-replay-node))))

(defthm fn-snt-replayed-node-idle-and-frontier
  (implies (fn-sf-history-recoverablep groups capacity records frontier)
           (let ((node (fn-sf-replay-node groups capacity records frontier)))
             (and (fn-node-statep node)
                  (null (fn-node-stage node))
                  (null (fn-state-pending (fn-node-acceptance node)))
                  (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                  (equal (fn-state-next-txid (fn-node-acceptance node)) frontier))))
  :hints (("Goal" :in-theory (enable fn-sf-replay-node))))

(defthm fn-snt-advance-replayed-node
  (implies (and (fn-sf-history-recoverablep groups capacity records first)
                (natp second) (<= first second))
           (equal (fn-replay-advance-txid
                   (fn-sf-replay-node groups capacity records first) second)
                  (fn-sf-replay-node groups capacity records second)))
  :hints (("Goal" :in-theory (enable fn-sf-replay-node))))

(defthm fn-snt-successful-replay-sequence
  (implies (and (natp sequence)
                (equal (fn-replay-result-kind
                        (fn-replay-loop node records sequence)) :ok))
           (equal (fn-replay-result-sequence
                   (fn-replay-loop node records sequence))
                  (+ sequence (len records))))
  :hints (("Goal" :induct (fn-replay-loop node records sequence)
           :in-theory (e/d (fn-replay-loop)
                            (fn-replay-apply-record)))))

(defthm fn-snt-successful-replay-history-length
  (implies (fn-replay-okp (fn-replay groups capacity records))
           (equal (fn-replay-result-sequence (fn-replay groups capacity records))
                  (len records)))
  :hints (("Goal" :use ((:instance fn-snt-successful-replay-sequence
                         (node (fn-node-initial-state groups capacity))
                         (sequence 0)))
           :in-theory (enable fn-replay))))

;; The two prepared-* lemmas below step the node through prepare and
;; complete.  Each step's body tests `fn-statep' of the acceptance it is
;; handed; this field fact answers that test with the whole-node recognizer
;; closed.  Opening `fn-node-statep', `fn-statep' and the core definitions
;; instead rewrote the full recognizer in every case to prove facts about one
;; or two fields (29 s and 60 s on the 2026-09-23 seam run,
;; planning/evidence/store-cluster-cost-2026-09-23.md).
(local
 (defthm fn-snx-node-state-acceptance-is-state
   (implies (fn-node-statep s) (fn-statep (fn-node-acceptance s)))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(defthm fn-snt-prepared-abort-is-frontier-advance
  (implies (and (fn-replay-advance-okp node (fn-record-txid record))
                (fn-node-pending-matchesp (fn-sn-prepare-node node record)
                  (fn-record-txid record) (fn-record-generation record)))
           (equal (fn-node-complete (fn-sn-prepare-node node record)
                    (fn-record-txid record) (fn-record-generation record) :aborted)
                  (fn-replay-advance-txid node (1+ (fn-record-txid record)))))
  :hints (("Goal" :use ((:instance fn-snx-node-state-acceptance-is-state
                         (s (fn-sn-prepare-node node record)))
                        (:instance fn-sn-prepare-node-preserves-state))
           :in-theory (e/d (fn-sn-prepare-node fn-node-prepare fn-node-complete
                            fn-replay-advance-txid fn-accept-prepare
                            fn-accept-complete fn-clear-pending
                            fn-pending-matchesp)
                           (fn-node-statep fn-statep fn-retain-admissiblep
                            fn-retain-admit fn-selection-validp
                            fn-record-record-vocabulary)))))

(defthm fn-snt-prepared-durable-is-idle-at-successor
  (implies (and (fn-replay-advance-okp node (fn-record-txid record))
                (fn-node-pending-matchesp (fn-sn-prepare-node node record)
                  (fn-record-txid record) (fn-record-generation record)))
           (let ((done (fn-node-complete (fn-sn-prepare-node node record)
                         (fn-record-txid record) (fn-record-generation record) :durable)))
             (and (fn-node-statep done)
                  (null (fn-node-stage done))
                  (null (fn-state-pending (fn-node-acceptance done)))
                  (equal (fn-state-fenced (fn-node-acceptance done)) nil)
                  (equal (fn-state-next-txid (fn-node-acceptance done))
                         (1+ (fn-record-txid record))))))
  :hints (("Goal" :use ((:instance fn-node-complete-preserves-state
                        (s (fn-sn-prepare-node node record))
                        (txid (fn-record-txid record))
                        (generation (fn-record-generation record))
                        (completion-status :durable))
                 (:instance fn-snx-node-state-acceptance-is-state
                            (s (fn-sn-prepare-node node record)))
                 (:instance fn-sn-prepare-node-preserves-state))
           :in-theory (e/d (fn-sn-prepare-node fn-node-prepare fn-node-complete
                            fn-replay-advance-txid fn-accept-prepare
                            fn-accept-complete fn-install-pending
                            fn-pending-matchesp)
                           (fn-node-statep fn-statep fn-retain-admissiblep
                            fn-retain-admit fn-selection-validp
                            fn-record-record-vocabulary)))))

;------------------------------------------------------------------------------
; The carried statement index (decision D21)
;
; fn-sn-indexedp is fn-sn-statep plus the agreement between the carried index
; and the store's lace projection.  It is the guard of nothing -- putting it
; in fn-sn-statep would re-derive the index, and so re-verify every signature
; in the store, inside the guard the host checks on every call (D20, D3).
; What makes it usable is this chain: it holds at fn-sn-initial and every
; transition preserves it, so it holds of every reachable state, and
; fn-sn-statement-lookup-is-the-lace-lookup below can hypothesise it.
;
; Which of these are proof events and which are not, said plainly:
; fn-sn-finish-preserves-indexedp is the one that does work -- the store grows
; there and the keystone underneath it is fn-stx-index-invariant-preserved-by-
; accept (books/stx-index.lisp), whose hypothesis is discharged by
; fn-stx-durable-completion-is-an-acceptance (books/stx-lace.lisp).  The
; prepare/io ones ride on a store-unchanged equation.  The recover, crash and
; set-keyring ones hold because those three transitions RECOMPUTE, so their
; conclusion is the recomputation restated; they are named -by-recomputation
; and are not offered as proof events.  They are still obligations: what they
; rule out is a transition that reaches a new store carrying the old index.

(local (in-theory (enable fn-sn-indexedp fn-sn-set-keyring fn-sn-accepted-delta
                          fn-sn-statement-lookup fn-sn-equivocatorp)))

; The store-unchanged equations the carrying transitions need.  Each is an
; unfolding of one transition -- named -unfolds, per the assurance rule that
; forbids offering a definition restated as a proof event.
(defthm fn-sn-prepare-node-keeps-the-store-unfolds
  (implies (fn-node-statep node)
           (equal (fn-stx-store (fn-sn-prepare-node node record))
                  (fn-stx-store node)))
  :hints (("Goal" :in-theory (e/d (fn-stx-store fn-sn-prepare-node)
                                  (fn-node-prepare fn-replay-advance-txid))
           :use ((:instance fn-replay-advance-preserves-node-statep
                            (node node) (recorded-txid (fn-record-txid record)))
                 (:instance fn-node-prepare-does-not-publish-or-commit-retention
                            (s (fn-replay-advance-txid node (fn-record-txid record)))
                            (generation (fn-record-generation record))
                            (msgid (fn-record-msgid record))
                            (payload (fn-record-payload record))
                            (groups (fn-record-groups record))
                            (obligation-id (fn-record-obligation-id record))
                            (subject (fn-record-content-subject record))
                            (evidence (fn-record-release-evidence record))
                            (charge (fn-record-charge record)))))))

(defthm fn-sn-initial-node-has-an-empty-store-unfolds
  (equal (fn-stx-store (fn-node-initial-state groups capacity)) nil)
  :hints (("Goal" :in-theory (enable fn-stx-store fn-node-initial-state
                                     fn-initial-state))))

(defthm fn-sn-index-of-an-empty-store-unfolds
  (equal (fn-stx-index-of-store nil keyring) (fn-stx-index-empty))
  :hints (("Goal" :in-theory (enable fn-stx-index-of-store))))

; Every reachable state is indexed: the base case.
(defthm fn-sn-initial-is-indexed
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups)
                (natp capacity))
           (fn-sn-indexedp (fn-sn-initial groups capacity)))
  :hints (("Goal" :in-theory (e/d (fn-stx-index-invariantp)
                                  (fn-node-initial-state fn-stx-index-of-store))
           :use ((:instance fn-sn-initial-is-state)))))

(defthm fn-sn-prepare-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-stx-index-invariantp)
                                  (fn-sn-prepare-node fn-node-statep
                                   fn-stx-index-of-store fn-stx-store
                                   fn-sf-prepare-record))
           :use ((:instance fn-sn-prepare-preserves-state)
                 (:instance fn-sn-prepare-node-keeps-the-store-unfolds
                            (node (fn-sn-node s)))))))

(defthm fn-sn-io-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-io s operation result)))
  :hints (("Goal" :in-theory (e/d (fn-stx-index-invariantp)
                                  (fn-sn-file-step fn-node-statep
                                   fn-stx-index-of-store fn-stx-store))
           :use ((:instance fn-sn-io-preserves-state)))))

; THE ONE THAT DOES WORK.  The store grows here, by the one article
; fn-install-pending conses, and the index grows by the delta of exactly that
; article -- at most one cons, never a walk.  The subject is fn-sn-finish,
; which host/store-node-host.lisp line 402 (fn-store-sn-finish) calls.
; The two arms of `fn-sn-finish' that are NOT an acceptance publish no
; article, so the index the state carries is still the index of its store.
; `fn-replay-advance-txid' rebuilds the acceptance record around the same
; article list; `fn-replay-node-with-retention' replaces the retention half
; and keeps the acceptance record whole; and the identity-neutral step is two
; advances.  Each is stated over `fn-stx-store', which this proof holds
; closed, so the equation reaches the invariant without opening the store.
(local
 (defthm fn-sn-store-of-node-with-retention
   (equal (fn-stx-store (fn-replay-node-with-retention node retention))
          (fn-stx-store node))
   :hints (("Goal" :in-theory (enable fn-stx-store
                                      fn-replay-node-with-retention)))))

(local
 (defthm fn-sn-store-of-advance-txid
   (equal (fn-stx-store (fn-replay-advance-txid node recorded-txid))
          (fn-stx-store node))
   :hints (("Goal" :in-theory (enable fn-stx-store fn-replay-advance-txid)))))

(local
 (defthm fn-sn-store-of-complete-retention
   (equal (fn-stx-store (fn-replay-complete-retention node retention event))
          (fn-stx-store node))
   :hints (("Goal" :in-theory (e/d (fn-replay-complete-retention)
                                   (fn-stx-store fn-replay-advance-txid
                                    fn-replay-node-with-retention))))))

(local
 (defthm fn-sn-store-of-retention-event
   (implies (fn-replay-apply-retention-event node event)
            (equal (fn-stx-store (fn-replay-apply-retention-event node event))
                   (fn-stx-store node)))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-retention-event)
                                   (fn-stx-store fn-replay-advance-txid
                                    fn-replay-complete-retention
                                    fn-record-shape-vocabulary
                                    fn-store-retention-event-p
                                    fn-retain-admissiblep fn-retain-admit
                                    fn-retain-release))))))

(local
 (defthm fn-sn-store-of-identity-neutral
   (implies (fn-replay-apply-identity-neutral node event)
            (equal (fn-stx-store (fn-replay-apply-identity-neutral node event))
                   (fn-stx-store node)))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-identity-neutral)
                                   (fn-stx-store fn-replay-advance-txid
                                    fn-record-shape-vocabulary))))))

; And the composite identity arm whose event binds nothing: its delta is the
; delta of no octets, which is empty, and adding an empty delta is the
; identity on the index.
(local
 (defthm fn-sn-no-delta-from-no-octets
   (equal (fn-stx-delta nil keyring) nil)
   :hints (("Goal" :in-theory (enable fn-stx-delta)))))

(local
 (defthm fn-sn-index-add-of-an-empty-delta
   (equal (fn-stx-index-add index nil) index)
   :hints (("Goal" :in-theory (enable fn-stx-index-add)))))

; The composite acceptance arm replays a decoded article.  Its prepared
; article must be exactly the head added to the Store and exactly the source
; of the carried index delta; the following local facts state those two
; equations without opening the record codec in the final arm dispatch.
(local
 (defthm fn-sn-cbor-octets-are-octets
   (implies (fn-cbor-octet-listp xs) (fn-octet-listp xs))
   :hints (("Goal" :induct (fn-cbor-octet-listp xs)
            :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp
                               fn-octet-listp fn-octetp)))))

(local
 (defthm fn-sn-record-payload-is-octets
   (implies (fn-record-p record)
            (fn-octet-listp (fn-record-payload record)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp
                                      fn-record-shape-vocabulary)))))

(local
 (defthm fn-sn-composite-kind-disjoint
   (implies (fn-stxa-p record)
            (and (not (fn-store-retention-event-p record))
                 (not (fn-stxe-p record))
                 (not (fn-stxk-p record))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-stxa-p fn-stxa-shapep fn-stxa-keyring-generation
                             fn-stxe-p fn-stxe-shapep fn-stxe-msgid
                             fn-stxk-p fn-stxk-shapep
                             fn-store-retention-event-p fn-record-msgidp)
                            (fn-stxe-bounded-octetsp
                             fn-record-metadata-bytes-p))))))

(local
 (defthm fn-sn-composite-idle-has-no-pending
   (implies (and (fn-node-statep node) (null (fn-node-stage node)))
            (null (fn-state-pending (fn-node-acceptance node))))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(local
 (defthm fn-sn-composite-stage-of-advance
   (equal (fn-node-stage (fn-replay-advance-txid node txid))
          (fn-node-stage node))
   :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

(local
 (defthm fn-sn-composite-is-not-topic-event
   (implies (fn-stxa-p event)
            (not (fn-th-topic-eventp event)))
   :hints (("Goal" :in-theory
            (e/d (fn-stxa-p fn-stxa-shapep
                  fn-th-topic-eventp fn-th-local-admin-eventp)
                 (fn-stxe-bounded-octetsp fn-th-auth-ref-p
                  fn-th-source-id-p fn-th-parents-p))))))

(local
 (defthm fn-sn-composite-replay-article-typed
   (implies (and (fn-stxa-p event)
                 (consp (fn-replay-apply-record node event)))
            (fn-record-p (fn-replay-composite-record event)))
   :hints (("Goal" :in-theory (e/d (fn-replay-apply-record)
                                   (fn-stxa-p fn-stxe-p fn-stxk-p
                                    fn-th-topic-eventp
                                    fn-store-retention-event-p
                                    fn-replay-advance-txid fn-node-prepare
                                    fn-node-complete fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

(local
 (defthm fn-sn-composite-replay-installs-decoded-payload
   (implies (and (fn-node-statep node)
                 (null (fn-node-stage node))
                 (fn-stxa-p event)
                 (consp (fn-replay-apply-record node event)))
            (equal (fn-article-payload
                    (car (fn-stx-store (fn-replay-apply-record node event))))
                   (fn-record-payload (fn-replay-composite-record event))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-replay-apply-record fn-node-complete
                             fn-accept-complete fn-install-pending
                             fn-article-from-pending fn-node-prepare
                             fn-accept-prepare fn-stx-store fn-node-statep
                             fn-node-pending-matchesp fn-pending-matchesp)
                            (fn-statep fn-record-shape-vocabulary
                             fn-record-record-vocabulary fn-stxa-p fn-stxe-p
                             fn-stxk-p fn-store-retention-event-p
                             fn-replay-composite-record
                             fn-replay-advance-txid))))))

(local
 (defthm fn-sn-composite-replay-installs-one-article
   (implies (and (fn-node-statep node)
                 (null (fn-node-stage node))
                 (fn-stxa-p event)
                 (consp (fn-replay-apply-record node event)))
            (and (consp (fn-stx-store (fn-replay-apply-record node event)))
                 (equal (cdr (fn-stx-store (fn-replay-apply-record node event)))
                        (fn-stx-store node))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-replay-apply-record fn-node-complete
                             fn-accept-complete fn-install-pending
                             fn-article-from-pending fn-node-prepare
                             fn-accept-prepare fn-stx-store fn-node-statep
                             fn-node-pending-matchesp fn-pending-matchesp)
                            (fn-statep fn-record-shape-vocabulary
                             fn-record-record-vocabulary fn-stxa-p fn-stxe-p
                             fn-stxk-p fn-store-retention-event-p
                             fn-replay-composite-record
                             fn-replay-advance-txid))))))

(local
 (defthm fn-sn-composite-delta-of-typed-article
   (implies (and (fn-prin-keyringp keyring)
                 (fn-record-p (fn-replay-composite-record event)))
            (equal (fn-sn-composite-delta event keyring)
                   (fn-stx-delta
                    (fn-record-payload (fn-replay-composite-record event))
                    keyring)))
   :hints (("Goal" :in-theory (enable fn-sn-composite-delta)))))

(local
 (defthm fn-sn-composite-replay-preserves-index-invariant
   (implies (and (fn-node-statep node)
                 (null (fn-node-stage node))
                 (fn-stxa-p event)
                 (consp (fn-replay-apply-record node event))
                 (fn-prin-keyringp keyring)
                 (fn-stx-index-invariantp index node keyring))
            (fn-stx-index-invariantp
             (fn-stx-index-add index (fn-sn-composite-delta event keyring))
             (fn-replay-apply-record node event) keyring))
   :hints (("Goal" :in-theory (e/d (fn-stx-index-invariantp
                                    fn-stx-index-of-store)
                                   (fn-stx-index-add fn-stx-store fn-stx-delta
                                    fn-sn-composite-delta
                                    fn-replay-composite-record
                                    fn-replay-apply-record fn-stxa-p
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

(local
 (defthm fn-sn-composite-completion-is-idle
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-stxa-p (fn-sn-completion-record s)))
            (null (fn-node-stage (fn-sn-node s))))
   :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp
                                    fn-replay-apply-record)
                                   (fn-sn-statep fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-sn-completion-record
                                    fn-replay-composite-record
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

(local
 (defthm fn-sn-composite-completion-has-replay
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-stxa-p (fn-sn-completion-record s)))
            (consp (fn-replay-apply-record
                    (fn-sn-node s) (fn-sn-completion-record s))))
   :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp)
                                   (fn-sn-statep fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-sn-completion-record
                                    fn-replay-apply-record fn-replay-identity-step
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

(local
 (defthm fn-sn-composite-completion-is-bound
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-stxa-p (fn-sn-completion-record s)))
            (fn-stxa-bindsp (fn-sn-completion-record s)))
   :hints (("Goal" :in-theory (e/d (fn-sn-completion-enabledp
                                    fn-replay-apply-record
                                    fn-replay-composite-record)
                                   (fn-sn-statep fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-sn-completion-record fn-stxa-bindsp
                                    fn-replay-identity-step
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

(local
 (defthmd fn-sn-finish-composite-arm-fields
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-stxa-p (fn-sn-completion-record s)))
            (and (equal (fn-sn-index (fn-sn-finish s))
                        (fn-stx-index-add
                         (fn-sn-index s)
                         (fn-sn-composite-delta (fn-sn-completion-record s)
                                                (fn-sn-keyring s))))
                 (equal (fn-sn-node (fn-sn-finish s))
                        (fn-replay-apply-record
                         (fn-sn-node s) (fn-sn-completion-record s)))
                 (equal (fn-sn-keyring (fn-sn-finish s))
                        (fn-sn-keyring s))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-finish-identity)
                                   (fn-sn-completion-enabledp fn-sn-statep
                                    fn-sn-completion-record
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-replay-apply-record fn-replay-identity-step
                                    fn-sn-identity-context fn-sf-core-completion
                                    fn-sf-emit-success fn-sn-composite-delta
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))
;; fn-sn-finish-preserves-indexedp, one arm at a time.  The theorem below
;; dispatches on the finish arm; with `fn-sn-finish', `fn-sn-completion-
;; enabledp' and `fn-sn-record-bindsp' open it split 5249 ways at Goal'' on
;; the record codec, the replay steps and the store-transaction recognizers
;; (118.8 s, 50.8 million steps, 13 734 subgoals on the 2026-09-23 seam run,
;; planning/evidence/store-cluster-cost-2026-09-23.md).  What it needs from
;; each arm is three fields of the result, stated here once per arm with the
;; replay steps and the recognizers closed; the theorem is then a `:cases' on
;; the arm; the disabled branch is `fn-sn-finish-disabled-is-no-op' above.
;; They are enabled only in that theorem's hint.
(local
 (defthmd fn-sn-finish-retention-arm-keeps-the-store-and-index
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-store-retention-event-p (fn-sn-completion-record s)))
            (and (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                        (fn-stx-store (fn-sn-node s)))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp)
                                   (fn-sn-statep fn-stx-store
                                    fn-replay-apply-retention-event
                                    fn-replay-apply-record
                                    fn-replay-identity-step fn-sn-identity-context
                                    fn-sf-core-completion fn-sf-emit-success
                                    fn-sn-completion-record fn-sn-record-bindsp
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-node-complete fn-sn-accepted-delta
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))
(local
 (defthmd fn-sn-finish-identity-arm-keeps-the-store-and-index
   (implies (and (fn-sn-completion-enabledp s)
                 (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                 (or (fn-stxe-p (fn-sn-completion-record s))
                     (fn-stxk-p (fn-sn-completion-record s)))
                 (not (fn-stxa-p (fn-sn-completion-record s))))
            (and (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                        (fn-stx-store (fn-sn-node s)))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp)
                                   (fn-sn-statep fn-stx-store
                                    fn-replay-apply-retention-event
                                    fn-replay-apply-identity-neutral
                                    fn-replay-composite-record
                                    fn-replay-identity-step fn-sn-identity-context
                                    fn-sf-core-completion fn-sf-emit-success
                                    fn-sn-completion-record fn-sn-record-bindsp
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-node-complete fn-sn-accepted-delta
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

; Consumer records are a distinct five-field Store kind.  Their node replay
; only advances txid; the carried consumer projection changes separately.
(local
 (defthm fn-snx-cpe-no-other-event
   (implies (fn-cpe-eventp event)
            (and (not (fn-store-retention-event-p event))
                 (not (fn-stxe-p event))
                 (not (fn-stxk-p event))
                 (not (fn-stxa-p event))))
   :hints (("Goal" :in-theory (enable fn-cpe-eventp
                                      fn-store-retention-event-p
                                      fn-stxe-shapep fn-stxk-shapep
                                      fn-stxa-shapep)))))
(local
 (defthm fn-snx-identity-neutral-keeps-articles
   (implies (consp (fn-replay-apply-identity-neutral node event))
            (equal (fn-state-articles
                    (fn-node-acceptance
                     (fn-replay-apply-identity-neutral node event)))
                   (fn-state-articles (fn-node-acceptance node))))
   :hints (("Goal" :in-theory (enable fn-replay-apply-identity-neutral)))))
(local
 (defthm fn-snx-consumer-completion-node-idle-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-cpe-eventp (fn-sn-completion-record s)))
            (null (fn-node-stage (fn-sn-node s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-replay-apply-record)
                 (fn-cpe-eventp fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-stxa-p
                  fn-replay-apply-identity-neutral))))))
(local
 (defthm fn-snx-consumer-completion-replay-non-nil-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-cpe-eventp (fn-sn-completion-record s)))
            (consp (fn-replay-apply-identity-neutral
                    (fn-sn-node s) (fn-sn-completion-record s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-replay-apply-record)
                 (fn-cpe-eventp fn-store-retention-event-p
                  fn-stxe-p fn-stxk-p fn-stxa-p
                  fn-replay-apply-identity-neutral))))))
(local
 (defthmd fn-sn-finish-consumer-arm-keeps-the-store-and-index
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-cpe-eventp (fn-sn-completion-record s)))
            (and (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                        (fn-stx-store (fn-sn-node s)))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-finish fn-stx-store fn-replay-apply-record)
                 (fn-sn-completion-enabledp fn-sn-completion-record
                  fn-cpe-eventp
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                  fn-replay-apply-identity-neutral
                  fn-replay-apply-retention-event fn-sf-core-completion
                  fn-sf-emit-success fn-record-shape-vocabulary))
            :use (fn-snx-consumer-completion-node-idle-by-definition
                  fn-snx-consumer-completion-replay-non-nil-by-definition)))))
(local
 (defthm fn-snx-topic-no-other-event
   (implies (fn-th-topic-eventp event)
            (and (not (fn-store-retention-event-p event))
                 (not (fn-stxe-p event))
                 (not (fn-stxk-p event))
                 (not (fn-stxa-p event))
                 (not (fn-cpe-eventp event))))
   :hints (("Goal" :in-theory
            (enable fn-th-topic-eventp fn-th-local-admin-eventp
                    fn-store-retention-event-p fn-stxe-shapep
                    fn-stxk-shapep fn-stxa-shapep fn-cpe-eventp)))))
(local
 (defthm fn-snx-topic-completion-node-idle-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-th-topic-eventp (fn-sn-completion-record s)))
            (null (fn-node-stage (fn-sn-node s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-replay-apply-record)
                 (fn-th-topic-eventp fn-cpe-eventp
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                  fn-replay-apply-identity-neutral))))))
(local
 (defthm fn-snx-topic-completion-replay-non-nil-by-definition
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-th-topic-eventp (fn-sn-completion-record s)))
            (consp (fn-replay-apply-identity-neutral
                    (fn-sn-node s) (fn-sn-completion-record s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-completion-enabledp fn-replay-apply-record)
                 (fn-th-topic-eventp fn-cpe-eventp
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                  fn-replay-apply-identity-neutral))))))
(local
 (defthmd fn-sn-finish-topic-arm-keeps-the-store-and-index
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-th-topic-eventp (fn-sn-completion-record s)))
            (and (equal (fn-sn-index (fn-sn-finish s)) (fn-sn-index s))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-stx-store (fn-sn-node (fn-sn-finish s)))
                        (fn-stx-store (fn-sn-node s)))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-finish fn-stx-store fn-replay-apply-record)
                 (fn-sn-completion-enabledp fn-sn-completion-record
                  fn-th-topic-eventp fn-cpe-eventp
                  fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                  fn-replay-apply-identity-neutral
                  fn-replay-apply-retention-event fn-sf-core-completion
                  fn-sf-emit-success fn-record-shape-vocabulary)
            :use (fn-snx-topic-completion-node-idle-by-definition
                  fn-snx-topic-completion-replay-non-nil-by-definition))))))
(local
 (defthmd fn-sn-finish-acceptance-arm-fields
   (implies (and (fn-sn-completion-enabledp s)
                 (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                 (not (fn-stxe-p (fn-sn-completion-record s)))
                 (not (fn-stxk-p (fn-sn-completion-record s)))
                 (not (fn-stxa-p (fn-sn-completion-record s)))
                 (not (fn-cpe-eventp (fn-sn-completion-record s)))
                 (not (fn-th-topic-eventp (fn-sn-completion-record s))))
            (and (equal (fn-sn-index (fn-sn-finish s))
                        (fn-stx-index-add (fn-sn-index s)
                                          (fn-sn-accepted-delta s)))
                 (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
                 (equal (fn-sn-node (fn-sn-finish s))
                        (fn-node-complete
                         (fn-sn-node s)
                         (fn-record-txid (fn-sn-completion-record s))
                         (fn-record-generation (fn-sn-completion-record s))
                         :durable))
                 (fn-node-pending-matchesp
                  (fn-sn-node s)
                  (fn-record-txid (fn-sn-completion-record s))
                  (fn-record-generation (fn-sn-completion-record s)))))
   :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-completion-enabledp
                                    fn-sn-record-bindsp)
                                   (fn-sn-statep fn-stx-store
                                    fn-replay-apply-retention-event
                                    fn-replay-apply-record
                                    fn-replay-identity-step fn-sn-identity-context
                                    fn-sf-core-completion fn-sf-emit-success
                                    fn-sn-completion-record
                                    fn-node-pending-matchesp fn-sn-pending-record
                                    fn-store-retention-event-p
                                    fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-th-topic-eventp
                                    fn-node-complete fn-sn-accepted-delta
                                    fn-stx-index-add
                                    fn-record-shape-vocabulary
                                    fn-record-record-vocabulary))))))

(defthm fn-sn-finish-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-finish s)))
  :hints (("Goal"
           ; One case per arm of `fn-sn-finish'; each closes by its arm lemma
           ; above.  `fn-stx-index-invariantp' is opened so the two
           ; non-acceptance arms reduce to the store equations; the store, the
           ; index, the replay steps and the recognizers stay closed.
           :cases ((not (fn-sn-completion-enabledp s))
                   (and (fn-sn-completion-enabledp s)
                        (fn-store-retention-event-p (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (not (fn-store-retention-event-p
                              (fn-sn-completion-record s)))
                        (or (fn-stxe-p (fn-sn-completion-record s))
                            (fn-stxk-p (fn-sn-completion-record s)))
                        (not (fn-stxa-p (fn-sn-completion-record s))))
                   (and (fn-sn-completion-enabledp s)
                        (fn-stxa-p (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (fn-cpe-eventp (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (fn-th-topic-eventp (fn-sn-completion-record s)))
                   (and (fn-sn-completion-enabledp s)
                        (not (fn-store-retention-event-p
                              (fn-sn-completion-record s)))
                        (not (fn-stxe-p (fn-sn-completion-record s)))
                        (not (fn-stxk-p (fn-sn-completion-record s)))
                        (not (fn-stxa-p (fn-sn-completion-record s)))
                        (not (fn-cpe-eventp (fn-sn-completion-record s)))
                        (not (fn-th-topic-eventp (fn-sn-completion-record s)))))
           :in-theory (e/d (fn-stx-index-invariantp
                            fn-sn-finish-retention-arm-keeps-the-store-and-index
                            fn-sn-finish-identity-arm-keeps-the-store-and-index
                            fn-sn-finish-composite-arm-fields
                            fn-sn-finish-consumer-arm-keeps-the-store-and-index
                            fn-sn-finish-topic-arm-keeps-the-store-and-index
                            fn-sn-finish-acceptance-arm-fields)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-sn-completion-record fn-sn-record-bindsp
                            fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p fn-cpe-eventp
                            fn-th-topic-eventp
                            fn-replay-apply-record fn-replay-identity-step
                            fn-sn-identity-context
                            fn-sf-core-completion fn-sf-emit-success
                            fn-node-statep fn-node-complete
                            fn-stx-index-of-store fn-stx-store
                            fn-stx-index-add
                            fn-node-pending-matchesp
                            fn-record-shape-vocabulary
                            fn-record-record-vocabulary))
           :use ((:instance fn-sn-finish-preserves-state)
                 (:instance fn-sn-finish-disabled-is-no-op)
                 (:instance fn-sn-composite-completion-is-idle)
                 (:instance fn-sn-composite-completion-has-replay)
                 (:instance fn-sn-composite-replay-preserves-index-invariant
                            (node (fn-sn-node s))
                            (event (fn-sn-completion-record s))
                            (keyring (fn-sn-keyring s))
                            (index (fn-sn-index s)))
                 (:instance fn-stx-durable-completion-is-an-acceptance
                            (s (fn-sn-node s))
                            (txid (fn-record-txid (fn-sn-completion-record s)))
                            (generation (fn-record-generation
                                         (fn-sn-completion-record s))))
                 (:instance fn-stx-index-invariant-preserved-by-accept
                            (index (fn-sn-index s))
                            (node (fn-sn-node s))
                            (keyring (fn-sn-keyring s))
                            (next (fn-node-complete
                                   (fn-sn-node s)
                                   (fn-record-txid (fn-sn-completion-record s))
                                   (fn-record-generation
                                    (fn-sn-completion-record s))
                                   :durable))
                            (article (fn-article-from-pending
                                      (fn-state-pending
                                       (fn-node-acceptance (fn-sn-node s))))))))))

; -by-recomputation: a crash resets the node to the empty store, so the empty
; index is the recomputation and not a carried value.  Not a proof event; the
; obligation it discharges is that the crash does not keep the old index.
(defthm fn-sn-crash-preserves-indexedp-by-recomputation
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal" :in-theory (e/d (fn-stx-index-invariantp)
                                  (fn-sf-crash fn-node-statep
                                   fn-node-initial-state
                                   fn-stx-index-of-store fn-stx-store))
           :use ((:instance fn-sn-crash-preserves-state)))))

; -by-recomputation: recovery's node comes from a replay, not from a step of
; this machine, so its index is recomputed over the replayed store.
(defthm fn-sn-recover-preserves-indexedp-by-recomputation
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-recover s)))
  :hints (("Goal" :in-theory (e/d (fn-stx-index-invariantp)
                                  (fn-sf-replay-node fn-sf-recover
                                   fn-node-statep fn-stx-index-of-store
                                   fn-stx-store))
           :use ((:instance fn-sn-recover-preserves-state)))))

; -by-recomputation: the reconfiguration transition recomputes over the whole
; store, which is correct and is not a served path.
(defthm fn-sn-set-keyring-preserves-indexedp-by-recomputation
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-set-keyring s keyring)))
  :hints (("Goal" :in-theory (e/d (fn-stx-index-invariantp fn-sn-statep)
                                  (fn-sf-statep fn-node-statep
                                   fn-stx-index-of-store fn-stx-store)))))

; -----------------------------------------------------------------------------
; The served query, and what licenses it
;
; :rule-classes nil on purpose.  As a rewrite rule this would replace the
; cheap index query by the linear lace projection in every proof above, which
; is the direction the index exists to avoid.  It is cited with :use.
;
; The host line: host/store-node-host.lisp fn-store-sn-statement calls
; fn-sn-statement-lookup on (f-get-global 'fn-store-sn state), whose value is
; produced by fn-sn-initial and the transitions above and by nothing else.
(defthm fn-sn-statement-lookup-is-the-lace-lookup
  (implies (fn-sn-indexedp s)
           (equal (fn-sn-statement-lookup s id)
                  (fn-lace-lookup (fn-stx-lace (fn-sn-node s) (fn-sn-keyring s))
                                  id)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stx-index-agrees-with-lace
                                   (index (fn-sn-index s))
                                   (node (fn-sn-node s))
                                   (keyring (fn-sn-keyring s))))
           :in-theory (disable fn-stx-index-invariantp fn-stx-lace
                               fn-stx-index-lookup fn-stx-index-equivocatorp
                               fn-node-statep fn-sf-statep))))

(defthm fn-sn-equivocatorp-is-the-lace-equivocator
  (implies (fn-sn-indexedp s)
           (iff (fn-sn-equivocatorp s creator incarnation)
                (fn-lace-equivocatorp
                 (fn-stx-lace (fn-sn-node s) (fn-sn-keyring s))
                 creator incarnation)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stx-index-agrees-with-lace
                                   (index (fn-sn-index s))
                                   (node (fn-sn-node s))
                                   (keyring (fn-sn-keyring s))
                                   (p creator) (i incarnation)))
           :in-theory (disable fn-stx-index-invariantp fn-stx-lace
                               fn-stx-index-lookup fn-stx-index-equivocatorp
                               fn-node-statep fn-sf-statep))))

; -----------------------------------------------------------------------------
; Prefix recoverability (lane w11/bytestore-k2, packet 2).
;
; fn-sn-replay-loop-append already gives ok(whole) implies ok(prefix).  What
; it does not give -- and what blocked the first attempt to widen
; fn-snt-admissible-crash-image-is-recoverable (handoff w10/kernel-freedom
; s6) -- is that the PREFIX node is IDLE and its next txid is no higher than
; the frontier.  Those two are exactly fn-replay-advance-okp, which is the
; one thing fn-sf-history-recoverablep needs beyond a successful replay.
;
; The same lemmas answer the frontier arm of the recovery freedom (K2f): a
; history whose txids are all below a bound replays to a node whose next txid
; is at most that bound, so it is recoverable at the bound.
;
; Every conclusion below is spelled (equal x nil) and not (null x): the
; built-in NULL rule subsumes a (null ...) conclusion, so ACL2 declines to
; store the rewrite and the lemma silently does nothing.  Measured here --
; five "the previously added rule NULL subsumes" warnings and an induction
; that then could not discharge its own step.

; The one field type these proofs need.  It is BOTH a rewrite and a forward
; chaining rule, and the forms below that depend on it close fn-record-txid,
; for two measured reasons.  Forward chaining runs on a goal's hypotheses as
; they stand when the goal is created, and (fn-record-p (car records)) only
; appears once fn-sf-record-listp has been opened during that goal's
; simplification -- so the rule never fires on the goal that needs it, and
; the :use in the step lemma below is not belt and braces.  And the record
; vocabulary is open in this book, so an unclosed fn-record-txid has already
; become (cadr record) in the goal while the rule's left-hand side is stored
; in accessor vocabulary and no longer matches.
(local
 (defthm fn-snt-record-txid-is-a-natural
   (implies (fn-record-p record) (natp (fn-record-txid record)))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-txid
                                      fn-record-uint32p)))))

(local
 (defthm fn-snt-advance-off-gate-is-identity
   (implies (not (fn-replay-advance-okp node recorded-txid))
            (equal (fn-replay-advance-txid node recorded-txid) node))
   :hints (("Goal" :in-theory (enable fn-replay-advance-txid
                                      fn-replay-advance-okp)))))

; One replayed record, from an idle node.  The refusal cases are excluded by
; the hypothesis that the result IS a node: fn-replay-apply-record returns
; NIL for both of them.  The <= conclusion is the part that is not already in
; fn-snt-prepared-durable-is-idle-at-successor: the loop could only have
; taken this record if the node's next txid had not passed it.
(local
 (defthm fn-snt-apply-record-from-idle-is-idle-at-successor
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (fn-record-p record)
                 (fn-node-statep (fn-replay-apply-record node record)))
            (and (equal (fn-node-stage (fn-replay-apply-record node record)) nil)
                 (equal (fn-state-pending
                         (fn-node-acceptance
                          (fn-replay-apply-record node record))) nil)
                 (equal (fn-state-fenced
                         (fn-node-acceptance
                          (fn-replay-apply-record node record))) nil)
                 (equal (fn-state-next-txid
                         (fn-node-acceptance
                          (fn-replay-apply-record node record)))
                        (1+ (fn-record-txid record)))))
   :hints (("Goal"
            :use ((:instance fn-snt-prepared-durable-is-idle-at-successor)
                  (:instance fn-snt-record-txid-is-a-natural)
                  (:instance fn-replay-advance-reconstructs-recorded-txid
                             (recorded-txid (fn-record-txid record))))
            :in-theory (e/d (fn-replay-apply-record fn-replay-advance-okp
                             fn-sn-prepare-node)
                            (fn-replay-advance-txid fn-node-prepare
                             fn-node-complete fn-node-statep
                             fn-node-pending-matchesp
                             fn-snt-prepared-durable-is-idle-at-successor
                             fn-replay-advance-reconstructs-recorded-txid))))))

; The same step's arithmetic half, :linear and on its own: a :rewrite rule
; from a (<= a b) conclusion only fires on a literal (< b a) in the goal, and
; the induction below needs the fact as a linear assumption instead.  The
; loop could only have taken this record if the node's next txid had not
; passed it: fn-replay-advance-txid moves a node forward or not at all, and
; fn-replay-apply-record refuses unless the advanced node sits exactly at the
; record's txid.
(local
 (defthm fn-snt-apply-record-from-idle-needs-its-txid
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (fn-record-p record)
                 (fn-node-statep (fn-replay-apply-record node record)))
            (<= (fn-state-next-txid (fn-node-acceptance node))
                (fn-record-txid record)))
   :rule-classes :linear
   :hints (("Goal"
            :use ((:instance fn-snt-record-txid-is-a-natural)
                  (:instance fn-replay-advance-reconstructs-recorded-txid
                             (recorded-txid (fn-record-txid record))))
            :in-theory (e/d (fn-replay-apply-record fn-replay-advance-okp
                             fn-sn-prepare-node)
                            (fn-replay-advance-txid fn-node-prepare
                             fn-node-complete fn-node-statep
                             fn-node-pending-matchesp
                             fn-replay-advance-reconstructs-recorded-txid))))))

; A loop that answers :ok was handed a node: its very first test is
; (not (fn-node-statep node)), whose branch is a fault.  Forward chained,
; because the induction below needs it of the node the step produced before
; the step lemma can say anything about that node.
(local
 (defthm fn-snt-replay-loop-ok-was-given-a-node
   (implies (equal (fn-replay-result-kind
                    (fn-replay-loop node records sequence)) :ok)
            (fn-node-statep node))
   :rule-classes :forward-chaining
   :hints (("Goal" :expand ((fn-replay-loop node records sequence))))))

; ...and the shape half of fn-replay-okp, which the loop's own two
; constructors give: an :ok kind can only have come from fn-replay-ok.
(local
 (defthm fn-snt-replay-loop-ok-has-ok-shape
   (implies (equal (fn-replay-result-kind
                    (fn-replay-loop node records sequence)) :ok)
            (fn-replay-ok-shapep (fn-replay-loop node records sequence)))
   :hints (("Goal" :induct (fn-replay-loop node records sequence)
            :in-theory (e/d (fn-replay-loop)
                            (fn-replay-apply-record fn-node-statep))))))

; `fn-replay-loop' hands `fn-replay-apply-record' any `fn-store-event-p', not
; only an article record: `6ab2c783' gave that function a retention arm and
; `4bb7bb3d' an identity arm, both on 2026-09-21, and this book has not
; certified since.  The step fact the induction below needs therefore has to
; hold of those arms too.  Both of them end in `fn-replay-advance-txid' to the
; successor of the event's transaction id and publish nothing, so they leave
; the node idle at that successor exactly as the article arm does.  Stated of
; the advance itself, then of each arm.
; Exported, not local: books/store-node-traces needs it of the same function
; for the retention arm of the relation it carries.
(defthm fn-snt-advance-from-idle-is-idle-at-its-txid
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (natp k)
                 (<= (fn-state-next-txid (fn-node-acceptance node)) k))
            (and (fn-node-statep (fn-replay-advance-txid node k))
                 (equal (fn-node-stage (fn-replay-advance-txid node k)) nil)
                 (equal (fn-state-pending
                         (fn-node-acceptance (fn-replay-advance-txid node k)))
                        nil)
                 (equal (fn-state-fenced
                         (fn-node-acceptance (fn-replay-advance-txid node k)))
                        nil)
                 (equal (fn-state-next-txid
                         (fn-node-acceptance (fn-replay-advance-txid node k)))
                        k)))
   :hints (("Goal"
            :use ((:instance fn-replay-advance-preserves-node-statep
                             (recorded-txid k)))
            :in-theory (e/d (fn-replay-advance-txid fn-node-statep fn-statep
                             fn-snx-core-definitions)
                            (fn-record-shape-vocabulary)))))

; `fn-replay-advance-txid' returns its argument unchanged unless that argument
; is a node, so an advance that IS a node was given one.  The retention arm
; needs this of the intermediate node it builds: the arm's own hypothesis is
; about the advance, and the rule above is about what the advance was given.
(defthm fn-snt-advance-of-a-node-came-from-a-node
   (implies (fn-node-statep (fn-replay-advance-txid node k))
            (fn-node-statep node))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (fn-replay-advance-txid)
                                   (fn-record-shape-vocabulary)))))

; Both arms test that the advance landed exactly on the event's transaction
; id.  That test is also what says the node was not already past it, which is
; the hypothesis the rule above needs: either the advance moved, and
; `fn-replay-advance-txid' moves only from at-or-before `k', or it did not
; move and the node was already exactly at `k'.
(defthm fn-snt-advance-that-lands-was-not-past-it
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (natp k)
                 (equal (fn-state-next-txid
                         (fn-node-acceptance (fn-replay-advance-txid node k)))
                        k))
            (<= (fn-state-next-txid (fn-node-acceptance node)) k))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-replay-advance-txid)
                                   (fn-record-shape-vocabulary)))))

(local
 (defthm fn-snt-identity-neutral-from-idle-is-idle-at-successor
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (natp (fn-store-event-txid event))
                 (fn-node-statep (fn-replay-apply-identity-neutral node event)))
            (and (equal (fn-node-stage
                         (fn-replay-apply-identity-neutral node event)) nil)
                 (equal (fn-state-pending
                         (fn-node-acceptance
                          (fn-replay-apply-identity-neutral node event))) nil)
                 (equal (fn-state-fenced
                         (fn-node-acceptance
                          (fn-replay-apply-identity-neutral node event))) nil)
                 (equal (fn-state-next-txid
                         (fn-node-acceptance
                          (fn-replay-apply-identity-neutral node event)))
                        (1+ (fn-store-event-txid event)))))
   :hints (("Goal"
            :use ((:instance fn-snt-advance-that-lands-was-not-past-it
                             (k (fn-store-event-txid event))))
            :in-theory (e/d (fn-replay-apply-identity-neutral)
                            (fn-replay-advance-txid fn-node-statep
                             fn-record-shape-vocabulary))))))

(local
 (defthm fn-snt-retention-from-idle-is-idle-at-successor
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (natp (fn-store-event-txid event))
                 (fn-node-statep (fn-replay-apply-retention-event node event)))
            (and (equal (fn-node-stage
                         (fn-replay-apply-retention-event node event)) nil)
                 (equal (fn-state-pending
                         (fn-node-acceptance
                          (fn-replay-apply-retention-event node event))) nil)
                 (equal (fn-state-fenced
                         (fn-node-acceptance
                          (fn-replay-apply-retention-event node event))) nil)
                 (equal (fn-state-next-txid
                         (fn-node-acceptance
                          (fn-replay-apply-retention-event node event)))
                        (1+ (fn-store-event-txid event)))))
   :hints (("Goal"
            :use ((:instance fn-snt-advance-that-lands-was-not-past-it
                             (k (fn-store-event-txid event))))
            :in-theory (e/d (fn-replay-apply-retention-event
                             fn-replay-complete-retention
                             fn-replay-node-with-retention)
                            (fn-replay-advance-txid fn-node-statep
                             fn-store-retention-event-p
                             fn-retain-admissiblep fn-retain-admit
                             fn-retain-release fn-retain-find-id
                             fn-retain-matching-releasep
                             fn-record-shape-vocabulary))))))

; The same two arms, as the linear half: each refuses unless the advance
; landed on the event's transaction id, so a node they accepted was not past
; it.  Stated separately from the idleness lemmas above because a `:rewrite'
; rule from a `<=' conclusion only fires on a literal match, and the step
; lemma below needs the fact as a linear assumption.
(local
 (defthm fn-snt-identity-neutral-from-idle-was-not-past-its-txid
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (natp (fn-store-event-txid event))
                 (fn-node-statep (fn-replay-apply-identity-neutral node event)))
            (<= (fn-state-next-txid (fn-node-acceptance node))
                (fn-store-event-txid event)))
   :rule-classes :linear
   :hints (("Goal"
            :use ((:instance fn-snt-advance-that-lands-was-not-past-it
                             (k (fn-store-event-txid event))))
            :in-theory (e/d (fn-replay-apply-identity-neutral)
                            (fn-replay-advance-txid fn-node-statep
                             fn-record-shape-vocabulary))))))

(local
 (defthm fn-snt-retention-from-idle-was-not-past-its-txid
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (natp (fn-store-event-txid event))
                 (fn-node-statep (fn-replay-apply-retention-event node event)))
            (<= (fn-state-next-txid (fn-node-acceptance node))
                (fn-store-event-txid event)))
   :rule-classes :linear
   :hints (("Goal"
            :use ((:instance fn-snt-advance-that-lands-was-not-past-it
                             (k (fn-store-event-txid event))))
            :in-theory (e/d (fn-replay-apply-retention-event
                             fn-replay-complete-retention
                             fn-replay-node-with-retention)
                            (fn-replay-advance-txid fn-node-statep
                             fn-store-retention-event-p
                             fn-retain-admissiblep fn-retain-admit
                             fn-retain-release fn-retain-find-id
                             fn-retain-matching-releasep
                             fn-record-shape-vocabulary))))))

; Every store event carries a uint32 transaction id, whichever of the five
; shapes it has.
(local
 (defthm fn-snt-store-event-txid-is-a-natural
   (implies (fn-store-event-p record)
            (natp (fn-store-event-txid record)))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal"
            :in-theory (e/d (fn-store-event-p fn-store-event-txid
                             fn-store-retention-event-p fn-record-p
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-record-uint32p)
                            (fn-record-shape-vocabulary
                             fn-record-msgidp fn-record-payloadp
                             fn-record-groups-validp
                             fn-record-metadata-bytes-p
                             fn-stxe-bounded-octetsp fn-stxe-tokenp))))))

; The three steps that can move the next transaction id only ever move it
; forward, and the durable completion leaves it where the preparation put it.
; Chained, that is the monotonicity half of the loop's step: the article and
; composite arms advance, prepare and complete, and the other two advance
; twice.
(local
 (defthm fn-snt-advance-is-txid-monotone
   (<= (fn-state-next-txid (fn-node-acceptance node))
       (fn-state-next-txid
        (fn-node-acceptance (fn-replay-advance-txid node k))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-replay-advance-txid)
                                   (fn-record-shape-vocabulary))))))

(local
 (defthm fn-snt-prepare-is-txid-monotone
   (<= (fn-state-next-txid (fn-node-acceptance s))
       (fn-state-next-txid
        (fn-node-acceptance
         (fn-node-prepare s generation msgid payload groups
                          obligation-id subject evidence charge stamp))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-node-prepare fn-accept-prepare
                                    fn-node-statep fn-statep
                                    fn-snx-core-definitions)
                                   (fn-record-shape-vocabulary))))))

(local
 (defthm fn-snt-durable-completion-is-idle-and-keeps-the-txid
   (implies (fn-node-pending-matchesp p txid generation)
            (and (equal (fn-node-stage
                         (fn-node-complete p txid generation :durable)) nil)
                 (equal (fn-state-pending
                         (fn-node-acceptance
                          (fn-node-complete p txid generation :durable))) nil)
                 (equal (fn-state-fenced
                         (fn-node-acceptance
                          (fn-node-complete p txid generation :durable))) nil)
                 (equal (fn-state-next-txid
                         (fn-node-acceptance
                          (fn-node-complete p txid generation :durable)))
                        (fn-state-next-txid (fn-node-acceptance p)))))
   ; `fn-state-pending' stays CLOSED, for the reason the note further down
   ; gives about `fn-state-next-txid': enabled, the goal becomes
   ; (car (cddddr (fn-make-state ...))) and the accessor-of-constructor rule
   ; the record generates no longer matches.
   :hints (("Goal" :in-theory (e/d (fn-node-complete fn-node-pending-matchesp
                                    fn-node-statep fn-statep
                                    fn-snx-core-definitions)
                                   (fn-state-pending fn-state-next-txid
                                    fn-node-stage fn-state-fenced
                                    fn-record-shape-vocabulary))))))

; The step fact the loop's induction needs, over every arm of
; `fn-replay-apply-record' rather than over an article record alone.
; Exported, not local: `books/store-node-traces' needs the same fact of the
; same function for the deferred publications `6ab2c783' and `4bb7bb3d'
; added, whose whole node effect IS this step.
(defthm fn-snt-apply-event-from-idle-is-idle-and-monotone
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (fn-store-event-p record)
                 (fn-node-statep (fn-replay-apply-record node record)))
            (and (equal (fn-node-stage
                         (fn-replay-apply-record node record)) nil)
                 (equal (fn-state-pending
                         (fn-node-acceptance
                          (fn-replay-apply-record node record))) nil)
                 (equal (fn-state-fenced
                         (fn-node-acceptance
                          (fn-replay-apply-record node record))) nil)
                 (<= (fn-state-next-txid (fn-node-acceptance node))
                     (fn-state-next-txid
                      (fn-node-acceptance
                       (fn-replay-apply-record node record))))))
   :hints (("Goal"
            :use ((:instance fn-snt-advance-that-lands-was-not-past-it
                             (k (fn-store-event-txid record))))
            :in-theory (e/d (fn-replay-apply-record)
                            (fn-replay-advance-txid fn-node-prepare
                             fn-node-complete fn-node-statep
                             fn-node-pending-matchesp
                             fn-replay-apply-retention-event
                             fn-replay-apply-identity-neutral
                             fn-replay-composite-record
                             fn-store-event-p fn-store-retention-event-p
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-record-record-vocabulary
                             fn-record-shape-vocabulary)))))

; A preparation that actually staged moved the next transaction id by exactly
; one: `fn-accept-prepare' writes `(1+ (fn-state-next-txid s))' and pins the
; pending there.  A preparation that refused returns its argument, whose stage
; is empty, and `fn-node-pending-matchesp' wants a stage.
(local
 (defthm fn-snt-prepare-that-stages-advances-by-one
   (implies (and (equal (fn-node-stage s) nil)
                 (equal (fn-state-pending (fn-node-acceptance s)) nil)
                 (fn-node-pending-matchesp
                  (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge stamp)
                  txid gen))
            (equal (fn-state-next-txid
                    (fn-node-acceptance
                     (fn-node-prepare s generation msgid payload groups
                                      obligation-id subject evidence charge stamp)))
                   (1+ (fn-state-next-txid (fn-node-acceptance s)))))
   ; The recognizers stay closed: the conclusion is one field, and
   ; `fn-snx-node-state-acceptance-is-state' answers the one `fn-statep'
   ; test `fn-accept-prepare' makes (95 s with them open, 2026-09-23).
   :hints (("Goal" :in-theory (e/d (fn-node-prepare fn-accept-prepare
                                    fn-node-pending-matchesp)
                                   (fn-node-statep fn-statep
                                    fn-retain-admissiblep fn-retain-admit
                                    fn-selection-validp
                                    fn-state-next-txid fn-state-pending
                                    fn-node-stage fn-state-fenced
                                    fn-record-shape-vocabulary))))))

; And so every arm of the step lands the node at the successor of the event's
; own transaction id: the two that only advance land there directly, and the
; two that prepare and complete land there because the advance put the node at
; the event's id, the preparation moved it by one and the durable completion
; left it alone.
; `fn-record-record-vocabulary' is withdrawn in both step lemmas below: with
; the record accessors open the arm's transaction id reaches the goal as
; `(cadr record)' and every rule stated over `fn-record-txid' or
; `fn-store-event-txid' stops matching.
(defthm fn-snt-apply-event-from-idle-is-at-the-successor
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (fn-store-event-p record)
                 (fn-node-statep (fn-replay-apply-record node record)))
            (equal (fn-state-next-txid
                    (fn-node-acceptance (fn-replay-apply-record node record)))
                   (1+ (fn-store-event-txid record))))
   :hints (("Goal"
            :use ((:instance fn-snt-advance-that-lands-was-not-past-it
                             (k (fn-store-event-txid record))))
            :in-theory (e/d (fn-replay-apply-record)
                            (fn-replay-advance-txid fn-node-prepare
                             fn-node-complete fn-node-statep
                             fn-node-pending-matchesp
                             fn-replay-apply-retention-event
                             fn-replay-apply-identity-neutral
                             fn-replay-composite-record
                             fn-store-event-p fn-store-retention-event-p
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-record-record-vocabulary
                             fn-record-shape-vocabulary)))))

; And the same step's other arithmetic half: a node the step accepted was not
; past the event's transaction id.  With the successor equation above, this is
; what closes the loop's monotonicity by linear arithmetic.
(local
 (defthm fn-snt-apply-event-from-idle-was-not-past-its-txid
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (fn-store-event-p record)
                 (fn-node-statep (fn-replay-apply-record node record)))
            (<= (fn-state-next-txid (fn-node-acceptance node))
                (fn-store-event-txid record)))
   :rule-classes :linear
   :hints (("Goal"
            :use ((:instance fn-snt-advance-that-lands-was-not-past-it
                             (k (fn-store-event-txid record))))
            :in-theory (e/d (fn-replay-apply-record)
                            (fn-replay-advance-txid fn-node-prepare
                             fn-node-complete fn-node-statep
                             fn-node-pending-matchesp
                             fn-replay-apply-retention-event
                             fn-replay-apply-identity-neutral
                             fn-replay-composite-record
                             fn-store-event-p fn-store-retention-event-p
                             fn-stxe-p fn-stxk-p fn-stxa-p
                             fn-record-record-vocabulary
                             fn-record-shape-vocabulary))))))

; The same step's arithmetic half as a linear fact: the loop induction closes
; its monotonicity conjunct by transitivity with the induction hypothesis, and
; a `:rewrite' rule from a `<=' conclusion does not reach that.
(local
 (defthm fn-snt-apply-event-from-idle-is-txid-monotone
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (fn-store-event-p record)
                 (fn-node-statep (fn-replay-apply-record node record)))
            (<= (fn-state-next-txid (fn-node-acceptance node))
                (fn-state-next-txid
                 (fn-node-acceptance (fn-replay-apply-record node record)))))
   :rule-classes :linear
   :hints (("Goal"
            :use fn-snt-apply-event-from-idle-is-idle-and-monotone
            :in-theory (disable fn-replay-apply-record fn-node-statep
                                fn-snt-apply-event-from-idle-is-idle-and-monotone)))))

; The loop carries idleness, and separately it only moves the next txid
; forward.  The two halves induct apart: with all five conclusions under one
; induction the arithmetic conjunct pushes a subgoal less general than its own
; parent and the attempt fails (hbox certify-20260922T110406Z-2884310).  The
; combined statement below is their conjunction and is what the callers cite.
(local
 (defthm fn-snt-replay-loop-from-idle-is-idle
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (equal (fn-replay-result-kind
                         (fn-replay-loop node records sequence)) :ok))
            (and (fn-node-statep
                  (fn-replay-result-node (fn-replay-loop node records sequence)))
                 (equal (fn-node-stage
                         (fn-replay-result-node
                          (fn-replay-loop node records sequence))) nil)
                 (equal (fn-state-pending
                         (fn-node-acceptance
                          (fn-replay-result-node
                           (fn-replay-loop node records sequence)))) nil)
                 (equal (fn-state-fenced
                         (fn-node-acceptance
                          (fn-replay-result-node
                           (fn-replay-loop node records sequence)))) nil)))
   :hints (("Goal" :induct (fn-replay-loop node records sequence)
            :in-theory (e/d (fn-replay-loop)
                            (fn-replay-apply-record fn-node-statep))))))

(local
 (defthm fn-snt-replay-loop-from-idle-is-txid-monotone
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (equal (fn-replay-result-kind
                         (fn-replay-loop node records sequence)) :ok))
            (<= (fn-state-next-txid (fn-node-acceptance node))
                (fn-state-next-txid
                 (fn-node-acceptance
                  (fn-replay-result-node
                   (fn-replay-loop node records sequence))))))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :induct (fn-replay-loop node records sequence)
            :in-theory (e/d (fn-replay-loop)
                            (fn-replay-apply-record fn-node-statep))))))

(local
 (defthm fn-snt-replay-loop-from-idle-is-idle-and-monotone
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (equal (fn-replay-result-kind
                         (fn-replay-loop node records sequence)) :ok))
            (and (fn-node-statep
                  (fn-replay-result-node (fn-replay-loop node records sequence)))
                 (equal (fn-node-stage
                         (fn-replay-result-node
                          (fn-replay-loop node records sequence))) nil)
                 (equal (fn-state-pending
                         (fn-node-acceptance
                          (fn-replay-result-node
                           (fn-replay-loop node records sequence)))) nil)
                 (equal (fn-state-fenced
                         (fn-node-acceptance
                          (fn-replay-result-node
                           (fn-replay-loop node records sequence)))) nil)
                 (<= (fn-state-next-txid (fn-node-acceptance node))
                     (fn-state-next-txid
                      (fn-node-acceptance
                       (fn-replay-result-node
                        (fn-replay-loop node records sequence)))))))
   :hints (("Goal"
            :use (fn-snt-replay-loop-from-idle-is-idle
                  fn-snt-replay-loop-from-idle-is-txid-monotone)
            :in-theory (disable fn-replay-loop fn-replay-apply-record
                                fn-node-statep
                                fn-snt-replay-loop-from-idle-is-idle
                                fn-snt-replay-loop-from-idle-is-txid-monotone)))))

; The txid bound, as its own list recursion.  fn-sf-record-listp carries a
; `lower' that the loop's induction does not move, so the induction hypothesis
; would be at the wrong lower bound; this predicate mentions only the bound.
(local
 (defun fn-snt-txids-below (records bound)
   (declare (xargs :guard t :verify-guards nil))
   (if (consp records)
       ; the natp is carried, not forward chained: in the loop induction the
       ; contradiction that discharges the step is txid < bound < txid+1,
       ; which linear arithmetic sees only over integers.
       ; `fn-store-event-txid', not `fn-record-txid': `fn-sf-record-listp'
       ; bounds the transaction id of every store event in the history, and
       ; since 6ab2c783 and 4bb7bb3d those are not all article records.
       (and (natp (fn-store-event-txid (car records)))
            (< (fn-store-event-txid (car records)) bound)
            (fn-snt-txids-below (cdr records) bound))
     t)))

(local
 (defthm fn-snt-record-listp-gives-txids-below
   (implies (fn-sf-record-listp records sequence lower bound)
            (fn-snt-txids-below records bound))
   :hints (("Goal" :induct (fn-sf-record-listp records sequence lower bound)
            :in-theory (disable fn-record-txid fn-store-event-txid)))))

(local
 (defthm fn-snt-replay-loop-from-idle-is-under-bound
   (implies (and (fn-node-statep node)
                 (equal (fn-node-stage node) nil)
                 (equal (fn-state-pending (fn-node-acceptance node)) nil)
                 (equal (fn-state-fenced (fn-node-acceptance node)) nil)
                 (natp bound)
                 (<= (fn-state-next-txid (fn-node-acceptance node)) bound)
                 (fn-snt-txids-below records bound)
                 (equal (fn-replay-result-kind
                         (fn-replay-loop node records sequence)) :ok))
            (<= (fn-state-next-txid
                 (fn-node-acceptance
                  (fn-replay-result-node (fn-replay-loop node records sequence))))
                bound))
   :hints (("Goal" :induct (fn-replay-loop node records sequence)
            :in-theory (e/d (fn-replay-loop)
                            (fn-replay-apply-record fn-node-statep
                             fn-record-txid fn-store-event-txid))))))

(local
 (defthm fn-snt-initial-node-is-idle
   (and (equal (fn-node-stage (fn-node-initial-state groups capacity)) nil)
        (equal (fn-state-pending
                (fn-node-acceptance (fn-node-initial-state groups capacity)))
               nil)
        (equal (fn-state-fenced
                (fn-node-acceptance (fn-node-initial-state groups capacity)))
               nil)
        (equal (fn-state-next-txid
                (fn-node-acceptance (fn-node-initial-state groups capacity)))
               0))
   ; fn-state-next-txid stays CLOSED: enabling it turns the goal into
   ; (cadddr (fn-make-state ...)) and the accessor-of-constructor rule the
   ; record generates no longer matches.
   :hints (("Goal" :in-theory (e/d (fn-node-initial-state
                                    fn-snx-core-definitions)
                                   (fn-state-next-txid))))))

; A successfully replayed history leaves an idle node.  The three conjuncts
; are the three things fn-replay-advance-okp needs that fn-replay-okp does
; not supply.
(defthm fn-snt-replayed-history-node-is-idle
  (implies (fn-replay-okp (fn-replay groups capacity records))
           (and (equal (fn-node-stage
                        (fn-replay-result-node
                         (fn-replay groups capacity records))) nil)
                (equal (fn-state-pending
                        (fn-node-acceptance
                         (fn-replay-result-node
                          (fn-replay groups capacity records)))) nil)
                (equal (fn-state-fenced
                        (fn-node-acceptance
                         (fn-replay-result-node
                          (fn-replay groups capacity records)))) nil)))
  :hints (("Goal"
           :use ((:instance fn-snt-replay-loop-from-idle-is-idle-and-monotone
                            (node (fn-node-initial-state groups capacity))
                            (sequence 0)))
           :in-theory (e/d (fn-replay fn-replay-okp)
                           (fn-replay-loop fn-node-statep
                            fn-snt-replay-loop-from-idle-is-idle-and-monotone)))))

; A history whose txids are all below a bound is recoverable AT that bound.
; With fn-sf-record-listp taken from the gate fn-sf-frontier-rollback-visiblep
; carries, this is the frontier arm of fn-sf-recovery-crash-imagep discharged.
(defthm fn-snt-history-recoverable-under-record-bound
  (implies (and (fn-replay-okp (fn-replay groups capacity records))
                (natp bound)
                (fn-sf-record-listp records 0 0 bound))
           (fn-sf-history-recoverablep groups capacity records bound))
  :hints (("Goal"
           :use ((:instance fn-snt-replay-loop-from-idle-is-under-bound
                            (node (fn-node-initial-state groups capacity))
                            (sequence 0))
                 (:instance fn-snt-record-listp-gives-txids-below
                            (sequence 0) (lower 0))
                 (:instance fn-snt-replay-loop-from-idle-is-idle-and-monotone
                            (node (fn-node-initial-state groups capacity))
                            (sequence 0))
                 (:instance fn-replay-advance-reconstructs-recorded-txid
                            (node (fn-replay-result-node
                                   (fn-replay groups capacity records)))
                            (recorded-txid bound))
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-replay-result-node
                                   (fn-replay groups capacity records)))
                            (recorded-txid bound)))
           :in-theory (e/d (fn-replay fn-replay-okp fn-sf-history-recoverablep
                            fn-sf-replay-node fn-replay-advance-okp)
                           (fn-replay-loop fn-node-statep fn-sf-record-listp
                            fn-replay-advance-txid fn-snt-txids-below
                            fn-snt-replay-loop-from-idle-is-under-bound
                            fn-snt-record-listp-gives-txids-below
                            fn-snt-replay-loop-from-idle-is-idle-and-monotone
                            fn-replay-advance-reconstructs-recorded-txid
                            fn-replay-advance-preserves-node-statep)))))

; PREFIX RECOVERABILITY.  :rule-classes nil because the suffix is free in the
; hypothesis; the corollary below is the rewrite rule.
(defthm fn-snt-history-recoverable-prefix
  (implies (and (true-listp prefix)
                (fn-sf-history-recoverablep groups capacity
                                            (append prefix suffix) frontier))
           (fn-sf-history-recoverablep groups capacity prefix frontier))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-snt-replay-loop-from-idle-is-idle-and-monotone
                            (node (fn-node-initial-state groups capacity))
                            (records prefix) (sequence 0))
                 (:instance fn-snt-replay-loop-from-idle-is-idle-and-monotone
                            (node (fn-replay-result-node
                                   (fn-replay groups capacity prefix)))
                            (records suffix)
                            (sequence (fn-replay-result-sequence
                                       (fn-replay groups capacity prefix))))
                 (:instance fn-snt-successful-replay-sequence
                            (node (fn-node-initial-state groups capacity))
                            (records prefix) (sequence 0))
                 (:instance fn-replay-advance-reconstructs-recorded-txid
                            (node (fn-replay-result-node
                                   (fn-replay groups capacity prefix)))
                            (recorded-txid frontier))
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-replay-result-node
                                   (fn-replay groups capacity prefix)))
                            (recorded-txid frontier)))
           :in-theory (e/d (fn-replay fn-replay-okp fn-sf-history-recoverablep
                            fn-sf-replay-node fn-replay-advance-okp)
                           (fn-replay-loop fn-node-statep
                            fn-replay-advance-txid
                            fn-snt-replay-loop-from-idle-is-idle-and-monotone
                            fn-snt-successful-replay-sequence
                            fn-replay-advance-reconstructs-recorded-txid
                            fn-replay-advance-preserves-node-statep)))))

; fn-sf-but-last-append-last carries (consp xs); the empty list needs no
; lemma -- both sides are nil -- but it does need to be a case.  Named here
; because fn-sf-but-last-append-last is :rule-classes nil, and a
; :rule-classes nil theorem in a THEORY EXPRESSION is a hard error, not a
; no-op (the sibling of w9/storage-3's constrained-function finding).
(local
 (defthm fn-snt-but-last-append-last-total
   (implies (true-listp xs)
            (equal (append (fn-sf-but-last xs) (last xs)) xs))
   :rule-classes nil
   :hints (("Goal" :cases ((consp xs))
            :use ((:instance fn-sf-but-last-append-last))
            :in-theory (enable fn-sf-but-last)))))

; The corollary the recovery freedom uses: dropping the last record of a
; recoverable history leaves a recoverable history at the same frontier.
(defthm fn-snt-history-recoverable-of-but-last
  (implies (and (true-listp records)
                (fn-sf-history-recoverablep groups capacity records frontier))
           (fn-sf-history-recoverablep groups capacity
                                       (fn-sf-but-last records) frontier))
  :hints (("Goal"
           :use ((:instance fn-snt-history-recoverable-prefix
                            (prefix (fn-sf-but-last records))
                            (suffix (last records)))
                 (:instance fn-snt-but-last-append-last-total (xs records)))
           :in-theory (disable fn-sf-history-recoverablep fn-sf-but-last))))

; -----------------------------------------------------------------------------
; Export theory.  Withdrawn under a name: the replay-composition and
; frontier-advance lemmas (proof vocabulary for the trace books) and the
; committed-record recognizer.  Enabled on include: the preservation
; keystones, the cannot-acknowledge family, the completion-gate keystone
; and the resolution correspondences.
(deftheory fn-store-node-invariants-vocabulary
  '(fn-sn-file-recovery-retains-history fn-sn-replay-loop-append
    fn-sn-replay-singleton-is-live-completion
    fn-sn-extended-history-equals-live-completion
    fn-snt-node-reconstruct fn-snt-acceptance-reconstruct
    fn-snt-valid-node-is-consp fn-snt-advanced-node-is-consp
    fn-snt-advance-is-idle fn-snt-advance-at-current-is-identity
    fn-snt-advance-twice fn-snt-history-recoverable-monotone
    fn-snt-replayed-node-idle-and-frontier fn-snt-advance-replayed-node
    fn-snt-successful-replay-sequence fn-snt-successful-replay-history-length
    fn-snt-prepared-abort-is-frontier-advance
    fn-snt-prepared-durable-is-idle-at-successor
    fn-snt-apply-event-from-idle-is-idle-and-monotone
    fn-snt-apply-event-from-idle-is-at-the-successor))
(in-theory (disable fn-store-node-invariants-vocabulary fn-sn-committed-recordp))
