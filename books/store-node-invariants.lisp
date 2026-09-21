; Correspondence for actual live node/file completion, without a trusted reply.
(in-package "ACL2")
(include-book "store-node")
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary)))

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

(defthm fn-sn-finish-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-finish s)))
  :hints (("Goal"
           :use ((:instance fn-sn-record-p-implies-string-msgid
                            (record (fn-sn-completion-record s))))
           :in-theory (disable fn-sf-core-completion
                               fn-sf-emit-success))))

; Keystone for the host-called acceptance subject.  host/store-node-host.lisp
; `fn-store-sn-finish' calls fn-sn-finish; on its enabled durable branch the
; cheap retrieval query returns exactly the verdict computed over the
; accepted record under the then-current keyring generation.
(defthm fn-sn-finish-records-the-acceptance-verdict
  (implies (fn-sn-completion-enabledp s)
           (equal
            (fn-sn-verdict-lookup
             (fn-sn-finish s)
             (fn-record-msgid (fn-sn-completion-record s)))
            (fn-stx-verdict-of-octets
             (fn-record-payload (fn-sn-completion-record s))
             (fn-sn-keyring s)
             (fn-sn-keyring-generation s))))
  :hints (("Goal"
           :in-theory (enable fn-sn-verdict-lookup
                              fn-sn-verdict-lookup-list))))

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

(defthm fn-sn-file-recovery-retains-history
  (and (equal (fn-sf-records (fn-sf-recover files groups capacity))
              (fn-sf-records files))
       (equal (fn-sf-frontier (fn-sf-recover files groups capacity))
              (fn-sf-frontier files))))

(defthm fn-sn-file-recovery-produces-valid-replay
  (implies (and (fn-sf-statep files)
                (equal (fn-sf-phase files) :replaying)
                (equal (fn-sf-phase (fn-sf-recover files groups capacity))
                       :recovering))
           (fn-node-statep (fn-sf-replay-node groups capacity
                              (fn-sf-records files) (fn-sf-frontier files))))
  :hints (("Goal" :in-theory (disable fn-sf-replay-node))))

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
                  (equal (fn-record-charge record) (fn-node-stage-charge stage)))))
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

(defthm fn-sn-finish-is-actual-durable-completion
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sn-node (fn-sn-finish s))
                  (fn-node-complete (fn-sn-node s)
                    (fn-record-txid (fn-sn-completion-record s))
                    (fn-record-generation (fn-sn-completion-record s))
                    :durable)))
  :hints (("Goal" :in-theory (disable fn-sn-completion-enabledp
                                      fn-sn-completion-record))))

(defthm fn-sn-finish-installs-exact-article-and-archive-pin
  (implies (fn-sn-completion-enabledp s)
           (fn-sn-committed-recordp (fn-sn-node (fn-sn-finish s))
                                    (fn-sn-completion-record s)))
  :hints (("Goal" :use (fn-sn-finish-is-actual-durable-completion
                         (:instance fn-sn-actual-durable-completion-installs-record
                          (node (fn-sn-node s))
                          (record (fn-sn-completion-record s))))
           :in-theory (disable fn-sn-finish fn-sn-committed-recordp
                               fn-sn-record-bindsp fn-sn-completion-record))))

(defthm fn-sn-finish-acknowledges-exact-pair
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sf-successes (fn-sn-files (fn-sn-finish s)))
                  (append (fn-sf-successes (fn-sn-files s))
                          (list (fn-sf-completion (fn-sn-files s))))))
  :hints (("Goal"
           :use ((:instance fn-sf-core-completion-preserves-state
                    (s (fn-sn-files s))
                    (sequence (fn-record-sequence (fn-sn-completion-record s)))
                    (txid (fn-record-txid (fn-sn-completion-record s)))))
           :in-theory (e/d (fn-sf-core-completion fn-sf-emit-success)
                            (fn-sn-record-bindsp fn-sn-completion-record)))))

(defthm fn-sn-new-success-requires-actual-matching-durable-node-completion
  (implies (not (equal (fn-sf-successes (fn-sn-files (fn-sn-finish s)))
                       (fn-sf-successes (fn-sn-files s))))
           (and (fn-sn-completion-enabledp s)
                (fn-sn-record-bindsp (fn-sn-node s) (fn-sn-completion-record s))
                (equal (fn-sn-node (fn-sn-finish s))
                       (fn-node-complete (fn-sn-node s)
                         (fn-record-txid (fn-sn-completion-record s))
                         (fn-record-generation (fn-sn-completion-record s))
                         :durable))
                (fn-sn-committed-recordp (fn-sn-node (fn-sn-finish s))
                                         (fn-sn-completion-record s))))
  :hints (("Goal" :use (fn-sn-finish-is-actual-durable-completion
                         fn-sn-finish-installs-exact-article-and-archive-pin
                         fn-sn-finish-disabled-is-no-op)
           :cases ((fn-sn-completion-enabledp s))
           :in-theory (disable fn-sn-finish fn-sn-completion-record
                               fn-sn-record-bindsp fn-sn-committed-recordp))))

; A matching live proposal has exactly the same durable meaning as a record
; interpreted by replay.  This is equality of the entire node: watermarks,
; memberships, articles, retention accounting, archive pins, bindings and txid.
(defthm fn-sn-replay-is-actual-live-durable-completion
  (implies (and (fn-replay-advance-okp node (fn-record-txid record))
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

(defthm fn-snt-prepared-abort-is-frontier-advance
  (implies (and (fn-replay-advance-okp node (fn-record-txid record))
                (fn-node-pending-matchesp (fn-sn-prepare-node node record)
                  (fn-record-txid record) (fn-record-generation record)))
           (equal (fn-node-complete (fn-sn-prepare-node node record)
                    (fn-record-txid record) (fn-record-generation record) :aborted)
                  (fn-replay-advance-txid node (1+ (fn-record-txid record)))))
  :hints (("Goal" :in-theory (enable fn-sn-prepare-node fn-node-prepare
    fn-node-complete fn-replay-advance-txid fn-node-statep fn-statep fn-snx-core-definitions
       fn-state-pending
    ))))

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
                        (completion-status :durable)))
           :in-theory (enable fn-sn-prepare-node fn-node-prepare
    fn-node-complete fn-replay-advance-txid fn-node-statep fn-statep fn-snx-core-definitions
       fn-state-pending
    ))))

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
(defthm fn-sn-finish-preserves-indexedp
  (implies (fn-sn-indexedp s)
           (fn-sn-indexedp (fn-sn-finish s)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-completion-enabledp fn-sn-record-bindsp)
                           (fn-sf-core-completion fn-sf-emit-success
                            fn-node-statep fn-node-complete
                            fn-stx-index-of-store fn-stx-store
                            fn-stx-index-invariantp fn-stx-index-add
                            fn-sn-completion-record fn-node-pending-matchesp))
           :use ((:instance fn-sn-finish-preserves-state)
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

; The loop carries idleness and only moves the next txid forward.
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
   :hints (("Goal" :induct (fn-replay-loop node records sequence)
            :in-theory (e/d (fn-replay-loop)
                            (fn-replay-apply-record fn-node-statep))))))

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
       (and (natp (fn-record-txid (car records)))
            (< (fn-record-txid (car records)) bound)
            (fn-snt-txids-below (cdr records) bound))
     t)))

(local
 (defthm fn-snt-record-listp-gives-txids-below
   (implies (fn-sf-record-listp records sequence lower bound)
            (fn-snt-txids-below records bound))
   :hints (("Goal" :induct (fn-sf-record-listp records sequence lower bound)
            :in-theory (disable fn-record-txid)))))

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
                             fn-record-txid))))))

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
    fn-snt-prepared-durable-is-idle-at-successor))
(in-theory (disable fn-store-node-invariants-vocabulary fn-sn-committed-recordp))
