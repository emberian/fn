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

(defthm fn-sn-finish-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-finish s)))
  :hints (("Goal" :in-theory (disable fn-sf-core-completion
                                      fn-sf-emit-success))))

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
