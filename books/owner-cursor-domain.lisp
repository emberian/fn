; The journal cursor relation at the actual owner state boundaries.
; Proof vocabulary only: no served history scan and no numeric ceiling.
(in-package "ACL2")
(include-book "owner-recovery-retain")
(include-book "consumer-store-invariants")
(include-book "record-width-producers")
(include-book "owner-snapshot-recovery")
(include-book "owner-prepare-deferred-carried")

(local (in-theory (disable (tau-system))))

; Both carried prepares stage a candidate without appending the journal or
; changing its cursor. Their admission gates need not be expanded here.
(defthm fn-owner-carried-identity-prepare-preserves-cursor
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-ccar-sn-prepare-identity s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-sequencep fn-ccar-sn-prepare-identity
                 fn-pcar-stage-record fn-sn-update fn-sf-completion-phasep)
                (fn-pcar-stage-record-is-stage-record fn-stxe-p fn-stxk-p fn-hstxa-p
                 fn-sn-statep fn-ccar-cpe-projection-step fn-replay-apply-record
                 fn-replay-identity-step fn-sn-make-v6)))))

(defthm fn-owner-carried-article-prepare-preserves-cursor
  (implies (fn-sn-identity-sequencep s)
           (fn-sn-identity-sequencep (fn-prc-spc-prepare s record view carry)))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-sequencep fn-prc-spc-prepare
                 fn-pcar-stage-record fn-sn-update fn-sf-completion-phasep)
                (fn-pcar-stage-record-is-stage-record fn-held-p
                 fn-sn-statep fn-prc-sn-prepare-node fn-rcon-sn-record-bindsp
                 fn-rcon-cpe-projection-step fn-sn-make-v6)))))

(defthm fn-owner-served-identity-prepare-preserves-cursor
  (implies (fn-sn-identity-sequencep (fn-sbud-oc-store oc))
           (fn-sn-identity-sequencep
            (fn-sbud-oc-store (fn-oiis-prepare-identity oc w h))))
  :hints (("Goal" :use fn-pout-store-of-oiis-prepare-identity
           :in-theory '(fn-owner-carried-identity-prepare-preserves-cursor))))

(defthm fn-owner-served-article-prepare-preserves-cursor
  (implies (fn-sn-identity-sequencep (fn-sbud-oc-store oc))
           (fn-sn-identity-sequencep
            (fn-sbud-oc-store (fn-psrv-prepare oc record budget carry))))
  :hints (("Goal" :use fn-pout-store-of-psrv-prepare
           :in-theory '(fn-owner-carried-article-prepare-preserves-cursor))))

(defthm fn-owner-served-topic-prepare-preserves-cursor
  (implies (fn-sn-identity-sequencep (fn-sbud-oc-store oc))
           (fn-sn-identity-sequencep
            (fn-sbud-oc-store (fn-psrv-prepare-topic oc e))))
  :hints (("Goal" :use fn-pout-store-of-psrv-prepare-topic
           :in-theory '(fn-csi-prepare-topic-preserves-identity-sequence))))

;; The carried deferred prepares (books/owner-prepare-deferred-carried.lisp)
;; stage a candidate without appending the journal or moving its cursor.
(defthm fn-owner-carried-deferred-prepares-preserve-cursor
  (implies (fn-sn-identity-sequencep s)
           (and (fn-sn-identity-sequencep (fn-pdc-sn-prepare-retention s event))
                (fn-sn-identity-sequencep (fn-pdc-sn-prepare-consumer s event))
                (fn-sn-identity-sequencep (fn-pdc-sn-prepare-topic s event))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-sequencep fn-pdc-sn-prepare-retention
                 fn-pdc-sn-prepare-consumer fn-pdc-sn-prepare-topic
                 fn-pcar-stage-record fn-sn-update fn-sf-completion-phasep)
                (fn-pcar-stage-record-is-stage-record fn-store-retention-event-p
                 fn-cpe-eventp fn-th-topic-eventp fn-th-prefix-step
                 fn-sn-statep fn-ccar-cpe-projection-step fn-replay-apply-record
                 fn-replay-apply-retention-event fn-sn-make-v6)))))

(defthm fn-owner-served-deferred-prepares-preserve-cursor
  (implies (fn-sn-identity-sequencep (fn-sbud-oc-store oc))
           (and (fn-sn-identity-sequencep
                 (fn-sbud-oc-store (mv-nth 1 (fn-pdc-pout-prepare-consumer oc e))))
                (fn-sn-identity-sequencep
                 (fn-sbud-oc-store (mv-nth 1 (fn-pdc-pout-prepare-topic oc e))))))
  :hints (("Goal" :use (fn-pdc-store-of-owner-prepares
                        fn-pdc-pout-prepares-answer-the-store-change)
           :in-theory '(fn-owner-carried-deferred-prepares-preserve-cursor))))

(local
 (defthm fn-owner-cursor-store-by-definition
   (equal (fn-owner-store state) (fn-sbud-oc-store (fn-owner-ocfg state)))
   :hints (("Goal" :in-theory (enable fn-owner-store fn-owner-core
                                      fn-owner-ocfg fn-sbud-oc-store)))))

(local
 (defthm fn-owner-irc-identity-prepare-preserves-cursor
   (implies (fn-sn-identity-sequencep s)
            (fn-sn-identity-sequencep (fn-irc-sn-prepare-identity s event carry)))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-identity-sequencep fn-irc-sn-prepare-identity
                  fn-pcar-stage-record fn-sn-update fn-sf-completion-phasep)
                 (fn-pcar-stage-record-is-stage-record fn-stxe-p fn-stxk-p fn-hstxa-p
                  fn-sn-statep fn-ccar-cpe-projection-step fn-irc-apply-record
                  fn-replay-identity-step fn-sn-make-v6))))))

(local
 (defthm fn-owner-irc-outcome-preserves-cursor
   (implies (fn-sn-identity-sequencep (fn-sbud-oc-store oc))
            (fn-sn-identity-sequencep
             (fn-sbud-oc-store (mv-nth 1 (fn-irc-pout-prepare-identity oc w h carry)))))
   :hints (("Goal" :in-theory
            '(fn-irc-pout-prepare-identity fn-irc-oiis-prepare-identity
              fn-irc-psrv-prepare-identity fn-irc-ocfg-prepare-identity
              fn-sbud-oc-store fn-ocfg-with-owner
              fn-ocfg-owner-of-fn-ocfg-make fn-own-refresh-keeps-fields
              fn-own-store-of-fn-own-make fn-owner-irc-identity-prepare-preserves-cursor
              mv-nth nth zp car-cons cdr-cons (:executable-counterpart zp)
              (:executable-counterpart binary-+) (:executable-counterpart unary--))))))

(defthm fn-owner-prepare-identity-preserves-cursor
  (implies (fn-sn-identity-sequencep (fn-owner-store state))
           (fn-sn-identity-sequencep
            (fn-owner-store
             (mv-nth 2 (fn-owner-prepare-identity event fn-arena state)))))
  :hints (("Goal" :in-theory
           '(fn-owner-cursor-store-by-definition
             (:type-prescription fn-irc-pout-prepare-identity)
             (:executable-counterpart zp) (:executable-counterpart binary-+)
             (:executable-counterpart unary--) fn-prc-carryp-of-refresh
             fn-owner-prepare-identity fn-pout-prepare-identity
             mv-nth nth endp zp car-cons cdr-cons
             fn-owner-ocfg-of-retain-carry-put fn-owner-ocfg-of-install-ocfg
             fn-owner-ocfg-of-other-global-put
             fn-owner-irc-outcome-preserves-cursor))))

; The cursor's representable range follows from the durable allocator and
; maintained count relation. It is not a new input bound or runtime scan.
(defthm fn-owner-carried-cursor-is-u32
  (implies (and (fn-sn-statep s) (fn-sn-identity-sequencep s))
           (fn-record-uint32p (fn-sn-identity-next s)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-record-listp-len-bound
                            (records (fn-sf-records (fn-sn-files s)))
                            (sequence 0) (lower 0)
                            (frontier (fn-sf-frontier (fn-sn-files s)))))
           :in-theory
           (e/d (fn-sn-statep fn-sf-statep fn-sn-identity-sequencep
                 fn-record-uint32p)
                (fn-sf-record-listp fn-sn-make-v6)))))

; Exact host-called entries, including their previously verified guards.
(defun fn-owner-prepare-consumer (event fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))))
           (ignorable fn-arena))
  (if (not (fn-cpe-eventp event))
      (value :invalid)
    ; fn-pdc-pout-prepare-consumer: (:store (:prepare-consumer E)) with the
    ; carried Store prepare, no appended-history replay
    ; (books/owner-prepare-deferred-carried.lisp: equal to
    ; fn-pout-prepare-consumer under fn-snt-relation and whenever the
    ; reference stages; keeps fn-lgoc-invariantp), and its word
    ; (fn-pdc-pout-prepares-answer-the-store-change).
    (mv-let (word next)
      (fn-pdc-pout-prepare-consumer (fn-owner-ocfg state) event)
      (let ((state (fn-owner-install-ocfg next state)))
        (value word)))))

(defun fn-owner-prepare-topic (event fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))))
           (ignorable fn-arena))
  (if (not (fn-th-topic-eventp event))
      (value :invalid)
    ; fn-psrv-prepare-topic (lane prepare-served): (:store (:prepare-topic
    ; E)) when the consumer projection accepts E, which its completion
    ; needs (fn-psrv-prepare-topic-is-ocfg-step-when-admitted,
    ; fn-psrv-prepare-topic-preserves-invariant); fn-pout-prepare-topic
    ; answers its word (KEYSTONE
    ; fn-pout-prepare-topic-answers-the-store-change).
    ; Since lane served-incremental-2: fn-pdc-pout-prepare-topic, the same
    ; with the carried Store prepare (no appended-history replay; equal to
    ; fn-pout-prepare-topic under fn-snt-relation and whenever the reference
    ; stages; fn-pdc-psrv-prepare-topic-preserves-invariant).
    (mv-let (word next)
      (fn-pdc-pout-prepare-topic (fn-owner-ocfg state) event)
      (let ((state (fn-owner-install-ocfg next state)))
        (value word)))))

(defthm fn-owner-prepare-consumer-preserves-cursor
  (implies (fn-sn-identity-sequencep (fn-owner-store state))
           (fn-sn-identity-sequencep
            (fn-owner-store
             (mv-nth 2 (fn-owner-prepare-consumer event fn-arena state)))))
  :hints (("Goal" :in-theory
           '(fn-owner-cursor-store-by-definition fn-owner-prepare-consumer
             fn-owner-served-deferred-prepares-preserve-cursor
             fn-owner-ocfg-of-install-ocfg
             mv-nth nth zp car-cons cdr-cons
             (:executable-counterpart zp) (:executable-counterpart binary-+)
             (:executable-counterpart unary--)))))

(defthm fn-owner-prepare-topic-preserves-cursor
  (implies (fn-sn-identity-sequencep (fn-owner-store state))
           (fn-sn-identity-sequencep
            (fn-owner-store
             (mv-nth 2 (fn-owner-prepare-topic event fn-arena state)))))
  :hints (("Goal" :in-theory
           '(fn-owner-cursor-store-by-definition fn-owner-prepare-topic
             fn-owner-served-deferred-prepares-preserve-cursor
             fn-owner-ocfg-of-install-ocfg
             mv-nth nth zp car-cons cdr-cons
             (:executable-counterpart zp) (:executable-counterpart binary-+)
             (:executable-counterpart unary--)))))

(local
 (defthm fn-owner-reference-completion-preserves-cursor
   (implies (fn-sn-identity-sequencep (fn-sbud-oc-store oc))
            (fn-sn-identity-sequencep
             (fn-sbud-oc-store (fn-ocfg-step oc '(:complete) fn-arena))))
   :hints (("Goal" :in-theory
            '(fn-ocfg-step fn-ocfg-complete fn-own-complete fn-sbud-oc-store
              fn-own-refresh-keeps-fields fn-own-store-of-fn-own-make
              fn-ocfg-owner-of-fn-ocfg-make
              fn-sn-finish-preserves-identity-sequence car-cons
              (:executable-counterpart car) (:executable-counterpart equal))))))

(defthm fn-owner-finish-synced-preserves-cursor
  (implies (and (fn-sn-identity-sequencep (fn-owner-store state))
                (fn-prc-carryp (fn-owner-retain-carry state))
                (fn-hist-of-storep fn-hist (fn-owner-store state)))
           (fn-sn-identity-sequencep
            (fn-owner-store
             (mv-nth 2 (fn-owner-finish-synced fn-hist state)))))
  :hints (("Goal" :use ((:instance fn-owner-reference-completion-preserves-cursor
                                           (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-cursor-store-by-definition
             fn-owner-core-is-configured-owner-by-definition fn-sbud-oc-store
             fn-owner-finish-synced fn-owner-reference-completion-preserves-cursor
             fn-irc-rix-ocfg-complete-of-refresh-is-ocfg-step-complete-by-definition
             fn-owner-ocfg-of-retain-carry-put fn-owner-ocfg-of-install-ocfg
             mv-nth nth zp car-cons cdr-cons
             (:executable-counterpart zp) (:executable-counterpart binary-+)
             (:executable-counterpart unary--)))))

(local
 (defthm fn-owner-cursor-open-kind-implies-okp
   (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier records)) :ok)
            (fn-sn-open-okp (fn-cpo-open-observed configs frontier records)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-cpo-open-observed fn-sn-open-kind fn-sn-open-state
               fn-sn-open-okp fn-sn-open-shapep fn-sn-open-ok fn-sn-open-error
               len car-cons cdr-cons))))))

(local
 (defthm fn-owner-cursor-recovered-full-has-retained-fields
   (implies (not (equal (fn-ock-recover-full configs frontier records max-conns) :fault))
            (fn-osr-retainedp
             (fn-sbud-oc-store (fn-ock-recover-full configs frontier records max-conns))))
   :hints (("Goal" :use fn-osr-open-establishes-full-retained-carry
            :in-theory
            '(fn-ock-recover-full fn-ock-install fn-sbud-oc-store
              fn-own-configure fn-own-start fn-own-refresh-keeps-fields
              fn-own-store-of-fn-own-make fn-ocfg-owner-of-fn-ocfg-make
              fn-owner-cursor-open-kind-implies-okp)))))

(defthm fn-owner-recovery-establishes-retained-store
  (let ((oc (fn-ock-recover-extended
             (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
             configs frontier max-conns)))
    (implies (not (equal oc :fault))
             (fn-osr-retainedp (fn-sbud-oc-store oc))))
  :hints (("Goal" :in-theory
           '(fn-owner-recover-from-checkpoint-equals-full-recover
             fn-owner-cursor-recovered-full-has-retained-fields))))

(local
 (defthm fn-owner-cursor-retained-implies-sequence
   (implies (fn-osr-retainedp s) (fn-sn-identity-sequencep s))
   :hints (("Goal" :in-theory '(fn-osr-retainedp fn-osr-livep
                                fn-sti-livep fn-csi-livep)))))

; The owner binding through the cold entry and the reclaim swap: the
; report writer's bracket (fn-orc-writer-enter/-leave) and every other put
; leave it; the install sets it.
(local
 (defthm fn-ocd-writer-owner-frame
   (and (equal (get-global 'fn-owner (fn-orc-writer-enter state))
               (get-global 'fn-owner state))
        (equal (get-global 'fn-owner (fn-orc-writer-leave state))
               (get-global 'fn-owner state)))
   :hints (("Goal" :in-theory (enable fn-orc-writer-enter fn-orc-writer-leave)))))

(local
 (defthm fn-ocd-get-owner-of-other-put
   (implies (not (equal key 'fn-owner))
            (equal (get-global 'fn-owner (put-global key value state))
                   (get-global 'fn-owner state)))
   :hints (("Goal" :in-theory (enable get-global put-global)))))

(local
 (defthm fn-ocd-get-owner-of-retain-carry-put
   (equal (get-global 'fn-owner (fn-owner-retain-carry-put carry state))
          (get-global 'fn-owner state))
   :hints (("Goal" :in-theory (enable fn-owner-retain-carry-put)))))

(local
 (defthm fn-ocd-get-owner-of-open-install
   (equal (get-global 'fn-owner (fn-owner-install-open-ocfg oc state)) oc)
   :hints (("Goal" :in-theory (enable fn-owner-install-open-ocfg fn-owner-install-ocfg)))))

; This is the unchanged Store pointer installed by the actual cold entry.
(defthm fn-owner-install-extended-store-effect-by-definition
  (implies (and (not (equal oc :fault)) (fn-onb-open-okp (fn-ocfg-owner oc)))
           (equal (fn-owner-store
                   (mv-nth 5 (fn-owner-install-extended
                              oc extended key fn-arena fn-cat fn-hist state)))
                  (fn-sbud-oc-store oc)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-owner-install-extended fn-owner-cursor-store-by-definition
              fn-owner-ocfg fn-ocd-writer-owner-frame fn-ocd-get-owner-of-other-put
              fn-ocd-get-owner-of-retain-carry-put fn-ocd-get-owner-of-open-install
              mv-nth nth zp car-cons cdr-cons)))))

(defthm fn-owner-recovered-install-establishes-cursor
  (let ((oc (fn-ock-recover-extended
             (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
             configs frontier max-conns)))
    (implies (and (not (equal oc :fault)) (fn-onb-open-okp (fn-ocfg-owner oc)))
             (fn-sn-identity-sequencep
              (fn-owner-store
               (mv-nth 5 (fn-owner-install-extended
                          oc extended key fn-arena fn-cat fn-hist state))))))
  :hints (("Goal" :in-theory '(fn-owner-install-extended-store-effect-by-definition
                               fn-owner-recovery-establishes-retained-store
                               fn-owner-cursor-retained-implies-sequence))))

(local
 (defthm fn-ocd-get-owner-of-install
   (equal (get-global 'fn-owner (fn-owner-install-ocfg oc state)) oc)
   :hints (("Goal" :in-theory (enable fn-owner-install-ocfg)))))

(local
 (defthm fn-owner-cursor-swapped-store
   (equal (fn-sbud-oc-store (fn-orcp-swapped-ocfg live-oc rebuilt-oc))
          (fn-sbud-oc-store rebuilt-oc))
   :hints (("Goal" :in-theory
            '(fn-sbud-oc-store fn-orcp-swapped-ocfg fn-orcp-swapped-owner
              fn-orcp-swap-base fn-own-set-conns fn-own-store-of-fn-own-make
              fn-ocfg-owner-of-fn-ocfg-make)))))

(defthm fn-owner-orcp-swap-store-effect-by-definition
  (equal (fn-owner-store (mv-nth 2 (fn-owner-orcp-swap rebuilt state)))
         (fn-sbud-oc-store (nth 1 rebuilt)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-owner-orcp-swap fn-owner-cursor-store-by-definition
              fn-owner-put-credits fn-owner-ocfg fn-ocd-get-owner-of-other-put
              fn-ocd-get-owner-of-retain-carry-put fn-ocd-get-owner-of-install
              fn-owner-cursor-swapped-store
              mv-nth nth zp car-cons cdr-cons)))))

(defthm fn-owner-rebuilt-swap-establishes-cursor
  (let ((rebuilt (fn-owner-orcp-rebuild (fn-sco-capture configs rows) configs frontier max-conns)))
    (implies (and (true-listp rows) (not (equal (nth 1 rebuilt) :fault)))
             (fn-sn-identity-sequencep
              (fn-owner-store (mv-nth 2 (fn-owner-orcp-swap rebuilt state))))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-owner-orcp-swap-store-effect-by-definition
              fn-owner-orcp-rebuild-of-capture-is-the-full-open
              fn-owner-cursor-recovered-full-has-retained-fields
              fn-owner-cursor-retained-implies-sequence nth zp car-cons cdr-cons)))))
