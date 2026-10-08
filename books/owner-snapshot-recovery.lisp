; Live capture/recovery correspondence.  Relations below are proof vocabulary:
; a capture takes the carried Store pointer, not a new scan of its history.
; PRF-1068 / HST-040.  This book does not assume successful observed open.
(in-package "ACL2")
(include-book "config-store-steps")
(include-book "topic-history-store-invariants")
(include-book "owner-commit-ocl")
(include-book "statement-keyring-publication")

(local (in-theory (disable (tau-system))))
; The "Theory" warning check costs about 20 ms on every :in-theory hint in this world.
(local (set-inhibit-warnings "Theory"))
; Rules of the included books that backchain through the store-event
; recognizers on every goal here; the proofs that need one name it in a hint.
(local (in-theory (disable fn-sti-local-admin-is-topic-event
                          fn-hls-kind4-disjoint-from-other-store-events
                          fn-scram-printable-facts fn-dl-th-progress
                          fn-snt-topic-event-is-not-hstxa fn-sf-fenced-rejects-success
                          fn-th-topic-event-is-not-stxe fn-th-topic-event-is-not-stxk)))

; Identity replay decisions do not consult their accumulated verdict list.
; The live completion context deliberately omits that list.  Preserve every
; decision-relevant field, including the fault reason, across this boundary.
(defun fn-osr-context-view (ctx)
  (declare (xargs :guard t))
  (list (fn-stxk-context-kind ctx) (fn-stxk-context-next ctx)
        (fn-stxk-context-snapshots ctx)
        (fn-stxk-context-current-generation ctx)
        (fn-stxk-context-tail ctx)))

(defthm fn-osr-context-view-of-context-by-definition
  (equal (fn-osr-context-view
          (fn-stxk-context kind next snapshots verdicts generation tail))
         (list kind next snapshots generation tail))
  :hints (("Goal" :in-theory (enable fn-osr-context-view fn-stxk-context))))

(defthm fn-osr-context-view-snapshot-congruence
  (implies (equal (fn-osr-context-view a) (fn-osr-context-view b))
           (equal (fn-osr-context-view (fn-stxk-apply-snapshot a event))
                  (fn-osr-context-view (fn-stxk-apply-snapshot b event))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-osr-context-view)
                              (:definition fn-stxk-apply-snapshot) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:definition natp) (:executable-counterpart car)
                              (:executable-counterpart cons) (:executable-counterpart equal)
                              (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal))))))

(defthm fn-osr-context-view-verdict-congruence
  (implies (equal (fn-osr-context-view a) (fn-osr-context-view b))
           (equal (fn-osr-context-view (fn-stxk-apply-verdict a event))
                  (fn-osr-context-view (fn-stxk-apply-verdict b event))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-osr-context-view)
                              (:definition fn-stxk-apply-verdict) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:executable-counterpart car) (:executable-counterpart cons)
                              (:executable-counterpart equal) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite cons-equal))))))

(defthm fn-osr-context-view-step-congruence
  (implies (equal (fn-osr-context-view a) (fn-osr-context-view b))
           (equal (fn-osr-context-view (fn-replay-identity-step a event))
                  (fn-osr-context-view (fn-replay-identity-step b event))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-osr-context-view)
                              (:definition fn-replay-apply-carried-verdict)
                              (:definition fn-replay-apply-revoked-verdict)
                              (:definition fn-replay-identity-advance)
                              (:definition fn-replay-identity-step)
                              (:definition fn-stxk-apply-snapshot)
                              (:definition fn-stxk-apply-verdict) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:definition natp) (:definition nfix) (:definition not)
                              (:executable-counterpart car) (:executable-counterpart cons)
                              (:executable-counterpart equal)
                              (:forward-chaining fn-hsig-article-event-carried-bindsp-facts)
                              (:forward-chaining fn-hsig-article-event-revoked-bindsp-facts)
                              (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal)
                              (:rewrite fn-hsig-article-event-revoked-is-not-carried)
                              (:type-prescription fn-hsig-article-event-carried-bindsp)
                              (:type-prescription fn-hsig-article-event-revoked-bindsp)
                              (:type-prescription fn-stxe-p) (:type-prescription fn-stxk-p))))))

; The carry relates the independently replayed identity prefix to the live
; completion context.  It does not mention the configured article replay and
; does not hide open success inside a predicate.
(defun fn-osr-identity-prefixp (s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((n (fn-sn-identity-next s))
         (records (fn-sf-records (fn-sn-files s)))
         (ctx (fn-replay-identity (take n records))))
    (and (natp n) (<= n (len records))
         (equal (fn-stxk-context-kind ctx) :ok)
         (equal (fn-osr-context-view ctx)
                (fn-osr-context-view (fn-sn-identity-context s))))))

(defthm fn-osr-initial-identity-prefix
  (fn-osr-identity-prefixp (fn-sn-initial groups capacity))
  :hints (("Goal" :in-theory
           (enable fn-osr-identity-prefixp fn-osr-context-view
                   fn-sn-initial fn-sn-identity-context
                   fn-sn-identity-next fn-sn-keyring-snapshots fn-sn-files
                   fn-sn-make-v2 fn-store-event-nth fn-sf-initial-state
                   fn-replay-identity fn-replay-identity-loop
                   fn-stxk-initial-context fn-stxk-context))))

; Guard-verified O(1) capture: return the existing pointer.  The producer's
; quiescent ownership/pin discipline supplies its lifetime, outside ACL2.
(defun fn-osr-capture (s)
  (declare (xargs :guard t))
  s)

(defthm fn-osr-capture-is-carried-store-by-definition
  (equal (fn-osr-capture s) s)
  :hints (("Goal" :in-theory (enable fn-osr-capture))))

(in-theory (disable fn-osr-context-view fn-osr-identity-prefixp fn-osr-capture))

(defun fn-osr-context-canonicalp (ctx)
  (declare (xargs :guard t))
  (and (equal (fn-stxk-context-current-generation ctx)
              (if (consp (fn-stxk-context-snapshots ctx))
                  (fn-stxk-keyring-generation
                   (car (fn-stxk-context-snapshots ctx)))
                nil))
       (equal (fn-stxk-context-tail ctx) nil)))

(defthm fn-osr-step-preserves-canonical-context
  (implies (and (fn-osr-context-canonicalp ctx)
                (equal (fn-stxk-context-kind ctx) :ok)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-step ctx event)) :ok))
           (fn-osr-context-canonicalp (fn-replay-identity-step ctx event)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-context-canonicalp)
                              (:definition fn-replay-apply-carried-verdict)
                              (:definition fn-replay-apply-revoked-verdict)
                              (:definition fn-replay-identity-advance)
                              (:definition fn-replay-identity-step)
                              (:definition fn-stxk-apply-snapshot)
                              (:definition fn-stxk-apply-verdict) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:definition natp) (:definition nfix) (:definition not)
                              (:executable-counterpart binary-+) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart equal) (:executable-counterpart natp)
                              (:executable-counterpart not) (:rewrite car-cons)
                              (:rewrite cdr-cons)
                              (:rewrite fn-hsig-article-event-revoked-is-not-carried)
                              (:type-prescription fn-hsig-article-event-carried-bindsp)
                              (:type-prescription fn-hsig-article-event-revoked-bindsp)
                              (:type-prescription fn-hsig-article-event-snapshot-bindsp)
                              (:type-prescription fn-hsig-revoked-tombstone-bindsp)
                              (:type-prescription fn-osr-context-canonicalp)
                              (:type-prescription fn-stmt-okp)
                              (:type-prescription fn-stxa-bindsp) (:type-prescription fn-stxa-p)
                              (:type-prescription fn-stxe-p) (:type-prescription fn-stxk-p)
                              (:type-prescription fn-stxk-same-snapshotp))))))

(defthm fn-osr-loop-ok-implies-input-ok
  (implies (equal (fn-stxk-context-kind
                  (fn-replay-identity-loop records ctx)) :ok)
           (equal (fn-stxk-context-kind ctx) :ok))
  :hints (("Goal" :induct (fn-replay-identity-loop records ctx)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-replay-identity-loop)
                              (:definition fn-replay-identity-step)
                              (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:definition not) (:definition null)
                              (:executable-counterpart cons) (:executable-counterpart consp)
                              (:executable-counterpart equal)
                              (:induction fn-replay-identity-loop) (:rewrite car-cons)
                              (:type-prescription fn-store-event-p))))))

(defthm fn-osr-loop-preserves-canonical-context
  (implies (and (fn-osr-context-canonicalp ctx)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-loop records ctx)) :ok))
           (fn-osr-context-canonicalp
            (fn-replay-identity-loop records ctx)))
  :hints (("Goal" :induct (fn-replay-identity-loop records ctx)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-replay-identity-loop)
                              (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:definition not) (:definition null)
                              (:executable-counterpart cons) (:executable-counterpart consp)
                              (:executable-counterpart equal)
                              (:induction fn-replay-identity-loop) (:rewrite car-cons)
                              (:rewrite fn-osr-step-preserves-canonical-context)
                              (:type-prescription fn-osr-context-canonicalp)
                              (:type-prescription fn-store-event-p))))
          ("Subgoal *1/2"
           :use ((:instance fn-osr-loop-ok-implies-input-ok
                            (records (cdr records))
                            (ctx (fn-replay-identity-step ctx (car records))))
                 fn-osr-loop-ok-implies-input-ok
                 (:instance fn-osr-step-preserves-canonical-context
                            (event (car records)))))))

(defthm fn-osr-identity-ok-has-canonical-context
  (implies (equal (fn-stxk-context-kind (fn-replay-identity records)) :ok)
           (fn-osr-context-canonicalp (fn-replay-identity records)))
  :hints (("Goal" :use ((:instance fn-osr-loop-preserves-canonical-context
                                  (ctx (fn-stxk-initial-context 0))))
           :in-theory (e/d (fn-replay-identity fn-stxk-initial-context
                            fn-stxk-context fn-osr-context-canonicalp)
                           (fn-replay-identity-loop
                            fn-osr-loop-preserves-canonical-context)))))

(defthm fn-osr-identity-loop-append
  (implies (and (true-listp records)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-loop records ctx)) :ok))
           (equal (fn-replay-identity-loop (append records suffix) ctx)
                  (fn-replay-identity-loop
                   suffix (fn-replay-identity-loop records ctx))))
  :hints (("Goal" :induct (fn-replay-identity-loop records ctx)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition binary-append) (:definition fn-replay-identity-loop)
                              (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:definition not) (:definition null) (:definition true-listp)
                              (:executable-counterpart cons) (:executable-counterpart consp)
                              (:executable-counterpart equal) (:executable-counterpart not)
                              (:executable-counterpart true-listp)
                              (:induction fn-replay-identity-loop) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite fn-cp-append-nil-left)
                              (:type-prescription fn-store-event-p))))))

(defthm fn-osr-identity-append-one
  (implies (and (true-listp records)
                (equal (fn-stxk-context-kind (fn-replay-identity records)) :ok)
                (fn-store-event-p event))
           (equal (fn-replay-identity (append records (list event)))
                  (fn-replay-identity-step (fn-replay-identity records) event)))
  :hints (("Goal" :use ((:instance fn-osr-identity-loop-append
                                  (ctx (fn-stxk-initial-context 0))
                                  (suffix (list event))))
           :in-theory
           (e/d (fn-replay-identity fn-replay-identity-loop)
                (fn-replay-identity-step fn-store-event-p
                 fn-osr-identity-loop-append)))))

(in-theory (disable fn-osr-context-canonicalp))


(defthm fn-osr-identity-context-of-update-by-definition
  (equal (fn-sn-identity-context (fn-sn-update s files node)) (fn-sn-identity-context s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-context fn-sn-update)
                (fn-sn-make-v6)))))

(defthm fn-osr-identity-context-of-with-topic-by-definition
  (equal (fn-sn-identity-context (fn-sn-with-topic s topic)) (fn-sn-identity-context s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-context fn-sn-with-topic)
                (fn-sn-make-v6)))))

(defthm fn-osr-identity-context-of-with-consumer-by-definition
  (equal (fn-sn-identity-context (fn-sn-with-consumer s consumer)) (fn-sn-identity-context s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-context fn-sn-with-consumer)
                (fn-sn-make-v6)))))

(defthm fn-osr-identity-context-of-with-event-index-by-definition
  (equal (fn-sn-identity-context (fn-sn-with-event-index s index)) (fn-sn-identity-context s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-context fn-sn-with-event-index)
                (fn-sn-make-v6)))))

(local
 (defthm fn-osr-cdr-update-nth
   (equal (cdr (update-nth n v x))
          (if (zp n) (cdr x) (update-nth (+ -1 n) v (cdr x))))
   :hints (("Goal" :in-theory (enable update-nth)))))
(local
 (defthm fn-osr-car-update-nth
   (equal (car (update-nth n v x)) (if (zp n) v (car x)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(defthm fn-osr-identity-context-of-with-configuration
  (equal (fn-sn-identity-context (fn-sn-with-configuration s groups capacity node configs)) (fn-sn-identity-context s))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-sn-identity-context)
                              (:definition fn-sn-identity-next)
                              (:definition fn-sn-keyring-snapshots)
                              (:definition fn-sn-with-configuration) (:definition update-nth)
                              (:executable-counterpart binary-+) (:executable-counterpart zp)
                              (:rewrite car-cons) (:rewrite cdr-cons)
                              (:rewrite fn-osr-car-update-nth) (:rewrite fn-osr-cdr-update-nth))))))

; Publication and preparation preserve the completed identity prefix.
(defthm fn-osr-io-preserves-identity-prefix
  (implies (and (fn-sn-statep s)
                (fn-osr-identity-prefixp s))
           (fn-osr-identity-prefixp (fn-sn-io s operation result)))
  :hints (("Goal"
           :use ((:instance fn-csi-take-append-after-prefix
                    (n (fn-sn-identity-next s))
                    (records (fn-sf-records (fn-sn-files s)))
                    (suffix (list (fn-sf-record-candidate (fn-sn-files s))))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:compound-recognizer zp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-frontier-dir-result)
                              (:definition fn-sf-frontier-file-result)
                              (:definition fn-sf-frontier-replace-result)
                              (:definition fn-sf-record-dir-result)
                              (:definition fn-sf-record-file-result)
                              (:definition fn-sf-record-link-result)
                              (:definition fn-sf-record-pair)
                              (:definition fn-sf-recovery-barrier)
                              (:definition fn-sf-start-frontier) (:definition fn-sn-file-step)
                              (:definition fn-sn-io) (:definition fn-stxk-context-kind)
                              (:definition natp) (:definition not) (:definition take)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-replay-identity)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-ocl-length-after-appended-config)
                              (:rewrite fn-osr-identity-context-of-update-by-definition)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-snoc)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep) (:type-prescription len))))))

(defthm fn-osr-prepare-consumer-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-candidatep) (:definition fn-sf-prepare-record)
                              (:definition fn-sn-prepare-consumer)
                              (:definition fn-stxk-context-kind) (:definition natp)
                              (:executable-counterpart equal)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-identity-context-of-update-by-definition)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-scalars-of-fn-sf-make-fields)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep))))))

(defthm fn-osr-prepare-article-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare s record)))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-candidatep) (:definition fn-sf-prepare-record)
                              (:definition fn-sn-prepare) (:definition fn-stxk-context-kind)
                              (:definition natp) (:executable-counterpart equal)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-held-kind-facts)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-identity-context-of-update-by-definition)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-scalars-of-fn-sf-make-fields)
                              (:type-prescription fn-held-p)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep))))))

(defthm fn-osr-prepare-retention-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-candidatep) (:definition fn-sf-prepare-record)
                              (:definition fn-sn-prepare-retention)
                              (:definition fn-stxk-context-kind) (:definition natp)
                              (:executable-counterpart equal)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-identity-context-of-update-by-definition)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-scalars-of-fn-sf-make-fields)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep))))))

(defthm fn-osr-prepare-identity-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare-identity s event)))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-candidatep) (:definition fn-sf-prepare-record)
                              (:definition fn-sn-prepare-identity)
                              (:definition fn-stxk-context-kind) (:definition natp)
                              (:executable-counterpart equal)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-identity-context-of-update-by-definition)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-scalars-of-fn-sf-make-fields)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep))))))

(defthm fn-osr-prepare-topic-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-candidatep) (:definition fn-sf-prepare-record)
                              (:definition fn-sn-prepare-topic)
                              (:definition fn-stxk-context-kind) (:definition fn-th-at)
                              (:definition natp) (:executable-counterpart equal)
                              (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-identity-context-of-update-by-definition)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-scalars-of-fn-sf-make-fields)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep))))))

(defthm fn-osr-refuse-reservation-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-refuse-reservation)
                              (:definition fn-sn-refuse-reservation)
                              (:definition fn-stxk-context-kind) (:definition natp)
                              (:executable-counterpart equal)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-identity-context-of-update-by-definition)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:type-prescription fn-osr-identity-prefixp))))))

(defthm fn-osr-known-abort-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-known-abort s)))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-abort-completion)
                              (:definition fn-sf-prepublish-abort)
                              (:definition fn-sf-record-file-result)
                              (:definition fn-sf-record-pair) (:definition fn-sn-known-abort)
                              (:definition fn-sn-known-abort-file-start)
                              (:definition fn-sn-known-abort-files)
                              (:definition fn-stxk-context-kind) (:definition natp)
                              (:executable-counterpart equal)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-held-kind-facts)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-identity-context-of-update-by-definition)
                              (:rewrite fn-sf-records-field-of-fn-sf-make-fields)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-scalars-of-fn-sf-make-fields)
                              (:rewrite fn-sf-successes-field-of-fn-sf-make-fields)
                              (:type-prescription fn-held-p)
                              (:type-prescription fn-osr-identity-prefixp))))))

(defthm fn-osr-live-identity-context-is-canonical
  (fn-osr-context-canonicalp (fn-sn-identity-context s))
  :hints (("Goal" :in-theory (enable fn-osr-context-canonicalp
                                     fn-sn-identity-context fn-stxk-context))))

(defthm fn-osr-finish-identity-context
  (implies (equal (fn-stxk-context-kind
                   (fn-replay-identity-step (fn-sn-identity-context s) record))
                  :ok)
           (equal (fn-osr-context-view
                   (fn-sn-identity-context
                    (fn-sn-finish-identity s files record node)))
                  (fn-osr-context-view
                   (fn-replay-identity-step (fn-sn-identity-context s) record))))
  :hints (("Goal"
           :use ((:instance fn-osr-step-preserves-canonical-context
                            (ctx (fn-sn-identity-context s)) (event record)))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-osr-context-canonicalp)
                              (:definition fn-osr-context-view) (:definition fn-sn-event-index)
                              (:definition fn-sn-finish-identity)
                              (:definition fn-sn-identity-context) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-p)
                              (:definition nfix) (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart equal) (:rewrite car-cons)
                              (:rewrite cdr-cons)
                              (:rewrite fn-hls-snapshot-is-no-retained-composite)
                              (:rewrite fn-osr-live-identity-context-is-canonical)
                              (:rewrite fn-sn-fields-of-fn-sn-make-v6)
                              (:type-prescription fn-record-uint32p)
                              (:type-prescription fn-stxe-bounded-octetsp)
                              (:type-prescription fn-stxk-shapep))))))

(defthm fn-osr-neutral-step-is-advance
  (implies (and (equal (fn-stxk-context-kind ctx) :ok)
                (equal (fn-store-event-sequence event) (fn-stxk-context-next ctx))
                (not (fn-hstxa-p event)) (not (fn-stxa-p event))
                (not (fn-stxe-p event)) (not (fn-stxk-p event)))
           (equal (fn-replay-identity-step ctx event)
                  (fn-replay-identity-advance ctx)))
  :hints (("Goal" :in-theory
           (e/d (fn-replay-identity-step fn-replay-identity-wire
                 fn-hsig-article-event-carried-bindsp
                 fn-hsig-article-event-revoked-bindsp)
                (fn-stxa-p fn-stxe-p fn-stxk-p fn-hstxa-p
                 fn-replay-identity-advance fn-stxk-apply-verdict
                 fn-stxk-apply-snapshot fn-stxk-fault
                 fn-record-shape-vocabulary fn-record-record-vocabulary)))))
(in-theory (disable fn-osr-neutral-step-is-advance))

(defthm fn-osr-neutral-retained-event-is-not-wire-composite
  (implies (and (fn-store-event-p event)
                (not (fn-stxe-p event)) (not (fn-stxk-p event))
                (not (fn-hstxa-p event)))
           (not (fn-stxa-p event)))
  :hints (("Goal" :use ((:instance fn-stxa-p-forward-shape (x event))
                        (:instance fn-held-p-forward-shape (x event)))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-cpe-eventp) (:definition fn-held-shapep)
                              (:definition fn-store-event-p)
                              (:definition fn-store-retention-event-p)
                              (:definition fn-stxa-shapep)
                              (:definition fn-th-local-admin-eventp)
                              (:definition fn-th-topic-eventp) (:definition not)
                              (:executable-counterpart equal)
                              (:forward-chaining fn-bs-stxa-is-a-cons)
                              (:forward-chaining fn-stxa-p-forward-shape)
                              (:type-prescription fn-stxa-p))))))

(local
 (defun fn-osr-nth-history-induct (n records sequence lower frontier)
   (declare (xargs :measure (len records)))
   (if (or (zp n) (atom records)) (list sequence lower frontier)
     (fn-osr-nth-history-induct
      (1- n) (cdr records) (1+ sequence)
      (1+ (fn-store-event-txid (car records))) frontier))))

(defthm fn-osr-history-nth-event-sequence
  (implies (and (fn-sf-record-listp records sequence lower frontier)
                (natp n) (< n (len records)))
           (and (fn-store-event-p (nth n records))
                (equal (fn-store-event-sequence (nth n records))
                       (+ sequence n))))
  :hints (("Goal" :induct (fn-osr-nth-history-induct n records sequence lower frontier)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:compound-recognizer zp-compound-recognizer) (:definition atom)
                              (:definition fix) (:definition fn-sf-record-listp)
                              (:definition len) (:definition natp) (:definition not)
                              (:definition nth) (:definition synp) (:elim car-cdr-elim)
                              (:executable-counterpart <) (:executable-counterpart binary-+)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fix)
                              (:executable-counterpart fn-store-event-p)
                              (:executable-counterpart fn-store-event-sequence)
                              (:executable-counterpart integerp) (:executable-counterpart len)
                              (:executable-counterpart not) (:executable-counterpart zp)
                              (:induction fn-osr-nth-history-induct)
                              (:rewrite associativity-of-+) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite commutativity-2-of-+)
                              (:rewrite commutativity-of-+) (:rewrite default-+-2)
                              (:rewrite fold-consts-in-+) (:rewrite unicity-of-0)
                              (:type-prescription fn-replay-record-counters-are-natural . 1)
                              (:type-prescription fn-sf-record-listp)
                              (:type-prescription fn-store-event-p) (:type-prescription len))))))

(local
 (defthm fn-osr-file-state-has-record-list
   (implies (fn-sf-statep files)
            (fn-sf-record-listp (fn-sf-records files) 0 0 (fn-sf-frontier files)))
   :hints (("Goal" :in-theory '(fn-sf-statep)))))

(defthm fn-osr-enabled-completion-is-next-event
  (implies (and (fn-csi-livep s) (fn-sn-completion-enabledp s))
           (and (fn-store-event-p (fn-sn-completion-record s))
                (equal (fn-store-event-sequence (fn-sn-completion-record s))
                       (fn-sn-identity-next s))))
  :hints (("Goal"
           :use (fn-csi-enabled-phase-by-definition
                 (:instance fn-osr-history-nth-event-sequence
                            (n (fn-sn-identity-next s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (sequence 0) (lower 0)
                            (frontier (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer) (:definition fix)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-sn-identity-sequencep) (:definition natp)
                              (:definition not) (:executable-counterpart equal)
                              (:executable-counterpart fix)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:forward-chaining fn-ccar-completion-enabled-implies-statep)
                              (:forward-chaining fn-cstp-sn-statep-files) (:rewrite default-+-2)
                              (:rewrite fn-csi-enabled-phase-by-definition)
                              (:rewrite fn-osr-file-state-has-record-list)
                              (:rewrite unicity-of-0)
                              (:type-prescription fn-replay-record-counters-are-natural . 1)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-store-event-p) (:type-prescription len))))))
(in-theory (disable fn-osr-enabled-completion-is-next-event))

(defthm fn-osr-retention-is-identity-neutral
  (implies (fn-store-retention-event-p event)
           (and (not (fn-stxe-p event)) (not (fn-stxk-p event))
                (not (fn-hstxa-p event))))
  :hints (("Goal"
           :use ((:instance fn-stxe-p-forward-shape (x event))
                 (:instance fn-stxk-p-forward-shape (x event))
                 (:instance fn-hstxa-p-forward-shape (x event)))
           :in-theory
           (e/d (fn-store-retention-event-p fn-store-event-nth
                 fn-stxe-shapep fn-stxk-shapep)
                (fn-stxe-p fn-stxk-p fn-hstxa-p)))))

; The wire-recognizer case is read off the enabledness definition; the neutral
; case is the advance step.  Neither opens the definition whole.
(local
 (defthm fn-osr-eis-wire-case
   (implies (and (fn-sn-completion-enabledp s)
                 (or (fn-stxe-p (fn-sn-completion-record s))
                     (fn-stxk-p (fn-sn-completion-record s))
                     (fn-hstxa-p (fn-sn-completion-record s))))
            (equal (fn-stxk-context-kind
                    (fn-replay-identity-step
                     (fn-sn-identity-context s) (fn-sn-completion-record s))) :ok))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-osr-retention-is-identity-neutral
                             (event (fn-sn-completion-record s))))
            :expand ((fn-sn-completion-enabledp s)
                     (fn-sn-completion-core-enabledp s))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-osr-eis-neutral-case
   (implies (and (fn-csi-livep s) (fn-sn-completion-enabledp s)
                 (not (fn-stxe-p (fn-sn-completion-record s)))
                 (not (fn-stxk-p (fn-sn-completion-record s)))
                 (not (fn-hstxa-p (fn-sn-completion-record s))))
            (equal (fn-stxk-context-kind
                    (fn-replay-identity-step
                     (fn-sn-identity-context s) (fn-sn-completion-record s))) :ok))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-osr-enabled-completion-is-next-event
                  (:instance fn-osr-neutral-retained-event-is-not-wire-composite
                             (event (fn-sn-completion-record s)))
                  (:instance fn-osr-neutral-step-is-advance
                             (ctx (fn-sn-identity-context s))
                             (event (fn-sn-completion-record s))))
            :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-replay-identity-advance)
                              (:definition fn-sn-identity-context) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-verdicts) (:definition nfix)
                              (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart equal) (:executable-counterpart not)
                              (:rewrite car-cons) (:rewrite cdr-cons)
                              (:rewrite fn-osr-neutral-retained-event-is-not-wire-composite)
                              (:type-prescription fn-csi-livep)
                              (:type-prescription fn-replay-record-counters-are-natural . 1)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-store-event-p)))))))

(defthm fn-osr-enabled-identity-step-ok
  (implies (and (fn-csi-livep s) (fn-sn-completion-enabledp s))
           (equal (fn-stxk-context-kind
                   (fn-replay-identity-step
                    (fn-sn-identity-context s) (fn-sn-completion-record s))) :ok))
  :hints (("Goal"
           :use (fn-osr-eis-wire-case fn-osr-eis-neutral-case)
           :in-theory (theory 'minimal-theory))))

(defthm fn-osr-consumer-is-not-retained-composite
  (implies (fn-cpe-eventp event) (not (fn-hstxa-p event)))
  :hints (("Goal" :use ((:instance fn-hstxa-p-forward-shape (x event)))
           :in-theory (e/d (fn-cpe-eventp) (fn-hstxa-p)))))

(defthm fn-osr-live-context-fields-by-definition
  (and (equal (fn-stxk-context-kind (fn-sn-identity-context s)) :ok)
       (equal (fn-stxk-context-next (fn-sn-identity-context s))
              (fn-sn-identity-next s)))
  :hints (("Goal" :in-theory (enable fn-sn-identity-context fn-stxk-context))))

(defthm fn-osr-identity-context-of-update-indexed-by-definition
  (equal (fn-sn-identity-context (fn-sn-update-indexed s files node index))
         (fn-sn-identity-context s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-context fn-sn-update-indexed) (fn-sn-make-v6)))))

(defthm fn-osr-identity-context-of-update-accepted-by-definition
  (equal (fn-sn-identity-context
          (fn-sn-update-accepted s files node index msgid verdict))
         (fn-sn-identity-context s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-context fn-sn-update-accepted) (fn-sn-make-v6)))))

(defthm fn-osr-advance-context-view-by-definition
  (equal (fn-osr-context-view
          (fn-sn-identity-context (fn-sn-advance-identity-next s)))
         (fn-osr-context-view
          (fn-replay-identity-advance (fn-sn-identity-context s))))
  :hints (("Goal" :in-theory
           (e/d (fn-osr-context-view fn-sn-identity-context
                 fn-sn-advance-identity-next fn-replay-identity-advance
                 fn-stxk-context) (fn-sn-make-v6)))))

(defthm fn-osr-finish-context-view
  (implies (and (fn-csi-livep s) (fn-sn-completion-enabledp s))
           (equal (fn-osr-context-view
                   (fn-sn-identity-context (fn-sn-finish s)))
                  (fn-osr-context-view
                   (fn-replay-identity-step
                    (fn-sn-identity-context s) (fn-sn-completion-record s)))))
  :hints (("Goal"
           :use (fn-osr-enabled-completion-is-next-event
                 fn-osr-enabled-identity-step-ok
                 (:instance fn-osr-neutral-retained-event-is-not-wire-composite
                            (event (fn-sn-completion-record s)))
                 (:instance fn-osr-neutral-step-is-advance
                            (ctx (fn-sn-identity-context s))
                            (event (fn-sn-completion-record s))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-sn-finish) (:definition fn-stxk-context-kind)
                              (:definition not) (:executable-counterpart equal)
                              (:executable-counterpart not)
                              (:rewrite fn-cpe-is-disjoint-from-old-event-kinds-by-shape)
                              (:rewrite fn-csi-topic-event-is-not-consumer-event)
                              (:rewrite fn-hls-retained-kind4-disjoint-from-other-store-events)
                              (:rewrite fn-hls-snapshot-disjoint-from-other-store-events)
                              (:rewrite fn-hls-snapshot-is-no-retained-composite)
                              (:rewrite fn-hstxa-is-no-wire-event)
                              (:rewrite fn-osr-advance-context-view-by-definition)
                              (:rewrite fn-osr-consumer-is-not-retained-composite)
                              (:rewrite fn-osr-finish-identity-context)
                              (:rewrite fn-osr-identity-context-of-update-accepted-by-definition)
                              (:rewrite fn-osr-identity-context-of-update-indexed-by-definition)
                              (:rewrite fn-osr-identity-context-of-with-consumer-by-definition)
                              (:rewrite fn-osr-identity-context-of-with-topic-by-definition)
                              (:rewrite fn-osr-live-context-fields-by-definition)
                              (:rewrite fn-osr-retention-is-identity-neutral)
                              (:rewrite fn-snt-topic-event-is-not-hstxa)
                              (:rewrite fn-sti-consumer-event-is-not-topic)
                              (:rewrite fn-sti-retention-event-is-not-topic)
                              (:rewrite fn-th-topic-event-is-not-stxa)
                              (:rewrite fn-th-topic-event-is-not-stxe)
                              (:rewrite fn-th-topic-event-is-not-stxk)
                              (:type-prescription fn-cpe-eventp)
                              (:type-prescription fn-csi-livep) (:type-prescription fn-hstxa-p)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-store-event-p)
                              (:type-prescription fn-store-retention-event-p)
                              (:type-prescription fn-stxe-p) (:type-prescription fn-stxk-p)
                              (:type-prescription fn-th-topic-eventp))))))

(defthm fn-osr-step-kind-congruence
  (implies (equal (fn-osr-context-view a) (fn-osr-context-view b))
           (equal (fn-stxk-context-kind (fn-replay-identity-step a event))
                  (fn-stxk-context-kind (fn-replay-identity-step b event))))
  :rule-classes nil
  :hints (("Goal" :use fn-osr-context-view-step-congruence
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-osr-context-view)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail) (:definition not)
                              (:executable-counterpart equal) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite cons-equal))))))

(local
 (defthm fn-osr-fpi-enabled
   (implies (and (fn-osr-identity-prefixp s) (fn-csi-livep s) (fn-sn-completion-enabledp s))
            (fn-osr-identity-prefixp (fn-sn-finish s)))
   :rule-classes nil
   :hints (("Goal"
            :do-not '(preprocess)
            :use (fn-snt-finish-image
                  fn-sn-finish-enabled-advances-identity-next
                  fn-csi-enabled-phase-by-definition
                  fn-osr-enabled-completion-is-next-event
                  fn-osr-enabled-identity-step-ok fn-osr-finish-context-view
                  (:instance fn-csi-len-of-take
                             (n (fn-sn-identity-next s))
                             (records (fn-sf-records (fn-sn-files s))))
                  (:instance fn-csi-take-next
                             (n (fn-sn-identity-next s))
                             (records (fn-sf-records (fn-sn-files s))))
                  (:instance fn-osr-identity-append-one
                             (records (take (fn-sn-identity-next s)
                                            (fn-sf-records (fn-sn-files s))))
                             (event (fn-sn-completion-record s)))
                  (:instance fn-osr-context-view-step-congruence
                             (a (fn-replay-identity
                                 (take (fn-sn-identity-next s)
                                       (fn-sf-records (fn-sn-files s)))))
                             (b (fn-sn-identity-context s))
                             (event (fn-sn-completion-record s)))
                  (:instance fn-osr-step-kind-congruence
                             (a (fn-replay-identity
                                 (take (fn-sn-identity-next s)
                                       (fn-sf-records (fn-sn-files s)))))
                             (b (fn-sn-identity-context s))
                             (event (fn-sn-completion-record s))))
            :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:compound-recognizer zp-compound-recognizer)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sn-identity-sequencep)
                              (:definition fn-stxk-context-kind) (:definition len)
                              (:definition member-equal) (:definition natp) (:definition not)
                              (:definition nth) (:definition take)
                              (:executable-counterpart binary-+) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart consp)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-cpe-projection-replay)
                              (:executable-counterpart fn-osr-context-view)
                              (:executable-counterpart fn-replay-identity)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart zp)
                              (:forward-chaining fn-ccar-completion-enabled-implies-statep)
                              (:forward-chaining fn-ocmt-enabled-completion-is-completing)
                              (:rewrite cons-equal)
                              (:rewrite fn-csi-enabled-phase-by-definition)
                              (:rewrite fn-csi-len-of-take) (:rewrite fn-csi-take-next)
                              (:rewrite fn-cstp-minus-one-of-successor)
                              (:rewrite fn-sn-finish-enabled-advances-identity-next)
                              (:type-prescription fn-replay-record-counters-are-natural . 1)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-store-event-p) (:type-prescription len)
                              (:type-prescription take)))))))

(defthm fn-osr-finish-preserves-identity-prefix
  (implies (and (fn-osr-identity-prefixp s) (fn-csi-livep s))
           (fn-osr-identity-prefixp (fn-sn-finish s)))
  :hints (("Goal"
           :use (fn-sn-finish-disabled-is-no-op fn-osr-fpi-enabled)
           :in-theory (theory 'minimal-theory))))

(defun fn-osr-livep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp (fn-sn-config-history s))
       (fn-cst-relation s) (fn-sti-livep s) (fn-osr-identity-prefixp s)))

(defthm fn-osr-ready-has-configured-history
  (implies (and (fn-cst-relation s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (fn-cpo-history-relation s))
  :hints (("Goal" :in-theory
           (e/d (fn-cst-relation fn-cst-recoverablep fn-cst-replay-node
                 fn-cst-final-configurationp fn-cpo-history-relation
                 fn-snt-idle-phasep)
                (fn-cpr-replay fn-cpr-loop fn-sn-statep fn-sf-statep
                 fn-cnode-statep fn-node-statep)))))

(defthm fn-osr-ready-identity-exact-view
  (implies (and (fn-osr-identity-prefixp s)
                (fn-csi-livep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (and (equal (fn-stxk-context-kind
                        (fn-replay-identity (fn-sf-records (fn-sn-files s)))) :ok)
                (equal (fn-osr-context-view
                        (fn-replay-identity (fn-sf-records (fn-sn-files s))))
                       (fn-osr-context-view (fn-sn-identity-context s)))))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list
                            (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                            (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sn-identity-sequencep)
                              (:definition fn-stxk-context-kind) (:definition natp)
                              (:definition not) (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:rewrite fn-sf-state-records-are-true-list)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep))))))

(defthm fn-osr-ready-topic-exact
  (implies (and (fn-sti-livep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (equal (fn-th-prefix-project (fn-sf-records (fn-sn-files s)))
                  (fn-sn-topic s)))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list
                            (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                            (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-sn-identity-sequencep)
                              (:definition fn-sti-completed-prefixp) (:definition fn-sti-livep)
                              (:definition fn-th-at) (:definition not)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart zp)
                              (:forward-chaining fn-snt-typed-store-components)
                              (:type-prescription fn-sn-statep) (:type-prescription len))))))

(defthm fn-osr-identity-next-of-with-configuration
  (equal (fn-sn-identity-next
          (fn-sn-with-configuration s groups capacity node configs))
         (fn-sn-identity-next s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-next fn-sn-with-configuration)
                (update-nth)))))

(defthm fn-osr-with-configuration-keeps-projections
  (let ((b (fn-sn-with-configuration s groups capacity node configs)))
    (and (equal (fn-sn-files b) (fn-sn-files s))
         (equal (fn-sn-consumer b) (fn-sn-consumer s))
         (equal (fn-sn-topic b) (fn-sn-topic s))
         (equal (fn-sn-identity-next b) (fn-sn-identity-next s))))
  :hints (("Goal" :in-theory
           (disable fn-sn-with-configuration fn-sn-identity-next))))

(defthm fn-osr-configure-durable-keeps-projections
  (let ((b (fn-cpo-configure-durable s record)))
    (and (equal (fn-sn-files b) (fn-sn-files s))
         (equal (fn-sn-consumer b) (fn-sn-consumer s))
         (equal (fn-sn-topic b) (fn-sn-topic s))
         (equal (fn-sn-identity-next b) (fn-sn-identity-next s))
         (equal (fn-sn-identity-context b) (fn-sn-identity-context s))))
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-configure-durable fn-cpo-install)
                (fn-cpo-history-relation fn-cpr-replay fn-sn-statep
                 fn-sn-with-configuration fn-cnode-statep
                 fn-replay-advance-okp fn-replay-advance-txid)))))

(defthm fn-osr-configure-durable-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-cpo-configure-durable s record)))
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-configure-durable)
                (fn-cpo-install fn-cpo-history-relation fn-cpr-replay
                 fn-sn-statep fn-cnode-statep fn-replay-advance-okp
                 fn-replay-advance-txid)))))

(defthm fn-osr-configure-durable-preserves-independent-live
  (implies (and (fn-sti-livep s) (fn-osr-identity-prefixp s))
           (and (fn-sti-livep (fn-cpo-configure-durable s record))
                (fn-osr-identity-prefixp (fn-cpo-configure-durable s record))))
  :hints (("Goal" :use fn-osr-configure-durable-keeps-projections
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-osr-identity-prefixp)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sf-record-phasep)
                              (:definition fn-sn-completion-record)
                              (:definition fn-sn-identity-sequencep)
                              (:definition fn-sti-completed-prefixp) (:definition fn-sti-livep)
                              (:definition fn-stxk-context-kind) (:definition fn-th-at)
                              (:definition member-equal) (:definition natp) (:definition not)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart zp)
                              (:rewrite fn-osr-configure-durable-preserves-state)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-sti-livep)
                              (:type-prescription fn-th-prefix-step) (:type-prescription len))))))

(in-theory (disable fn-osr-livep))


; Recovery construction typing; no successful-open premise.
(local
 (defthm fn-osr-verdict-listp-of-replay-verdict-pairs
   (fn-sn-verdict-listp (fn-replay-verdict-pairs events))
   :hints (("Goal" :induct (fn-replay-verdict-pairs events)
            :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-record-msgidp)
                              (:definition fn-record-string-octets)
                              (:definition fn-record-uint32p)
                              (:definition fn-replay-verdict-pairs)
                              (:definition fn-stx-make-verdict)
                              (:definition fn-stx-verdict-generation)
                              (:definition fn-stx-verdict-token) (:definition fn-stxe-p)
                              (:definition fn-stxe-tokenp) (:definition member-equal)
                              (:definition natp) (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart consp)
                              (:executable-counterpart fn-record-nonempty-at-mostp)
                              (:executable-counterpart fn-sn-verdict-listp)
                              (:executable-counterpart fn-stxe-tokenp)
                              (:executable-counterpart member-equal)
                              (:induction fn-replay-verdict-pairs) (:rewrite car-cons)
                              (:rewrite cdr-cons)
                              (:rewrite fn-sn-verdict-listp-of-recorded-cons)
                              (:type-prescription fn-record-ascii-stringp)
                              (:type-prescription fn-record-nonempty-at-mostp)
                              (:type-prescription fn-sn-verdict-listp)
                              (:type-prescription fn-stxe-bounded-octetsp)
                              (:type-prescription fn-stxe-shapep)))))))

(local (defthm fn-osr-verdict-listp-of-single
 (equal (fn-sn-verdict-listp (list pair))
        (and (consp pair) (stringp (car pair))
             (member-equal (fn-stx-verdict-token (cdr pair)) *fn-stx-verdicts*)
             (natp (fn-stx-verdict-generation (cdr pair)))))
 :hints (("Goal" :in-theory (enable fn-sn-verdict-listp)))))

(local (defthm fn-osr-held-msgid-is-string
 (implies (fn-held-p row) (stringp (fn-record-msgid row)))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-held-p fn-record-msgidp fn-record-ascii-stringp
     fn-held-accessors-are-the-wire-accessors))))))

(local (defthm fn-osr-event-verdict-pair-is-valid
 (implies (fn-stxe-p e)
          (fn-sn-verdict-listp (list (fn-replay-verdict-pair e))))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-osr-verdict-listp-of-single fn-stxe-p fn-record-msgidp
     fn-record-ascii-stringp fn-stxe-tokenp fn-record-uint32p natp
     fn-replay-verdict-pair fn-stx-make-verdict fn-stx-verdict-token
     fn-stx-verdict-generation car-cons cdr-cons))))))

(local (defthm fn-osr-row-verdict-pair-is-valid
 (fn-sn-verdict-listp (if (fn-sn-row-verdict-pair row)
                          (list (fn-sn-row-verdict-pair row)) nil))
 :hints (("Goal" :cases ((fn-held-p row)) :in-theory
  (union-theories (theory 'minimal-theory)
   '(car-cons cdr-cons
     (:executable-counterpart fn-sn-verdict-listp)
     fn-sn-row-verdict-pair fn-osr-verdict-listp-of-single
     fn-osr-held-msgid-is-string fn-held-p-fields fn-hc-p-fields
     fn-osr-event-verdict-pair-is-valid))))))
(local (defthm fn-osr-row-verdict-pair-fields
 (implies (fn-sn-row-verdict-pair row)
  (and (consp (fn-sn-row-verdict-pair row))
       (stringp (car (fn-sn-row-verdict-pair row)))
       (member-equal (fn-stx-verdict-token (cdr (fn-sn-row-verdict-pair row))) *fn-stx-verdicts*)
       (natp (fn-stx-verdict-generation (cdr (fn-sn-row-verdict-pair row))))))
 :hints (("Goal" :use fn-osr-row-verdict-pair-is-valid
  :in-theory (e/d (fn-sn-verdict-listp)
                 (fn-sn-row-verdict-pair fn-osr-row-verdict-pair-is-valid))))))
(local (defthm fn-osr-row-verdicts-fold-is-valid
 (implies (fn-sn-verdict-listp verdicts)
          (fn-sn-verdict-listp (fn-sn-row-verdicts-fold rows verdicts)))
 :hints (("Goal" :induct (fn-sn-row-verdicts-fold rows verdicts)
                 :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-sn-row-verdicts-fold)
                              (:definition fn-sn-verdict-listp) (:definition not)
                              (:induction fn-sn-row-verdicts-fold) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite fn-osr-row-verdict-pair-fields)
                              (:type-prescription fn-sn-row-verdict-pair)
                              (:type-prescription fn-sn-verdict-listp)))))))
(local (defthm fn-osr-row-verdicts-is-valid
 (fn-sn-verdict-listp (fn-sn-row-verdicts rows))
 :hints (("Goal" :in-theory (enable fn-sn-row-verdicts fn-sn-verdict-listp)))))

(local (defthm fn-osr-snapshot-generation-is-natural
  (natp (fn-ssk-generation snapshots))
  :hints (("Goal" :in-theory (enable fn-ssk-generation)))))

(local
 (defthm fn-osr-statep-of-v6-fields
   (implies (and (fn-string-listp groups)
                 (fn-no-duplicatesp groups)
                 (natp capacity)
                 (fn-sf-statep files)
                 (fn-node-statep node)
                 (fn-prin-keyringp keyring)
                 (natp keyring-generation)
                 (fn-sn-verdict-listp verdicts)
                 (fn-sn-keyring-snapshot-listp snapshots)
                 (natp identity-next))
            (fn-sn-statep
             (fn-sn-make-v6 groups capacity files node keyring index
                            keyring-generation verdicts snapshots identity-next
                            config-history consumer topic event-index)))
   :hints (("Goal" :in-theory
            (enable fn-sn-statep fn-sn-shapep fn-sn-make-v6
                    fn-sn-groups fn-sn-capacity fn-sn-files fn-sn-node
                    fn-sn-keyring fn-sn-keyring-generation fn-sn-verdicts
                    fn-sn-keyring-snapshots fn-sn-identity-next)))))

(local
 (defthm fn-osr-with-consumer-preserves-state
   (implies (fn-sn-statep s)
            (fn-sn-statep (fn-sn-with-consumer s consumer)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-sn-capacity) (:definition fn-sn-event-index)
                              (:definition fn-sn-files) (:definition fn-sn-groups)
                              (:definition fn-sn-identity-next) (:definition fn-sn-keyring)
                              (:definition fn-sn-keyring-generation)
                              (:definition fn-sn-keyring-snapshots) (:definition fn-sn-make-v6)
                              (:definition fn-sn-node) (:definition fn-sn-shapep)
                              (:definition fn-sn-statep) (:definition fn-sn-verdicts)
                              (:definition fn-sn-with-consumer) (:definition len)
                              (:definition natp) (:definition synp) (:definition true-listp)
                              (:executable-counterpart <) (:executable-counterpart binary-+)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fn-no-duplicatesp)
                              (:executable-counterpart fn-node-statep)
                              (:executable-counterpart fn-prin-keyringp)
                              (:executable-counterpart fn-sf-statep)
                              (:executable-counterpart fn-sn-keyring-snapshot-listp)
                              (:executable-counterpart fn-sn-verdict-listp)
                              (:executable-counterpart fn-string-listp)
                              (:executable-counterpart integerp) (:executable-counterpart len)
                              (:executable-counterpart not) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite fold-consts-in-+)
                              (:type-prescription fn-no-duplicatesp)
                              (:type-prescription fn-node-statep)
                              (:type-prescription fn-prin-keyringp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-keyring-snapshot-listp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-sn-verdict-listp)
                              (:type-prescription fn-string-listp)))))))

(local
 (defthm fn-osr-with-topic-preserves-state
   (implies (fn-sn-statep s)
            (fn-sn-statep (fn-sn-with-topic s topic)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-sn-capacity) (:definition fn-sn-event-index)
                              (:definition fn-sn-files) (:definition fn-sn-groups)
                              (:definition fn-sn-identity-next) (:definition fn-sn-keyring)
                              (:definition fn-sn-keyring-generation)
                              (:definition fn-sn-keyring-snapshots) (:definition fn-sn-make-v6)
                              (:definition fn-sn-node) (:definition fn-sn-shapep)
                              (:definition fn-sn-statep) (:definition fn-sn-verdicts)
                              (:definition fn-sn-with-topic) (:definition len)
                              (:definition natp) (:definition synp) (:definition true-listp)
                              (:executable-counterpart <) (:executable-counterpart binary-+)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fn-no-duplicatesp)
                              (:executable-counterpart fn-node-statep)
                              (:executable-counterpart fn-prin-keyringp)
                              (:executable-counterpart fn-sf-statep)
                              (:executable-counterpart fn-sn-keyring-snapshot-listp)
                              (:executable-counterpart fn-sn-verdict-listp)
                              (:executable-counterpart fn-string-listp)
                              (:executable-counterpart integerp) (:executable-counterpart len)
                              (:executable-counterpart not) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite fold-consts-in-+)
                              (:type-prescription fn-no-duplicatesp)
                              (:type-prescription fn-node-statep)
                              (:type-prescription fn-prin-keyringp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-keyring-snapshot-listp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-sn-verdict-listp)
                              (:type-prescription fn-string-listp)))))))

(local
 (defthm fn-osr-with-event-index-preserves-state
   (implies (fn-sn-statep s)
            (fn-sn-statep (fn-sn-with-event-index s event-index)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-sn-capacity) (:definition fn-sn-files)
                              (:definition fn-sn-groups) (:definition fn-sn-identity-next)
                              (:definition fn-sn-keyring) (:definition fn-sn-keyring-generation)
                              (:definition fn-sn-keyring-snapshots) (:definition fn-sn-make-v6)
                              (:definition fn-sn-node) (:definition fn-sn-shapep)
                              (:definition fn-sn-statep) (:definition fn-sn-verdicts)
                              (:definition fn-sn-with-event-index) (:definition len)
                              (:definition natp) (:definition synp) (:definition true-listp)
                              (:executable-counterpart <) (:executable-counterpart binary-+)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fn-no-duplicatesp)
                              (:executable-counterpart fn-node-statep)
                              (:executable-counterpart fn-prin-keyringp)
                              (:executable-counterpart fn-sf-statep)
                              (:executable-counterpart fn-sn-keyring-snapshot-listp)
                              (:executable-counterpart fn-sn-verdict-listp)
                              (:executable-counterpart fn-string-listp)
                              (:executable-counterpart integerp) (:executable-counterpart len)
                              (:executable-counterpart not) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite fold-consts-in-+)
                              (:type-prescription fn-no-duplicatesp)
                              (:type-prescription fn-node-statep)
                              (:type-prescription fn-prin-keyringp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-keyring-snapshot-listp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-sn-verdict-listp)
                              (:type-prescription fn-string-listp)))))))

(local
 (defthm fn-osr-recovering-files-are-state
   (implies (fn-sn-observed-historyp frontier records)
            (fn-sf-statep (fn-sf-make :recovering frontier nil records nil nil nil 0)))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-observed-historyp fn-sf-statep fn-sf-phase-shapep
                  fn-record-uint32p)
                 (fn-sf-record-listp fn-sf-make))))))

(local
 (defthm fn-osr-source-fields-typed
   (implies (fn-sn-statep s)
            (and (fn-string-listp (fn-sn-groups s))
                 (fn-no-duplicatesp (fn-sn-groups s))
                 (natp (fn-sn-capacity s))
                 (fn-node-statep (fn-sn-node s))
                 (fn-sn-keyring-snapshot-listp (fn-sn-keyring-snapshots s))
                 (natp (fn-sn-identity-next s))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-sn-statep)))))

(local
 (defthm fn-osr-with-configuration-of-v6
   (equal (fn-sn-with-configuration
           (fn-sn-make-v6 groups capacity files node keyring index generation
                          verdicts snapshots next configs consumer topic event-index)
           new-groups new-capacity new-node new-configs)
          (fn-sn-make-v6 new-groups new-capacity files new-node keyring index
                         generation verdicts snapshots next new-configs
                         consumer topic event-index))
   :hints (("Goal" :in-theory
            (enable fn-sn-with-configuration fn-sn-make-v6 update-nth)))))

; The inverse recovery keystone.  The four replay premises come from carried
; configuration, identity, consumer and topic relations.  Successful open is
; the conclusion, not a capture predicate or a served whole-history check.
(defthm fn-osr-live-ready-capture-opens
  (implies (and (fn-osr-livep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (fn-sn-open-okp
            (fn-cpo-open-observed (fn-sn-config-history (fn-osr-capture s))
                                  (fn-sf-frontier (fn-sn-files (fn-osr-capture s)))
                                  (fn-sf-records (fn-sn-files (fn-osr-capture s))))))
  :hints (("Goal"
           :use (fn-osr-ready-has-configured-history
                 fn-osr-ready-identity-exact-view
                 fn-csi-live-ready-exact-replay
                 fn-osr-ready-topic-exact
                 fn-sti-current-records-topic-ok-including-completed)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-cpo-history-relation) (:definition fn-cpo-install)
                              (:definition fn-cpo-open-observed)
                              (:definition fn-osr-context-view) (:definition fn-osr-livep)
                              (:definition fn-sn-event-index)
                              (:definition fn-sn-identity-context) (:definition fn-sn-make)
                              (:definition fn-sn-make-v2) (:definition fn-sn-observed-seed)
                              (:definition fn-sn-observed-topic-okp)
                              (:definition fn-sn-open-kind) (:definition fn-sn-open-ok)
                              (:definition fn-sn-open-okp) (:definition fn-sn-open-shapep)
                              (:definition fn-sn-open-state) (:definition fn-sn-update-replayed)
                              (:definition fn-sn-with-consumer)
                              (:definition fn-sn-with-event-index)
                              (:definition fn-sn-with-topic) (:definition fn-sti-livep)
                              (:definition fn-store-event-nth) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail) (:definition len)
                              (:definition not) (:executable-counterpart binary-+)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart cons) (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart fn-sn-open-error)
                              (:executable-counterpart fn-sn-open-okp)
                              (:executable-counterpart fn-store-event-nth)
                              (:executable-counterpart fn-stx-index-empty)
                              (:executable-counterpart fn-th-prefix-state)
                              (:executable-counterpart len) (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-osr-source-fields-typed) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite cons-equal)
                              (:rewrite fn-cnode-config-of-fn-cnode-make)
                              (:rewrite fn-cnode-node-of-fn-cnode-make)
                              (:rewrite fn-cpr-replay-ok-is-configured)
                              (:rewrite fn-cstp-statep-observed)
                              (:rewrite fn-osr-capture-is-carried-store-by-definition)
                              (:rewrite fn-osr-recovering-files-are-state)
                              (:rewrite fn-osr-row-verdicts-is-valid)
                              (:rewrite fn-osr-statep-of-v6-fields)
                              (:rewrite fn-osr-with-configuration-of-v6)
                              (:rewrite fn-sf-records-of-fn-sf-make)
                              (:rewrite fn-sn-fields-of-fn-sn-make-v6)
                              (:rewrite fn-ssk-keyring-of-snapshots-is-keyring)
                              (:type-prescription fn-cpe-projection-replay)
                              (:type-prescription fn-csi-livep)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-no-duplicatesp)
                              (:type-prescription fn-node-statep)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-replay-advance-okp)
                              (:type-prescription fn-sn-keyring-snapshot-listp)
                              (:type-prescription fn-sn-open-okp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-ssk-generation)
                              (:type-prescription fn-sti-completed-prefixp)
                              (:type-prescription fn-string-listp))))))

(defthm fn-osr-open-success-independent-projections
  (implies (and (true-listp configs)
                (fn-sn-open-okp (fn-cpo-open-observed configs frontier records)))
           (let ((st (fn-sn-open-state
                      (fn-cpo-open-observed configs frontier records)))
                 (identity (fn-replay-identity records))
                 (consumer (fn-cpe-projection-replay nil records 0))
                 (topic (fn-th-prefix-project records)))
             (and (consp configs)
                  (fn-sn-statep st)
                  (fn-sn-observed-historyp frontier records)
                  (equal (fn-stxk-context-kind identity) :ok)
                  (equal (car consumer) :ok)
                  (equal (fn-th-at 0 topic) :ok)
                  (equal (fn-sn-identity-next st) (fn-stxk-context-next identity))
                  (equal (fn-sn-keyring-snapshots st)
                         (fn-stxk-context-snapshots identity))
                  (equal (fn-sn-consumer st) (fn-cp-nth 1 consumer))
                  (equal (fn-sn-topic st) topic))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-cpo-install) (:definition fn-cpo-open-observed)
                              (:definition fn-sn-event-index) (:definition fn-sn-open-kind)
                              (:definition fn-sn-open-ok) (:definition fn-sn-open-okp)
                              (:definition fn-sn-open-state) (:definition fn-sn-update-replayed)
                              (:definition fn-sn-with-consumer)
                              (:definition fn-sn-with-event-index)
                              (:definition fn-sn-with-topic) (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots) (:definition fn-th-at)
                              (:executable-counterpart car) (:executable-counterpart equal)
                              (:executable-counterpart fn-sn-open-error)
                              (:executable-counterpart not) (:executable-counterpart true-listp)
                              (:executable-counterpart zp) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite fn-cnode-config-of-fn-cnode-make)
                              (:rewrite fn-cnode-node-of-fn-cnode-make)
                              (:rewrite fn-cpr-replay-ok-is-configured)
                              (:rewrite fn-osr-with-configuration-of-v6)
                              (:rewrite fn-sf-records-of-fn-sf-make)
                              (:rewrite fn-sn-fields-of-fn-sn-make-v6)
                              (:type-prescription fn-replay-advance-okp)
                              (:type-prescription fn-sn-observed-historyp)
                              (:type-prescription fn-sn-statep))))))

; The startup boundary checks the history once; it establishes every carry
; needed later.  Using this theorem at initialization is distinct from
; assuming that a later running capture reopens successfully.
(defthm fn-osr-open-establishes-live-carry
  (implies (and (true-listp configs)
                (fn-sn-open-okp (fn-cpo-open-observed configs frontier records)))
           (fn-osr-livep
            (fn-sn-open-state (fn-cpo-open-observed configs frontier records))))
  :hints (("Goal"
           :do-not '(preprocess)
           :use ((:instance fn-cpo-open-success-exact-image (events records))
                 (:instance fn-cst-open-success-has-historical-relation
                            (events records))
                 fn-osr-open-success-independent-projections
                 (:instance fn-replay-identity-ok-next-is-record-count)
                 (:instance fn-osr-identity-ok-has-canonical-context)
                 (:instance fn-csi-replay-ok-has-projection
                            (s nil) (expected 0))
                 (:instance fn-cstp-prefix-loop-next
                            (p (fn-th-prefix-state :ok 0 nil nil nil nil nil)))
                 (:instance fn-sf-record-listp-is-true-list
                            (sequence 0) (lower 0))
                 (:instance fn-cbor-take-whole-list (xs records)))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer) (:definition fix)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-osr-context-canonicalp)
                              (:definition fn-osr-context-view)
                              (:definition fn-osr-identity-prefixp) (:definition fn-osr-livep)
                              (:definition fn-sn-event-index)
                              (:definition fn-sn-identity-context)
                              (:definition fn-sn-identity-sequencep)
                              (:definition fn-sn-observed-historyp)
                              (:definition fn-sti-completed-prefixp) (:definition fn-sti-livep)
                              (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail) (:definition fn-th-at)
                              (:definition fn-th-prefix-project) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart eq) (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart fn-th-at)
                              (:executable-counterpart fn-th-prefix-state)
                              (:executable-counterpart natp) (:executable-counterpart zp)
                              (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite unicity-of-0)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-osr-livep)
                              (:type-prescription fn-sf-record-listp)
                              (:type-prescription fn-sn-open-okp)
                              (:type-prescription fn-sn-statep) (:type-prescription len))))))

(defthm fn-osr-known-abort-preserves-topic-live
  (implies (fn-sti-livep s) (fn-sti-livep (fn-sn-known-abort s)))
  :hints (("Goal"
           :use (fn-sti-known-abort-preserves-consumer-live)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-sf-abort-completion)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sf-prepublish-abort)
                              (:definition fn-sf-record-file-result)
                              (:definition fn-sf-record-pair) (:definition fn-sf-record-phasep)
                              (:definition fn-sn-completion-record)
                              (:definition fn-sn-known-abort)
                              (:definition fn-sn-known-abort-file-start)
                              (:definition fn-sn-known-abort-files)
                              (:definition fn-sti-completed-prefixp) (:definition fn-sti-livep)
                              (:definition fn-th-at) (:definition member-equal)
                              (:definition natp) (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart consp)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart zp)
                              (:rewrite fn-csi-identity-next-of-update)
                              (:rewrite fn-cstp-held-kind-facts)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-sf-records-field-of-fn-sf-make-fields)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-scalars-of-fn-sf-make-fields)
                              (:rewrite fn-sf-successes-field-of-fn-sf-make-fields)
                              (:rewrite fn-sti-topic-of-update)
                              (:type-prescription fn-csi-livep) (:type-prescription fn-held-p)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sti-livep)
                              (:type-prescription fn-th-prefix-step))))))

(defun fn-osr-independent-livep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sti-livep s) (fn-osr-identity-prefixp s)))

(defthm fn-osr-initial-independent-live
  (implies (and (fn-string-listp groups) (fn-no-duplicatesp groups) (natp capacity))
           (fn-osr-independent-livep (fn-sn-initial groups capacity)))
  :hints (("Goal" :use (fn-sti-initial-live fn-osr-initial-identity-prefix)
           :in-theory (e/d (fn-osr-independent-livep)
                           (fn-sti-livep fn-osr-identity-prefixp fn-sn-initial)))))

(local
 (defthm fn-osr-topic-live-implies-consumer-live
   (implies (fn-sti-livep s) (fn-csi-livep s))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-sti-livep)))))
(local
 (defthm fn-osr-consumer-live-implies-state
   (implies (fn-csi-livep s) (fn-sn-statep s))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory '(fn-csi-livep)))))

(defthm fn-osr-store-step-preserves-independent-live
  (implies (and (fn-osr-independent-livep s)
                (not (member-equal (car event) '(:crash :recover))))
           (fn-osr-independent-livep (fn-snrt-step s event)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-osr-independent-livep) (:definition fn-snrt-step)
                              (:definition fn-snt-step) (:definition member-equal)
                              (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart consp)
                              (:executable-counterpart equal)
                              (:forward-chaining fn-osr-consumer-live-implies-state)
                              (:forward-chaining fn-osr-topic-live-implies-consumer-live)
                              (:rewrite fn-osr-finish-preserves-identity-prefix)
                              (:rewrite fn-osr-io-preserves-identity-prefix)
                              (:rewrite fn-osr-known-abort-preserves-identity-prefix)
                              (:rewrite fn-osr-known-abort-preserves-topic-live)
                              (:rewrite fn-osr-prepare-article-preserves-identity-prefix)
                              (:rewrite fn-osr-prepare-consumer-preserves-identity-prefix)
                              (:rewrite fn-osr-prepare-identity-preserves-identity-prefix)
                              (:rewrite fn-osr-prepare-retention-preserves-identity-prefix)
                              (:rewrite fn-osr-prepare-topic-preserves-identity-prefix)
                              (:rewrite fn-osr-refuse-reservation-preserves-identity-prefix)
                              (:rewrite fn-sti-finish-preserves-live)
                              (:rewrite fn-sti-io-preserves-live)
                              (:rewrite fn-sti-prepare-article-preserves-live)
                              (:rewrite fn-sti-prepare-consumer-preserves-live)
                              (:rewrite fn-sti-prepare-identity-preserves-live)
                              (:rewrite fn-sti-prepare-retention-preserves-live)
                              (:rewrite fn-sti-prepare-topic-preserves-live)
                              (:rewrite fn-sti-refuse-reservation-preserves-live)
                              (:type-prescription fn-csi-livep)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-osr-independent-livep)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-sti-livep))))))

(defthm fn-osr-store-trace-preserves-independent-live
  (implies (and (fn-osr-independent-livep s) (fn-csi-no-crash-eventsp events))
           (fn-osr-independent-livep (fn-snrt-run s events)))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-csi-no-crash-eventsp) (:definition fn-snrt-run)
                              (:definition member-equal) (:definition not)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart consp) (:induction fn-snrt-run)
                              (:rewrite fn-osr-store-step-preserves-independent-live)
                              (:type-prescription fn-osr-independent-livep))))))

(defthm fn-osr-configure-durable-keeps-config-domain
  (implies (consp (fn-sn-config-history s))
           (consp (fn-sn-config-history (fn-cpo-configure-durable s record))))
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-configure-durable fn-cpo-install)
                (fn-cpo-history-relation fn-cpr-replay fn-sn-statep
                 fn-sn-with-configuration fn-cnode-statep
                 fn-replay-advance-okp fn-replay-advance-txid)))))

(defthm fn-osr-configure-durable-keeps-config-proper
  (implies (true-listp (fn-sn-config-history s))
           (true-listp (fn-sn-config-history (fn-cpo-configure-durable s record))))
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-configure-durable fn-cpo-install)
                (fn-cpo-history-relation fn-cpr-replay fn-sn-statep
                 fn-sn-with-configuration fn-cnode-statep
                 fn-replay-advance-okp fn-replay-advance-txid)))))

(defthm fn-osr-configured-relation-implies-config-proper
  (implies (fn-cst-relation s) (true-listp (fn-sn-config-history s)))
  :hints (("Goal" :in-theory '(fn-cst-relation))))

(defthm fn-osr-configure-durable-not-ready-is-identity-by-definition
  (implies (not (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (equal (fn-cpo-configure-durable s record) s))
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-configure-durable)
                (fn-cpo-history-relation fn-cpr-replay fn-sn-statep)))))

(defthm fn-osr-configure-durable-preserves-configured-relation
  (implies (fn-cst-relation s)
           (fn-cst-relation (fn-cpo-configure-durable s record)))
  :hints (("Goal"
           :cases ((equal (fn-sf-phase (fn-sn-files s)) :ready))
           :use (fn-osr-ready-has-configured-history
                 (:instance fn-cpo-configure-durable-preserves-history-relation
                            (st s))
                 (:instance fn-cst-idle-from-observed-history
                            (st (fn-cpo-configure-durable s record))))
           :in-theory
           (e/d (fn-snt-idle-phasep)
                (fn-cpo-configure-durable fn-cpo-history-relation fn-cst-relation
                 fn-osr-ready-has-configured-history
                 fn-cpo-configure-durable-preserves-history-relation)))))

(defthm fn-osr-configure-durable-preserves-live-carry
  (implies (fn-osr-livep s) (fn-osr-livep (fn-cpo-configure-durable s record)))
  :hints (("Goal"
           :use fn-osr-configure-durable-preserves-independent-live
           :in-theory
           (e/d (fn-osr-livep)
                (fn-cpo-configure-durable fn-cst-relation fn-sti-livep
                 fn-osr-identity-prefixp)))))

(in-theory (disable fn-osr-independent-livep))

; Actual durable completion installs the configured replay node.  Independent
; projections are preserved by their own completion proofs; no revalidation.
(defthm fn-osr-finish-preserves-live-carry
  (implies (fn-osr-livep s) (fn-osr-livep (fn-sn-finish s)))
  :hints (("Goal" :use fn-osr-finish-preserves-identity-prefix
           :in-theory
           (e/d (fn-osr-livep)
                (fn-sn-finish fn-cst-relation fn-sti-livep
                 fn-osr-identity-prefixp fn-sn-config-history)))))

; These are the independent projections already carried by the running Store.
; Statement key tables, held verdicts and frozen row contexts have a separate
; recovery repair obligation; this theorem does not omit them from HST-040.
(defthm fn-osr-ready-capture-keeps-established-projections
  (implies (and (fn-osr-livep s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (let ((target (fn-sn-open-state
                          (fn-cpo-open-observed
                           (fn-sn-config-history (fn-osr-capture s))
                           (fn-sf-frontier (fn-sn-files (fn-osr-capture s)))
                           (fn-sf-records (fn-sn-files (fn-osr-capture s)))))))
             (and (equal (fn-sn-node target) (fn-sn-node s))
                  (equal (fn-sn-groups target) (fn-sn-groups s))
                  (equal (fn-sn-capacity target) (fn-sn-capacity s))
                  (equal (fn-sn-config-history target) (fn-sn-config-history s))
                  (equal (fn-sf-frontier (fn-sn-files target))
                         (fn-sf-frontier (fn-sn-files s)))
                  (equal (fn-sf-records (fn-sn-files target))
                         (fn-sf-records (fn-sn-files s)))
                  (equal (fn-sn-identity-next target) (fn-sn-identity-next s))
                  (equal (fn-sn-keyring-snapshots target) (fn-sn-keyring-snapshots s))
                  (equal (fn-sn-consumer target) (fn-sn-consumer s))
                  (equal (fn-sn-topic target) (fn-sn-topic s)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-osr-live-ready-capture-opens
                 fn-osr-ready-identity-exact-view
                 fn-csi-live-ready-exact-replay
                 fn-osr-ready-topic-exact
                 fn-osr-ready-has-configured-history
                 (:instance fn-cpo-open-success-has-historical-relation
                   (configs (fn-sn-config-history s))
                   (frontier (fn-sf-frontier (fn-sn-files s)))
                   (events (fn-sf-records (fn-sn-files s))))
                 (:instance fn-cpo-open-success-exact-image
                   (configs (fn-sn-config-history s))
                   (frontier (fn-sf-frontier (fn-sn-files s)))
                   (events (fn-sf-records (fn-sn-files s))))
                 (:instance fn-osr-open-success-independent-projections
                   (configs (fn-sn-config-history s))
                   (frontier (fn-sf-frontier (fn-sn-files s)))
                   (records (fn-sf-records (fn-sn-files s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-cnode-domain)
                              (:definition fn-cpo-history-relation)
                              (:definition fn-osr-context-view) (:definition fn-osr-livep)
                              (:definition fn-sn-event-index)
                              (:definition fn-sn-identity-context) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail) (:definition fn-th-at)
                              (:definition hide) (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart equal) (:executable-counterpart if)
                              (:executable-counterpart not) (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-advance-okp-natp)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-osr-topic-live-implies-consumer-live)
                              (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal)
                              (:rewrite fn-cpr-replay-ok-is-configured)
                              (:rewrite fn-csi-second-of-ok-by-definition)
                              (:rewrite fn-cstp-okp-later) (:rewrite fn-cstp-statep-observed)
                              (:rewrite fn-osr-capture-is-carried-store-by-definition)
                              (:rewrite fn-osr-configured-relation-implies-config-proper)
                              (:type-prescription fn-csi-livep)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-replay-advance-okp)
                              (:type-prescription fn-sn-open-okp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-sti-livep))))))

; :ready is required for equality to the source's committed node, but not
; for the history's ability to open. Remove that redundant opening premise.
(defthm fn-osr-configured-completing-enables-finish
  (implies (and (fn-cst-relation s)
                (equal (fn-sf-phase (fn-sn-files s)) :completing))
           (fn-sn-completion-enabledp s))
  :hints (("Goal" :in-theory
           (e/d (fn-cst-relation fn-snt-idle-phasep fn-sf-record-phasep)
                (fn-cst-recoverablep fn-cst-final-configurationp
                 fn-cst-completion-linkp fn-sn-statep fn-sn-completion-enabledp)))))

(defthm fn-osr-configured-never-completed
  (implies (fn-cst-relation s)
           (not (equal (fn-sf-phase (fn-sn-files s)) :completed)))
  :hints (("Goal" :in-theory
           (e/d (fn-cst-relation fn-snt-idle-phasep fn-sf-record-phasep)
                (fn-cst-recoverablep fn-cst-final-configurationp
                 fn-cst-completion-linkp fn-sn-statep fn-sn-completion-enabledp)))))


(defthm fn-osr-live-not-completing-identity-and-consumer-ok
  (implies (and (fn-osr-livep s)
                (not (equal (fn-sf-phase (fn-sn-files s)) :completing)))
           (and (equal (fn-stxk-context-kind
                        (fn-replay-identity (fn-sf-records (fn-sn-files s)))) :ok)
                (equal (car (fn-cpe-projection-replay
                             nil (fn-sf-records (fn-sn-files s)) 0)) :ok)))
  :hints (("Goal"
           :use ((:instance fn-sf-state-records-are-true-list
                            (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                            (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-csi-completed-prefixp) (:definition fn-csi-livep)
                              (:definition fn-osr-identity-prefixp) (:definition fn-osr-livep)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sf-record-phasep)
                              (:definition fn-sn-identity-sequencep) (:definition fn-sti-livep)
                              (:definition fn-th-at) (:definition member-equal)
                              (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart consp)
                              (:executable-counterpart equal) (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:forward-chaining fn-osr-source-fields-typed) (:rewrite car-cons)
                              (:rewrite fn-osr-configured-never-completed)
                              (:rewrite fn-sf-state-records-are-true-list)
                              (:type-prescription fn-cpe-projection-replay)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep) (:type-prescription len))))))

; The completing case is the finished Store's ready case; the livep recognizers
; are opened once, here, instead of under every phase branch of the keystone.
(local
 (defthm fn-osr-livep-parts
   (implies (fn-osr-livep s)
            (and (fn-cst-relation s) (fn-sti-livep s) (fn-csi-livep s)
                 (fn-osr-identity-prefixp s)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-osr-livep s) (fn-sti-livep s))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-osr-completing-enabled
   (implies (and (fn-cst-relation s)
                 (equal (fn-sf-phase (fn-sn-files s)) :completing))
            (fn-sn-completion-enabledp s))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-cst-relation s))
            :in-theory (union-theories (theory 'minimal-theory) '(fn-snt-idle-phasep fn-sf-record-phasep member-equal (:executable-counterpart member-equal)))))))

(local
 (defthm fn-osr-lcic-completing
   (implies (and (fn-osr-livep s)
                 (equal (fn-sf-phase (fn-sn-files s)) :completing))
            (and (equal (fn-stxk-context-kind
                         (fn-replay-identity (fn-sf-records (fn-sn-files s)))) :ok)
                 (equal (car (fn-cpe-projection-replay
                              nil (fn-sf-records (fn-sn-files s)) 0)) :ok)))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-osr-livep-parts
                  (:instance fn-osr-livep-parts (s (fn-sn-finish s)))
                  (:instance fn-osr-completing-enabled)
                  fn-osr-finish-preserves-live-carry fn-snt-finish-image
                  (:instance fn-osr-ready-identity-exact-view (s (fn-sn-finish s)))
                  (:instance fn-csi-live-ready-exact-replay (s (fn-sn-finish s))))
            :in-theory (union-theories (theory 'minimal-theory) '(car-cons))))))

(defthm fn-osr-live-current-identity-and-consumer-ok
  (implies (fn-osr-livep s)
           (and (equal (fn-stxk-context-kind
                        (fn-replay-identity (fn-sf-records (fn-sn-files s)))) :ok)
                (equal (car (fn-cpe-projection-replay
                             nil (fn-sf-records (fn-sn-files s)) 0)) :ok)))
  :hints (("Goal"
           :use (fn-osr-lcic-completing
                 fn-osr-live-not-completing-identity-and-consumer-ok)
           :in-theory (theory 'minimal-theory))))

; Proved a phase at a time: with the phase fixed, the livep recognizers open
; to a short conjunction; with the case split left to the one theorem they
; open under every branch of the phase disjunctions at once.
(local
 (defthm fn-osr-live-replay-identity-fields-typed-not-completing
  (implies (and (fn-osr-livep s)
                (not (equal (fn-sf-phase (fn-sn-files s)) :completing)))
           (and (natp (fn-stxk-context-next
                       (fn-replay-identity (fn-sf-records (fn-sn-files s)))))
                (fn-sn-keyring-snapshot-listp
                 (fn-stxk-context-snapshots
                  (fn-replay-identity (fn-sf-records (fn-sn-files s)))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-osr-source-fields-typed
                 (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                            (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-csi-livep) (:definition fn-osr-context-view)
                              (:definition fn-osr-identity-prefixp) (:definition fn-osr-livep)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sf-record-phasep)
                              (:definition fn-sn-identity-context)
                              (:definition fn-sn-identity-sequencep) (:definition fn-sti-livep)
                              (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail) (:definition fn-th-at)
                              (:definition member-equal) (:definition natp) (:definition not)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart cons) (:executable-counterpart consp)
                              (:executable-counterpart equal) (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:forward-chaining fn-snt-typed-store-components)
                              (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal)
                              (:rewrite fn-osr-configured-never-completed)
                              (:rewrite fn-sf-state-records-are-true-list)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-no-duplicatesp)
                              (:type-prescription fn-node-statep)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-keyring-snapshot-listp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-string-listp) (:type-prescription len)))))))

(local
 (defthm fn-osr-live-replay-identity-fields-typed-completing
  (implies (and (fn-osr-livep s)
                (equal (fn-sf-phase (fn-sn-files s)) :completing))
           (and (natp (fn-stxk-context-next
                       (fn-replay-identity (fn-sf-records (fn-sn-files s)))))
                (fn-sn-keyring-snapshot-listp
                 (fn-stxk-context-snapshots
                  (fn-replay-identity (fn-sf-records (fn-sn-files s)))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-osr-source-fields-typed
                 (:instance fn-osr-ready-identity-exact-view (s (fn-sn-finish s)))
                 (:instance fn-osr-source-fields-typed (s (fn-sn-finish s)))
                 fn-osr-finish-preserves-live-carry fn-snt-finish-image
                 (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                            (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-csi-livep) (:definition fn-osr-context-view)
                              (:definition fn-osr-identity-prefixp) (:definition fn-osr-livep)
                              (:definition fn-sn-identity-context)
                              (:definition fn-sn-identity-sequencep) (:definition fn-sti-livep)
                              (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-tail) (:definition fn-th-at)
                              (:definition natp) (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:forward-chaining fn-osr-topic-live-implies-consumer-live)
                              (:forward-chaining fn-snt-typed-store-components)
                              (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal)
                              (:rewrite fn-csi-enabled-phase-by-definition)
                              (:rewrite fn-csi-finish-preserves-live)
                              (:rewrite fn-csi-take-next)
                              (:rewrite fn-ocmt-sn-finish-keeps-config-history)
                              (:rewrite fn-ocmt-sn-finish-preserves-cst-relation)
                              (:rewrite fn-osr-configured-completing-enables-finish)
                              (:rewrite fn-osr-finish-preserves-identity-prefix)
                              (:rewrite fn-osr-live-current-identity-and-consumer-ok)
                              (:rewrite fn-sf-state-records-are-true-list)
                              (:rewrite fn-sn-finish-enabled-advances-identity-next)
                              (:rewrite fn-sn-finish-preserves-state)
                              (:rewrite fn-sti-enabled-topic-step-ok-by-definition)
                              (:rewrite fn-sti-finish-preserves-live)
                              (:type-prescription fn-csi-livep)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-no-duplicatesp)
                              (:type-prescription fn-node-statep)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-keyring-snapshot-listp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-sti-completed-prefixp)
                              (:type-prescription fn-sti-livep)
                              (:type-prescription fn-string-listp)))))))

(defthm fn-osr-live-replay-identity-fields-typed
  (implies (fn-osr-livep s)
           (and (natp (fn-stxk-context-next
                       (fn-replay-identity (fn-sf-records (fn-sn-files s)))))
                (fn-sn-keyring-snapshot-listp
                 (fn-stxk-context-snapshots
                  (fn-replay-identity (fn-sf-records (fn-sn-files s)))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-osr-live-replay-identity-fields-typed-not-completing
                 fn-osr-live-replay-identity-fields-typed-completing)
           :in-theory (theory 'minimal-theory))))

; The phase-independent part of the relation; the keystone below needs no phase case.
(local
 (defthm fn-osr-cst-relation-common
   (implies (fn-cst-relation s)
            (and (fn-sn-statep s)
                 (true-listp (fn-sn-config-history s))
                 (fn-sn-observed-historyp (fn-sf-frontier (fn-sn-files s)) (fn-sf-records (fn-sn-files s)))
                 (fn-cst-final-configurationp s)
                 (fn-cst-recoverablep (fn-sn-config-history s) (fn-sf-records (fn-sn-files s)) (fn-sf-frontier (fn-sn-files s)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (theory (quote minimal-theory)) :expand ((fn-cst-relation s))))))

(defthm fn-osr-live-capture-opens
  (implies (fn-osr-livep s)
           (fn-sn-open-okp
            (fn-cpo-open-observed (fn-sn-config-history (fn-osr-capture s))
                                  (fn-sf-frontier (fn-sn-files (fn-osr-capture s)))
                                  (fn-sf-records (fn-sn-files (fn-osr-capture s))))))
  :hints (("Goal"
           :use ((:instance fn-osr-cst-relation-common)
                 fn-osr-live-replay-identity-fields-typed
                 fn-osr-live-current-identity-and-consumer-ok
                 fn-sti-current-records-topic-ok-including-completed)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-cpo-install) (:definition fn-cpo-open-observed)
                              (:definition fn-cst-final-configurationp)
                              (:definition fn-cst-recoverablep) (:definition fn-cst-replay-node)
                              (:definition fn-osr-livep) (:definition fn-sf-completion-phasep)
                              (:definition fn-sf-record-phasep) (:definition fn-sn-event-index)
                              (:definition fn-sn-make) (:definition fn-sn-make-v2)
                              (:definition fn-sn-observed-seed)
                              (:definition fn-sn-observed-topic-okp)
                              (:definition fn-sn-open-kind) (:definition fn-sn-open-ok)
                              (:definition fn-sn-open-okp) (:definition fn-sn-open-shapep)
                              (:definition fn-sn-open-state) (:definition fn-sn-update-replayed)
                              (:definition fn-sn-with-consumer)
                              (:definition fn-sn-with-event-index)
                              (:definition fn-sn-with-topic) (:definition fn-sti-livep)
                              (:definition fn-store-event-nth)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots) (:definition len)
                              (:definition member-equal) (:definition natp) (:definition not)
                              (:executable-counterpart binary-+) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart fn-sn-open-error)
                              (:executable-counterpart fn-sn-open-okp)
                              (:executable-counterpart fn-store-event-nth)
                              (:executable-counterpart fn-stx-index-empty)
                              (:executable-counterpart fn-th-prefix-state)
                              (:executable-counterpart len) (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-okp-node-statep)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-node-statep-forward-shape)
                              (:forward-chaining fn-osr-consumer-live-implies-state)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:forward-chaining fn-osr-topic-live-implies-consumer-live)
                              (:rewrite car-cons) (:rewrite cdr-cons)
                              (:rewrite fn-cnode-config-of-fn-cnode-make)
                              (:rewrite fn-cnode-node-of-fn-cnode-make)
                              (:rewrite fn-cpr-replay-ok-is-configured)
                              (:rewrite fn-cstp-advance-idle-at)
                              (:rewrite fn-cstp-statep-observed)
                              (:rewrite fn-osr-capture-is-carried-store-by-definition)
                              (:rewrite fn-osr-configured-never-completed)
                              (:rewrite fn-osr-configured-relation-implies-config-proper)
                              (:rewrite fn-osr-live-not-completing-identity-and-consumer-ok)
                              (:rewrite fn-osr-recovering-files-are-state)
                              (:rewrite fn-osr-row-verdicts-is-valid)
                              (:rewrite fn-osr-statep-of-v6-fields)
                              (:rewrite fn-osr-with-configuration-of-v6)
                              (:rewrite fn-replay-advance-preserves-node-statep)
                              (:rewrite fn-sf-records-of-fn-sf-make)
                              (:rewrite fn-sn-fields-of-fn-sn-make-v6)
                              (:rewrite fn-ssk-keyring-of-snapshots-is-keyring)
                              (:type-prescription fn-csi-livep)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-no-duplicatesp)
                              (:type-prescription fn-node-statep)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-replay-advance-okp)
                              (:type-prescription fn-sn-keyring-snapshot-listp)
                              (:type-prescription fn-sn-open-okp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-ssk-generation)
                              (:type-prescription fn-sti-completed-prefixp)
                              (:type-prescription fn-sti-livep)
                              (:type-prescription fn-string-listp)
                              (:type-prescription fn-th-topic-eventp))))))


; These are maintained proof predicates, never scans at live capture.
(defun fn-osr-verdict-prefixp (s)
  (declare (xargs :guard t :verify-guards nil))
  (equal (fn-sn-verdicts s)
         (fn-sn-row-verdicts
          (take (fn-sn-identity-next s) (fn-sf-records (fn-sn-files s))))))

(defun fn-osr-frozen-index-prefixp (s)
  (declare (xargs :guard t :verify-guards nil))
  (equal (fn-sn-index s)
         (fn-sn-index-of-rows
          (take (fn-sn-identity-next s) (fn-sf-records (fn-sn-files s))))))

(defun fn-osr-retainedp (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-osr-livep s) (fn-skp-resolvedp s)
       (fn-osr-verdict-prefixp s) (fn-osr-frozen-index-prefixp s)
       (equal (fn-sn-event-index s) nil)))

(defthm fn-osr-with-configuration-keeps-retained-fields
  (let ((b (fn-sn-with-configuration s groups capacity node configs)))
    (and (equal (fn-sn-keyring b) (fn-sn-keyring s))
         (equal (fn-sn-keyring-generation b) (fn-sn-keyring-generation s))
         (equal (fn-sn-verdicts b) (fn-sn-verdicts s))
         (equal (fn-sn-index b) (fn-sn-index s))
         (equal (fn-sn-event-index b) (fn-sn-event-index s))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-sn-event-index) (:definition fn-sn-index)
                              (:definition fn-sn-keyring) (:definition fn-sn-keyring-generation)
                              (:definition fn-sn-verdicts)
                              (:definition fn-sn-with-configuration)
                              (:definition fn-store-event-nth) (:definition update-nth)
                              (:elim car-cdr-elim) (:executable-counterpart binary-+)
                              (:executable-counterpart cdr) (:executable-counterpart equal)
                              (:executable-counterpart fn-store-event-nth)
                              (:executable-counterpart zp) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite default-cdr)
                              (:rewrite fn-cstp-store-event-nth-of-update-nth)
                              (:rewrite fn-osr-car-update-nth) (:rewrite fn-osr-cdr-update-nth))))))

(defthm fn-osr-open-success-retained-fields
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier records))
           (let* ((s (fn-sn-open-state (fn-cpo-open-observed configs frontier records)))
                  (snapshots (fn-stxk-context-snapshots (fn-replay-identity records))))
             (and (equal (fn-sn-keyring s) (fn-ssk-keyring-of-snapshots snapshots))
                  (equal (fn-sn-keyring-generation s) (fn-ssk-generation snapshots))
                  (equal (fn-sn-verdicts s) (fn-sn-row-verdicts records))
                  (equal (fn-sn-index s) (fn-sn-index-of-rows records))
                  (equal (fn-sn-event-index s) nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-cpo-install) (:definition fn-cpo-open-observed)
                              (:definition fn-sn-open-kind) (:definition fn-sn-open-ok)
                              (:definition fn-sn-open-okp) (:definition fn-sn-open-shapep)
                              (:definition fn-sn-open-state) (:definition fn-sn-update-replayed)
                              (:definition fn-sn-with-consumer)
                              (:definition fn-sn-with-event-index)
                              (:definition fn-sn-with-topic) (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots) (:definition fn-th-at)
                              (:executable-counterpart car) (:executable-counterpart equal)
                              (:executable-counterpart fn-sn-open-error)
                              (:executable-counterpart zp) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite fn-cnode-config-of-fn-cnode-make)
                              (:rewrite fn-cnode-node-of-fn-cnode-make)
                              (:rewrite fn-cpr-replay-ok-is-configured)
                              (:rewrite fn-osr-with-configuration-of-v6)
                              (:rewrite fn-sf-records-of-fn-sf-make)
                              (:rewrite fn-sn-fields-of-fn-sn-make-v6)
                              (:type-prescription fn-replay-advance-okp)
                              (:type-prescription fn-sn-observed-historyp)
                              (:type-prescription fn-sn-statep))))))

(local (defthm fn-osr-config-first-implies-consp
  (implies (fn-cpr-config-firstp configs events) (consp configs))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory) '(fn-cpr-config-firstp))))))
(local (defthm fn-osr-cpr-loop-success-has-proper-configs
  (implies (equal (fn-replay-result-kind
                   (fn-cpr-loop cn configs events config-sequence event-sequence)) :ok)
           (true-listp configs))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cpr-loop cn configs events config-sequence event-sequence)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-cpr-loop) (:definition fn-replay-fault)
                              (:definition fn-replay-result-kind) (:definition not)
                              (:definition null) (:definition true-listp)
                              (:executable-counterpart cons) (:executable-counterpart equal)
                              (:executable-counterpart true-listp) (:induction fn-cpr-loop)
                              (:rewrite car-cons) (:rewrite fn-osr-config-first-implies-consp)))))))
(local (defthm fn-osr-cpr-success-has-proper-configs
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs records)) :ok)
           (true-listp configs))
  :hints (("Goal"
           :use ((:instance fn-osr-cpr-loop-success-has-proper-configs
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (events records) (config-sequence 0) (event-sequence 0)))
           :in-theory
           (union-theories (theory 'minimal-theory) '(fn-cpr-replay))))))
(local (defthm fn-osr-open-success-has-proper-configs
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier records))
           (true-listp configs))
  :hints (("Goal" :use fn-osr-cpr-success-has-proper-configs
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-cpo-open-observed fn-sn-open-okp fn-sn-open-shapep fn-sn-open-kind
              fn-sn-open-error fn-sn-open-ok car-cons cdr-cons len
              (:executable-counterpart equal) (:executable-counterpart true-listp)))))))

(defthm fn-osr-open-establishes-full-retained-carry
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier records))
           (fn-osr-retainedp
            (fn-sn-open-state (fn-cpo-open-observed configs frontier records))))
  :hints (("Goal" :use (fn-osr-open-success-has-proper-configs
                        fn-osr-open-success-retained-fields
                        fn-osr-open-success-independent-projections
                        (:instance fn-cpo-open-success-exact-image (events records))
                        (:instance fn-replay-identity-ok-next-is-record-count)
                        (:instance fn-sf-record-listp-is-true-list (sequence 0) (lower 0))
                        (:instance fn-cbor-take-whole-list (xs records)))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-osr-frozen-index-prefixp)
                              (:definition fn-osr-retainedp)
                              (:definition fn-osr-verdict-prefixp)
                              (:definition fn-skp-resolvedp)
                              (:definition fn-sn-observed-historyp)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots) (:definition fn-th-at)
                              (:definition fn-th-prefix-project) (:definition not)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-th-prefix-state)
                              (:executable-counterpart zp)
                              (:rewrite fn-osr-open-establishes-live-carry)
                              (:rewrite fn-osr-open-success-has-proper-configs)
                              (:type-prescription fn-osr-retainedp)
                              (:type-prescription fn-sf-record-listp)
                              (:type-prescription fn-sn-open-okp))))))

(defthm fn-osr-ready-capture-keeps-retained-fields
  (implies (and (fn-osr-retainedp s)
                (equal (fn-sf-phase (fn-sn-files s)) :ready))
           (let ((target
                  (fn-sn-open-state
                   (fn-cpo-open-observed
                    (fn-sn-config-history (fn-osr-capture s))
                    (fn-sf-frontier (fn-sn-files (fn-osr-capture s)))
                    (fn-sf-records (fn-sn-files (fn-osr-capture s)))))))
             (and (equal (fn-sn-keyring target) (fn-sn-keyring s))
                  (equal (fn-sn-keyring-generation target) (fn-sn-keyring-generation s))
                  (equal (fn-sn-verdicts target) (fn-sn-verdicts s))
                  (equal (fn-sn-index target) (fn-sn-index s))
                  (equal (fn-sn-event-index target) (fn-sn-event-index s)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-osr-ready-capture-keeps-established-projections
                 fn-osr-live-ready-capture-opens
                 fn-osr-configured-relation-implies-config-proper
                 (:instance fn-osr-open-establishes-full-retained-carry
                            (configs (fn-sn-config-history s))
                            (frontier (fn-sf-frontier (fn-sn-files s)))
                            (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sf-state-records-are-true-list
                            (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list
                            (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-osr-frozen-index-prefixp)
                              (:definition fn-osr-livep) (:definition fn-osr-retainedp)
                              (:definition fn-osr-verdict-prefixp)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sf-record-phasep) (:definition fn-skp-resolvedp)
                              (:definition fn-sn-identity-sequencep)
                              (:definition fn-sti-completed-prefixp) (:definition fn-sti-livep)
                              (:definition fn-th-at) (:definition fn-th-prefix-project)
                              (:definition member-equal) (:definition natp) (:definition not)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart fn-th-prefix-state)
                              (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:rewrite fn-csi-enabled-phase-by-definition)
                              (:rewrite fn-csi-take-next)
                              (:rewrite fn-osr-capture-is-carried-store-by-definition)
                              (:rewrite fn-osr-configured-completing-enables-finish)
                              (:rewrite fn-osr-configured-never-completed)
                              (:rewrite fn-osr-open-establishes-live-carry)
                              (:rewrite fn-osr-open-success-has-proper-configs)
                              (:rewrite fn-sf-state-records-are-true-list)
                              (:rewrite fn-sti-enabled-topic-step-ok-by-definition)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-open-okp)
                              (:type-prescription fn-sn-statep))))))

(local (defthm fn-osr-with-configuration-keeps-retained-snapshots
  (equal (fn-sn-keyring-snapshots
           (fn-sn-with-configuration s groups capacity node configs))
         (fn-sn-keyring-snapshots s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-with-configuration fn-sn-keyring-snapshots fn-store-event-nth)
                (fn-sn-make-v6))))))

(defthm fn-osr-configure-durable-keeps-retained-fields
  (let ((b (fn-cpo-configure-durable s record)))
    (and (equal (fn-sn-keyring b) (fn-sn-keyring s))
         (equal (fn-sn-keyring-generation b) (fn-sn-keyring-generation s))
         (equal (fn-sn-keyring-snapshots b) (fn-sn-keyring-snapshots s))
         (equal (fn-sn-verdicts b) (fn-sn-verdicts s))
         (equal (fn-sn-index b) (fn-sn-index s))
         (equal (fn-sn-event-index b) (fn-sn-event-index s))))
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-configure-durable fn-cpo-install)
                (fn-cpo-history-relation fn-cpr-replay fn-sn-statep
                 fn-sn-with-configuration fn-cnode-statep
                 fn-replay-advance-okp fn-replay-advance-txid
                 fn-sn-keyring fn-sn-keyring-generation fn-sn-keyring-snapshots
                 fn-sn-verdicts fn-sn-index fn-sn-event-index)))))

(defthm fn-osr-configure-durable-preserves-full-retained-carry
  (implies (fn-osr-retainedp s)
           (fn-osr-retainedp (fn-cpo-configure-durable s record)))
  :hints (("Goal" :use (fn-osr-configure-durable-keeps-retained-fields
                        fn-osr-configure-durable-keeps-projections
                        fn-osr-configure-durable-preserves-live-carry)
           :in-theory
           (e/d (fn-osr-retainedp fn-skp-resolvedp fn-osr-verdict-prefixp
                 fn-osr-frozen-index-prefixp)
                (fn-cpo-configure-durable fn-osr-livep
                 fn-sn-keyring fn-sn-keyring-generation fn-sn-keyring-snapshots
                 fn-sn-verdicts fn-sn-index fn-sn-event-index
                 fn-sn-identity-next fn-sn-files fn-sf-records
                 fn-sn-row-verdicts fn-sn-index-of-rows
                 fn-ssk-keyring-of-snapshots fn-ssk-generation
                 fn-osr-configure-durable-keeps-retained-fields
                 fn-osr-configure-durable-keeps-projections
                 fn-osr-configure-durable-preserves-live-carry)))))

(local (defthm fn-osr-index-add-no-delta
  (equal (fn-stx-index-add index nil) index)
  :hints (("Goal" :in-theory '(fn-stx-index-add)))))

(local (defthm fn-osr-finish-keeps-retired-index
  (equal (fn-sn-event-index (fn-sn-finish s)) (fn-sn-event-index s))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-sn-advance-identity-next)
                              (:definition fn-sn-finish) (:definition fn-sn-finish-identity)
                              (:definition fn-sn-update-accepted)
                              (:definition fn-sn-update-indexed)
                              (:definition fn-sn-with-consumer) (:definition fn-sn-with-topic)
                              (:definition nfix) (:definition not)
                              (:executable-counterpart fn-replay-verdict-pairs)
                              (:forward-chaining fn-ccar-completion-enabled-implies-statep)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:rewrite fn-cp-append-nil-left)
                              (:rewrite fn-cpe-is-disjoint-from-old-event-kinds-by-shape)
                              (:rewrite fn-csi-topic-event-is-not-consumer-event)
                              (:rewrite fn-hls-retained-kind4-disjoint-from-other-store-events)
                              (:rewrite fn-hls-snapshot-disjoint-from-other-store-events)
                              (:rewrite fn-hls-snapshot-identity-step-has-no-new-verdict)
                              (:rewrite fn-hls-snapshot-is-no-retained-composite)
                              (:rewrite fn-osr-consumer-is-not-retained-composite)
                              (:rewrite fn-osr-retention-is-identity-neutral)
                              (:rewrite fn-sn-event-index-of-fn-sn-with-consumer)
                              (:rewrite fn-sn-event-index-of-fn-sn-with-topic)
                              (:rewrite fn-sn-fields-of-fn-sn-make-v6)
                              (:rewrite fn-sti-consumer-event-is-not-topic)
                              (:rewrite fn-sti-retention-event-is-not-topic)
                              (:rewrite fn-th-topic-event-is-no-hstxa)
                              (:type-prescription fn-cpe-eventp) (:type-prescription fn-hstxa-p)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-store-retention-event-p)
                              (:type-prescription fn-stxk-p)
                              (:type-prescription fn-th-topic-eventp)))))))

(local (defthm fn-osr-finish-advances-frozen-index
  (implies (and (fn-sn-statep s) (fn-sn-completion-enabledp s))
           (equal (fn-sn-index (fn-sn-finish s))
                  (fn-stx-index-add (fn-sn-index s)
                                   (fn-sn-row-delta (fn-sn-completion-record s)))))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-sn-accepted-delta)
                              (:definition fn-sn-advance-identity-next)
                              (:definition fn-sn-composite-delta)
                              (:definition fn-sn-event-index) (:definition fn-sn-finish)
                              (:definition fn-sn-finish-identity) (:definition fn-sn-row-delta)
                              (:definition fn-sn-statep) (:definition fn-sn-update-accepted)
                              (:definition fn-sn-update-indexed) (:definition natp)
                              (:definition nfix) (:definition not)
                              (:executable-counterpart fn-replay-verdict-pairs)
                              (:forward-chaining fn-ccar-completion-enabled-implies-statep)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:rewrite fn-cp-append-nil-left)
                              (:rewrite fn-cpe-is-disjoint-from-old-event-kinds-by-shape)
                              (:rewrite fn-csi-topic-event-is-not-consumer-event)
                              (:rewrite fn-cstp-held-kind-facts)
                              (:rewrite fn-hls-retained-kind4-disjoint-from-other-store-events)
                              (:rewrite fn-hls-snapshot-disjoint-from-other-store-events)
                              (:rewrite fn-hls-snapshot-identity-step-has-no-new-verdict)
                              (:rewrite fn-hls-snapshot-is-no-retained-composite)
                              (:rewrite fn-hstxa-is-not-held)
                              (:rewrite fn-osr-consumer-is-not-retained-composite)
                              (:rewrite fn-osr-index-add-no-delta)
                              (:rewrite fn-osr-retention-is-identity-neutral)
                              (:rewrite fn-sn-fields-of-fn-sn-make-v6)
                              (:rewrite fn-sn-state-fields-of-fn-sn-with-consumer)
                              (:rewrite fn-sn-state-fields-of-fn-sn-with-topic)
                              (:rewrite fn-sti-consumer-event-is-not-topic)
                              (:rewrite fn-sti-retention-event-is-not-topic)
                              (:rewrite fn-th-topic-event-is-no-hstxa)
                              (:type-prescription fn-cpe-eventp) (:type-prescription fn-held-p)
                              (:type-prescription fn-hstxa-p)
                              (:type-prescription fn-no-duplicatesp)
                              (:type-prescription fn-node-statep)
                              (:type-prescription fn-prin-keyringp)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-sn-keyring-snapshot-listp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-store-retention-event-p)
                              (:type-prescription fn-string-listp)
                              (:type-prescription fn-stxk-p)
                              (:type-prescription fn-th-topic-eventp)))))))

(local (defthm fn-osr-standalone-verdict-emits-no-acceptance
  (implies (and (fn-stxe-p event)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-step (fn-sn-identity-context s) event)) :ok))
           (equal (fn-stxk-context-verdicts
                   (fn-replay-identity-step (fn-sn-identity-context s) event)) nil))
  :hints (("Goal"
           :use ((:instance fn-hls-snapshot-identity-step-has-no-new-verdict)
                 (:instance fn-hls-snapshot-disjoint-from-other-store-events)
                 (:instance fn-hls-retained-kind4-disjoint-from-other-store-events))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-replay-identity-step)
                              (:definition fn-replay-identity-wire)
                              (:definition fn-sn-identity-context) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:definition not) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart equal) (:executable-counterpart not)
                              (:rewrite car-cons) (:rewrite cdr-cons)
                              (:rewrite fn-hls-snapshot-is-no-retained-composite)
                              (:type-prescription fn-stxe-p) (:type-prescription fn-stxk-p)))))))

(local (defthm fn-osr-composite-enabled-decode-ok
  (implies (and (fn-csi-livep s) (fn-sn-completion-enabledp s)
                (fn-hstxa-p (fn-sn-completion-record s)))
           (fn-stmt-okp
            (fn-stxe-decode-exact
             (fn-stxa-verdict-event (fn-hstxa-stxa (fn-sn-completion-record s))))))
  :hints (("Goal"
           :use (fn-osr-enabled-identity-step-ok
                 (:instance fn-hls-retained-kind4-disjoint-from-other-store-events
                            (event (fn-sn-completion-record s)))
                 (:instance fn-hls-kind4-disjoint-from-other-store-events
                            (event (fn-hstxa-stxa (fn-sn-completion-record s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-hsig-article-event-carried-bindsp)
                              (:definition fn-hsig-article-event-revoked-bindsp)
                              (:definition fn-replay-identity-step)
                              (:definition fn-replay-identity-wire)
                              (:definition fn-sn-identity-context) (:definition fn-stxa-bindsp)
                              (:definition fn-stxa-schema) (:definition fn-stxk-context)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-verdicts) (:definition fn-stxk-fault)
                              (:definition not) (:definition posp) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart cons)
                              (:executable-counterpart equal) (:executable-counterpart integerp)
                              (:executable-counterpart not) (:rewrite car-cons)
                              (:rewrite cdr-cons)
                              (:rewrite fn-hls-retained-kind4-disjoint-from-other-store-events)
                              (:rewrite fn-hstxa-p-fields) (:type-prescription fn-csi-livep)
                              (:type-prescription fn-hstxa-p)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-stmt-okp)))))))

(local (defthm fn-osr-finish-advances-retained-verdicts
  (implies (and (fn-csi-livep s) (fn-sn-completion-enabledp s))
           (equal (fn-sn-verdicts (fn-sn-finish s))
                  (let ((pair (fn-sn-row-verdict-pair (fn-sn-completion-record s))))
                    (if pair (cons pair (fn-sn-verdicts s)) (fn-sn-verdicts s)))))
  :hints (("Goal"
           :use (fn-osr-enabled-completion-is-next-event
                 fn-osr-composite-enabled-decode-ok
                 fn-hls-finish-kind4-verdicts
                 (:instance fn-hls-kind4-identity-step-ok-has-evidence-record
                            (event (fn-sn-completion-record s)))
                 fn-osr-enabled-identity-step-ok)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition binary-append) (:definition fn-replay-verdict-pair)
                              (:definition fn-replay-verdict-pairs)
                              (:definition fn-sn-advance-identity-next)
                              (:definition fn-sn-event-index) (:definition fn-sn-finish)
                              (:definition fn-sn-finish-identity)
                              (:definition fn-sn-row-verdict-pair)
                              (:definition fn-sn-update-accepted)
                              (:definition fn-sn-update-indexed) (:definition fn-store-event-p)
                              (:definition fn-stxk-context-current-generation)
                              (:definition fn-stxk-context-kind)
                              (:definition fn-stxk-context-next)
                              (:definition fn-stxk-context-snapshots)
                              (:definition fn-stxk-context-verdicts) (:definition nfix)
                              (:definition not) (:executable-counterpart equal)
                              (:executable-counterpart fn-replay-verdict-pairs)
                              (:forward-chaining fn-ccar-completion-enabled-implies-statep)
                              (:forward-chaining fn-held-p-forward-natural-head)
                              (:forward-chaining fn-hstxa-p-forward-shape)
                              (:forward-chaining fn-osr-consumer-live-implies-state)
                              (:forward-chaining fn-osr-source-fields-typed) (:rewrite car-cons)
                              (:rewrite cdr-cons) (:rewrite fn-cp-append-nil-left)
                              (:rewrite fn-cpe-is-disjoint-from-old-event-kinds-by-shape)
                              (:rewrite fn-csi-topic-event-is-not-consumer-event)
                              (:rewrite fn-cstp-held-kind-facts)
                              (:rewrite fn-hls-kind4-identity-step-emits-its-verdict-event)
                              (:rewrite fn-hls-retained-kind4-disjoint-from-other-store-events)
                              (:rewrite fn-hls-snapshot-disjoint-from-other-store-events)
                              (:rewrite fn-hls-snapshot-identity-step-has-no-new-verdict)
                              (:rewrite fn-hls-snapshot-is-no-retained-composite)
                              (:rewrite fn-hstxa-is-not-held)
                              (:rewrite fn-osr-consumer-is-not-retained-composite)
                              (:rewrite fn-osr-retention-is-identity-neutral)
                              (:rewrite fn-osr-standalone-verdict-emits-no-acceptance)
                              (:rewrite fn-sn-fields-of-fn-sn-make-v6)
                              (:rewrite fn-sn-state-fields-of-fn-sn-with-consumer)
                              (:rewrite fn-sn-state-fields-of-fn-sn-with-topic)
                              (:rewrite fn-sti-consumer-event-is-not-topic)
                              (:rewrite fn-sti-retention-event-is-not-topic)
                              (:rewrite fn-th-topic-event-is-no-hstxa)
                              (:type-prescription fn-cpe-eventp)
                              (:type-prescription fn-csi-livep) (:type-prescription fn-held-p)
                              (:type-prescription fn-hstxa-p)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-sn-statep) (:type-prescription fn-stmt-okp)
                              (:type-prescription fn-store-retention-event-p)
                              (:type-prescription fn-stx-make-verdict)
                              (:type-prescription fn-stxe-p) (:type-prescription fn-stxk-p)
                              (:type-prescription fn-th-topic-eventp)))))))
(local (defthm fn-osr-finish-preserves-retained-verdict-prefix
  (implies (and (fn-osr-verdict-prefixp s) (fn-csi-livep s))
           (fn-osr-verdict-prefixp (fn-sn-finish s)))
  :hints (("Goal"
           :do-not '(preprocess)
           :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-disabled-is-no-op fn-snt-finish-image
                 fn-sn-finish-enabled-advances-identity-next
                 fn-csi-enabled-phase-by-definition fn-osr-finish-advances-retained-verdicts
                 (:instance fn-csi-take-next
                            (n (fn-sn-identity-next s))
                            (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sn-row-verdicts-of-append-one
                            (rows (take (fn-sn-identity-next s)
                                        (fn-sf-records (fn-sn-files s))))
                            (row (fn-sn-completion-record s))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:compound-recognizer zp-compound-recognizer) (:definition fix)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-osr-verdict-prefixp)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sn-identity-sequencep) (:definition len)
                              (:definition member-equal) (:definition natp) (:definition not)
                              (:definition synp) (:definition take) (:executable-counterpart <)
                              (:executable-counterpart binary-+) (:executable-counterpart car)
                              (:executable-counterpart cdr) (:executable-counterpart consp)
                              (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart integerp) (:executable-counterpart not)
                              (:forward-chaining fn-ccar-completion-enabled-implies-statep)
                              (:forward-chaining fn-osr-consumer-live-implies-state)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:rewrite fn-csi-enabled-phase-by-definition)
                              (:rewrite fn-cstp-minus-one-of-successor)
                              (:rewrite fn-sn-finish-enabled-advances-identity-next)
                              (:rewrite fold-consts-in-+) (:rewrite unicity-of-0)
                              (:rewrite zp-open) (:type-prescription fn-csi-livep)
                              (:type-prescription fn-osr-verdict-prefixp)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-sn-row-verdict-pair)
                              (:type-prescription fn-sn-statep) (:type-prescription len)))))))

(local (defthm fn-osr-finish-preserves-frozen-index-prefix
  (implies (and (fn-osr-frozen-index-prefixp s) (fn-csi-livep s))
           (fn-osr-frozen-index-prefixp (fn-sn-finish s)))
  :hints (("Goal"
           :do-not '(preprocess)
           :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-disabled-is-no-op fn-snt-finish-image
                 fn-sn-finish-enabled-advances-identity-next
                 fn-csi-enabled-phase-by-definition fn-osr-finish-advances-frozen-index
                 (:instance fn-csi-take-next
                            (n (fn-sn-identity-next s))
                            (records (fn-sf-records (fn-sn-files s))))
                 (:instance fn-sn-index-of-rows-of-append-one
                            (rows (take (fn-sn-identity-next s)
                                        (fn-sf-records (fn-sn-files s))))
                            (row (fn-sn-completion-record s))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:compound-recognizer zp-compound-recognizer)
                              (:definition fn-csi-completed-prefixp)
                              (:definition fn-csi-completion-lastp) (:definition fn-csi-livep)
                              (:definition fn-osr-frozen-index-prefixp)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sn-identity-sequencep) (:definition len)
                              (:definition member-equal) (:definition natp) (:definition take)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart not)
                              (:forward-chaining fn-ccar-completion-enabled-implies-statep)
                              (:forward-chaining fn-osr-consumer-live-implies-state)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:rewrite fn-csi-enabled-phase-by-definition)
                              (:rewrite fn-cstp-minus-one-of-successor)
                              (:rewrite fn-sn-finish-enabled-advances-identity-next)
                              (:type-prescription fn-csi-livep)
                              (:type-prescription fn-osr-frozen-index-prefixp)
                              (:type-prescription fn-sn-completion-enabledp)
                              (:type-prescription fn-sn-statep) (:type-prescription len)))))))

(defthm fn-osr-finish-preserves-full-retained-carry
  (implies (fn-osr-retainedp s)
           (fn-osr-retainedp (fn-sn-finish s)))
  :hints (("Goal"
           :use (fn-osr-finish-preserves-live-carry fn-skp-finish-preserves-resolution
                 fn-osr-finish-preserves-retained-verdict-prefix
                 fn-osr-finish-preserves-frozen-index-prefix fn-osr-finish-keeps-retired-index)
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-livep) (:definition fn-osr-retainedp)
                              (:definition fn-sf-completion-phasep)
                              (:definition fn-sf-record-phasep)
                              (:definition fn-sti-completed-prefixp) (:definition fn-sti-livep)
                              (:definition fn-th-at) (:definition fn-th-prefix-project)
                              (:definition member-equal) (:definition not)
                              (:executable-counterpart car) (:executable-counterpart cdr)
                              (:executable-counterpart consp) (:executable-counterpart equal)
                              (:executable-counterpart fn-sf-completion-phasep)
                              (:executable-counterpart fn-sf-record-phasep)
                              (:executable-counterpart fn-th-prefix-state)
                              (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:forward-chaining fn-osr-topic-live-implies-consumer-live)
                              (:rewrite fn-csi-enabled-phase-by-definition)
                              (:rewrite fn-ocmt-sn-finish-keeps-config-history)
                              (:rewrite fn-ocmt-sn-finish-preserves-cst-relation)
                              (:rewrite fn-osr-configured-completing-enables-finish)
                              (:rewrite fn-osr-configured-never-completed)
                              (:rewrite fn-osr-finish-preserves-identity-prefix)
                              (:rewrite fn-sti-enabled-topic-step-ok-by-definition)
                              (:rewrite fn-sti-finish-preserves-live)
                              (:type-prescription fn-csi-livep)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-osr-frozen-index-prefixp)
                              (:type-prescription fn-osr-identity-prefixp)
                              (:type-prescription fn-osr-retainedp)
                              (:type-prescription fn-osr-verdict-prefixp)
                              (:type-prescription fn-skp-resolvedp)
                              (:type-prescription fn-sn-statep)
                              (:type-prescription fn-sti-livep)
                              (:type-prescription fn-th-prefix-step)
                              (:type-prescription fn-th-topic-eventp))))))

; This boundary view includes every additional semantic carry and the rows
; to which it refers. It is proof vocabulary, not a served-state revalidation.
(defun fn-osr-retained-view (s)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-sn-keyring s) (fn-sn-keyring-generation s)
        (fn-sn-keyring-snapshots s) (fn-sn-verdicts s) (fn-sn-index s)
        (fn-sn-event-index s)
        (take (fn-sn-identity-next s) (fn-sf-records (fn-sn-files s)))))

(defthm fn-osr-retained-view-connects-full-carry
  (implies (and (fn-osr-retainedp a) (fn-osr-livep b)
                (equal (fn-osr-retained-view a) (fn-osr-retained-view b)))
           (fn-osr-retainedp b))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-osr-retained-view fn-osr-retainedp fn-skp-resolvedp
                 fn-osr-verdict-prefixp fn-osr-frozen-index-prefixp)
                (fn-osr-livep fn-sn-keyring fn-sn-keyring-generation
                 fn-sn-keyring-snapshots fn-sn-verdicts fn-sn-index fn-sn-event-index
                 fn-sn-identity-next fn-sn-files fn-sf-records take
                 fn-ssk-keyring-of-snapshots fn-ssk-generation
                 fn-sn-row-verdicts fn-sn-index-of-rows)))))

(local (defthm fn-osr-update-retained-selectors
  (let ((b (fn-sn-update s files node)))
    (and (equal (fn-sn-keyring b) (fn-sn-keyring s))
         (equal (fn-sn-keyring-generation b) (fn-sn-keyring-generation s))
         (equal (fn-sn-keyring-snapshots b) (fn-sn-keyring-snapshots s))
         (equal (fn-sn-verdicts b) (fn-sn-verdicts s))
         (equal (fn-sn-index b) (fn-sn-index s))
         (equal (fn-sn-event-index b) (fn-sn-event-index s))
         (equal (fn-sn-identity-next b) (fn-sn-identity-next s))))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-update)
                (fn-sn-make-v6 fn-sn-keyring fn-sn-keyring-generation
                 fn-sn-keyring-snapshots fn-sn-verdicts fn-sn-index
                 fn-sn-event-index fn-sn-identity-next))))))

(defthm fn-osr-preparations-keep-retained-view
  (and (equal (fn-osr-retained-view (fn-sn-prepare s record)) (fn-osr-retained-view s))
       (equal (fn-osr-retained-view (fn-sn-prepare-retention s record)) (fn-osr-retained-view s))
       (equal (fn-osr-retained-view (fn-sn-prepare-identity s record)) (fn-osr-retained-view s))
       (equal (fn-osr-retained-view (fn-sn-prepare-consumer s record)) (fn-osr-retained-view s))
       (equal (fn-osr-retained-view (fn-sn-prepare-topic s record)) (fn-osr-retained-view s))
       (equal (fn-osr-retained-view (fn-sn-refuse-reservation s txid)) (fn-osr-retained-view s))
       (equal (fn-osr-retained-view (fn-sn-known-abort s)) (fn-osr-retained-view s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                             '((:definition fn-osr-retained-view)
                              (:definition fn-sf-abort-completion)
                              (:definition fn-sf-candidatep) (:definition fn-sf-prepare-record)
                              (:definition fn-sf-prepublish-abort)
                              (:definition fn-sf-record-file-result)
                              (:definition fn-sf-record-pair)
                              (:definition fn-sf-refuse-reservation)
                              (:definition fn-sn-known-abort)
                              (:definition fn-sn-known-abort-file-start)
                              (:definition fn-sn-known-abort-files) (:definition fn-sn-prepare)
                              (:definition fn-sn-prepare-consumer)
                              (:definition fn-sn-prepare-identity)
                              (:definition fn-sn-prepare-retention)
                              (:definition fn-sn-prepare-topic)
                              (:definition fn-sn-refuse-reservation)
                              (:definition fn-stxk-context-kind) (:definition fn-th-at)
                              (:definition natp) (:executable-counterpart equal)
                              (:executable-counterpart zp)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:rewrite fn-cstp-held-kind-facts)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-update-retained-selectors)
                              (:rewrite fn-sf-records-field-of-fn-sf-make-fields)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-scalars-of-fn-sf-make-fields)
                              (:rewrite fn-sf-successes-field-of-fn-sf-make-fields)
                              (:type-prescription fn-held-p) (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep))))))

(defthm fn-osr-io-keeps-retained-view
  (implies (fn-osr-retainedp s)
           (equal (fn-osr-retained-view (fn-sn-io s operation result))
                  (fn-osr-retained-view s)))
  :hints (("Goal"
           :use ((:instance fn-csi-take-append-after-prefix
                            (n (fn-sn-identity-next s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (suffix (list (fn-sf-record-candidate (fn-sn-files s))))))
           :in-theory (union-theories (theory 'minimal-theory)
                             '((:compound-recognizer natp-compound-recognizer)
                              (:definition fn-osr-identity-prefixp) (:definition fn-osr-livep)
                              (:definition fn-osr-retained-view) (:definition fn-osr-retainedp)
                              (:definition fn-sf-frontier-dir-result)
                              (:definition fn-sf-frontier-file-result)
                              (:definition fn-sf-frontier-replace-result)
                              (:definition fn-sf-record-dir-result)
                              (:definition fn-sf-record-file-result)
                              (:definition fn-sf-record-link-result)
                              (:definition fn-sf-record-pair)
                              (:definition fn-sf-recovery-barrier)
                              (:definition fn-sf-start-frontier) (:definition fn-sn-file-step)
                              (:definition fn-sn-io) (:definition not)
                              (:forward-chaining fn-cstp-relation-is-statep)
                              (:forward-chaining fn-cstp-sn-statep-files)
                              (:forward-chaining fn-osr-source-fields-typed)
                              (:rewrite fn-cstp-sn-update-fields)
                              (:rewrite fn-osr-update-retained-selectors)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-kept)
                              (:rewrite fn-sf-records-of-fn-sf-make-fields-snoc)
                              (:type-prescription fn-cst-relation)
                              (:type-prescription fn-sf-statep)
                              (:type-prescription fn-sn-statep) (:type-prescription len))))))
