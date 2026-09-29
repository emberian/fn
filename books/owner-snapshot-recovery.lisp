; Live capture/recovery correspondence.  Relations below are proof vocabulary:
; a capture takes the carried Store pointer, not a new scan of its history.
; PRF-1068 / HST-040.  This book does not assume successful observed open.
(in-package "ACL2")
(include-book "config-store-steps")
(include-book "topic-history-store-invariants")
(include-book "owner-commit-ocl")

(local (in-theory (disable (tau-system))))

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
  :hints (("Goal" :in-theory
           (e/d (fn-osr-context-view fn-stxk-apply-snapshot fn-stxk-fault
                 fn-stxk-context)
                (fn-stxk-p fn-stxk-find fn-stxk-same-snapshotp)))))

(defthm fn-osr-context-view-verdict-congruence
  (implies (equal (fn-osr-context-view a) (fn-osr-context-view b))
           (equal (fn-osr-context-view (fn-stxk-apply-verdict a event))
                  (fn-osr-context-view (fn-stxk-apply-verdict b event))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-osr-context-view fn-stxk-apply-verdict fn-stxk-fault
                 fn-stxk-context)
                (fn-stxe-p fn-stxk-find)))))

(defthm fn-osr-context-view-step-congruence
  (implies (equal (fn-osr-context-view a) (fn-osr-context-view b))
           (equal (fn-osr-context-view (fn-replay-identity-step a event))
                  (fn-osr-context-view (fn-replay-identity-step b event))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-osr-context-view fn-replay-identity-step
                 fn-replay-identity-advance fn-replay-apply-carried-verdict
                 fn-replay-apply-revoked-verdict fn-stxk-fault fn-stxk-context
                 fn-stxk-apply-snapshot fn-stxk-apply-verdict)
                (fn-stxk-p fn-stxe-p fn-stxa-p fn-stxa-bindsp
                 fn-replay-identity-wire fn-hsig-article-event-carried-bindsp
                 fn-hsig-article-event-revoked-bindsp
                 fn-hsig-article-event-snapshot-bindsp
                 fn-hsig-revoked-tombstone-bindsp
                 fn-hsig-article-event-carrier-keys
                 fn-stxe-decode-exact fn-stxk-find
                 fn-record-shape-vocabulary fn-record-record-vocabulary)))))

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
  :hints (("Goal" :in-theory
           (e/d (fn-osr-context-canonicalp fn-replay-identity-step
                 fn-replay-identity-advance fn-replay-apply-carried-verdict
                 fn-replay-apply-revoked-verdict fn-stxk-fault fn-stxk-context
                 fn-stxk-apply-snapshot fn-stxk-apply-verdict)
                (fn-stxk-p fn-stxe-p fn-stxa-p fn-stxa-bindsp
                 fn-replay-identity-wire fn-hsig-article-event-carried-bindsp
                 fn-hsig-article-event-revoked-bindsp
                 fn-hsig-article-event-snapshot-bindsp
                 fn-hsig-revoked-tombstone-bindsp
                 fn-hsig-article-event-carrier-keys
                 fn-stxe-decode-exact fn-stxk-find fn-stxk-same-snapshotp
                 fn-record-shape-vocabulary fn-record-record-vocabulary)))))

(defthm fn-osr-loop-ok-implies-input-ok
  (implies (equal (fn-stxk-context-kind
                  (fn-replay-identity-loop records ctx)) :ok)
           (equal (fn-stxk-context-kind ctx) :ok))
  :hints (("Goal" :induct (fn-replay-identity-loop records ctx)
           :in-theory
           (e/d (fn-replay-identity-loop fn-replay-identity-step
                 fn-stxk-fault fn-stxk-context)
                (fn-store-event-p fn-stxk-p fn-stxe-p fn-stxa-p
                 fn-stxa-bindsp fn-hsig-article-event-snapshot-bindsp
                 fn-stxk-apply-snapshot fn-stxk-apply-verdict
                 fn-stxe-decode-exact fn-stxk-find
                 fn-record-shape-vocabulary fn-record-record-vocabulary)))))

(defthm fn-osr-loop-preserves-canonical-context
  (implies (and (fn-osr-context-canonicalp ctx)
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-loop records ctx)) :ok))
           (fn-osr-context-canonicalp
            (fn-replay-identity-loop records ctx)))
  :hints (("Goal" :induct (fn-replay-identity-loop records ctx)
           :in-theory
           (e/d (fn-replay-identity-loop fn-stxk-fault fn-stxk-context)
                (fn-store-event-p fn-replay-identity-step
                 fn-osr-context-canonicalp)))
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
           :in-theory
           (e/d (fn-replay-identity-loop fn-stxk-fault fn-stxk-context)
                (fn-store-event-p fn-replay-identity-step)))))

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
  :hints (("Goal" :in-theory
           (e/d (fn-sn-identity-context fn-sn-with-configuration
                 fn-sn-identity-next fn-sn-keyring-snapshots fn-store-event-nth)
                (fn-sn-make-v6)))))

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
           :in-theory (e/d (fn-osr-identity-prefixp fn-sn-io fn-sn-file-step
                            fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result
                            fn-sf-record-file-result
                            fn-sf-record-link-result
                            fn-sf-record-dir-result
                            fn-sf-recovery-barrier)
                           (fn-sn-update fn-sn-with-event-index fn-sn-make-v6
                            fn-cei-put fn-replay-identity fn-sn-statep
                            fn-sf-statep fn-csi-take-append-after-prefix)))))

(defthm fn-osr-prepare-consumer-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare-consumer s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-osr-identity-prefixp
                            fn-sn-prepare-consumer 
                            fn-sf-prepare-record)
                           (fn-sn-update fn-sn-make-v6 fn-replay-identity
                            fn-cpe-projection-step fn-replay-apply-record
                            fn-cpe-eventp fn-sn-statep fn-sf-statep)))))

(defthm fn-osr-prepare-article-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare s record)))
  :hints (("Goal"
           :in-theory (e/d (fn-osr-identity-prefixp fn-sn-prepare
                            fn-sf-prepare-record)
                           (fn-sn-update fn-sn-make-v6 fn-replay-identity fn-sn-statep
                            fn-sf-statep fn-sn-prepare-node
                            fn-sn-record-bindsp)))))

(defthm fn-osr-prepare-retention-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare-retention s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-osr-identity-prefixp
                            fn-sn-prepare-retention 
                            fn-sf-prepare-record)
                           (fn-sn-update fn-sn-make-v6 fn-replay-identity
                            fn-replay-apply-retention-event
                            fn-store-retention-event-p
                            fn-sn-statep fn-sf-statep)))))

(defthm fn-osr-prepare-identity-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare-identity s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-osr-identity-prefixp
                            fn-sn-prepare-identity 
                            fn-sf-prepare-record)
                           (fn-sn-update fn-sn-make-v6 fn-replay-identity
                            fn-replay-apply-record fn-replay-identity-step
                            fn-stxe-p fn-stxk-p
                            fn-stxa-p fn-sn-statep fn-sf-statep)))))

(defthm fn-osr-prepare-topic-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-prepare-topic s event)))
  :hints (("Goal"
           :in-theory (e/d (fn-osr-identity-prefixp
                            fn-sn-prepare-topic fn-sf-prepare-record)
                           (fn-sn-update fn-sn-make-v6 fn-replay-identity fn-sn-statep
                            fn-sf-statep fn-th-topic-eventp
                            fn-th-prefix-step fn-replay-apply-record)))))

(defthm fn-osr-refuse-reservation-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :in-theory (e/d (fn-osr-identity-prefixp
                            fn-sn-refuse-reservation 
                            fn-sf-refuse-reservation)
                           (fn-sn-update fn-sn-make-v6 fn-replay-identity fn-sn-statep
                            fn-sf-statep fn-replay-advance-txid)))))

(defthm fn-osr-known-abort-preserves-identity-prefix
  (implies (fn-osr-identity-prefixp s)
           (fn-osr-identity-prefixp (fn-sn-known-abort s)))
  :hints (("Goal"
           :in-theory (e/d (fn-osr-identity-prefixp fn-sn-known-abort
                            fn-sn-known-abort-files
                            fn-sn-known-abort-file-start
                            fn-sf-prepublish-abort
                            fn-sf-abort-completion
                            fn-sf-record-file-result)
                           (fn-sn-update fn-sn-make-v6 fn-replay-identity fn-sn-statep
                            fn-sf-statep fn-replay-advance-txid
                            fn-node-complete)))))

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
           :in-theory
           (e/d (fn-sn-finish-identity fn-sn-identity-context
                 fn-osr-context-view fn-osr-context-canonicalp fn-stxk-context)
                (fn-sn-make-v6 fn-replay-identity-step fn-replay-verdict-pairs
                 fn-stx-index-add fn-sn-composite-delta fn-hstxa-p
                 fn-osr-step-preserves-canonical-context)))))

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

(defthm fn-osr-neutral-retained-event-is-not-wire-composite
  (implies (and (fn-store-event-p event)
                (not (fn-stxe-p event)) (not (fn-stxk-p event))
                (not (fn-hstxa-p event)))
           (not (fn-stxa-p event)))
  :hints (("Goal" :use ((:instance fn-stxa-p-forward-shape (x event))
                        (:instance fn-held-p-forward-shape (x event)))
           :in-theory
           (e/d (fn-stxa-shapep fn-held-shapep
                 fn-store-event-p fn-store-retention-event-p fn-cpe-eventp
                 fn-th-topic-eventp fn-th-local-admin-eventp fn-th-at
                 fn-cp-nth fn-store-event-nth)
                (fn-stxa-p fn-held-p fn-stxe-p fn-stxk-p fn-hstxa-p
                 fn-th-source-id-p fn-th-auth-ref-p fn-th-exact-octets-p)))))

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
           :in-theory (e/d (fn-sf-record-listp nth len)
                           (fn-store-event-p fn-store-event-sequence)))))

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
           :in-theory
           (e/d (fn-csi-livep fn-csi-completion-lastp
                 fn-sn-identity-sequencep fn-sf-completion-phasep)
                (fn-sn-statep fn-sf-statep fn-store-event-p
                 fn-store-event-sequence fn-sn-completion-enabledp
                 fn-osr-history-nth-event-sequence)))))

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

(defthm fn-osr-enabled-identity-step-ok
  (implies (and (fn-csi-livep s) (fn-sn-completion-enabledp s))
           (equal (fn-stxk-context-kind
                   (fn-replay-identity-step
                    (fn-sn-identity-context s) (fn-sn-completion-record s))) :ok))
  :hints (("Goal"
           :use (fn-osr-enabled-completion-is-next-event
                 (:instance fn-osr-neutral-retained-event-is-not-wire-composite
                            (event (fn-sn-completion-record s)))
                 (:instance fn-osr-neutral-step-is-advance
                            (ctx (fn-sn-identity-context s))
                            (event (fn-sn-completion-record s))))
           :in-theory
           (e/d (fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                 fn-sn-identity-context fn-stxk-context fn-replay-identity-advance)
                (fn-sn-statep fn-sf-statep fn-csi-livep
                 fn-replay-identity-step fn-replay-apply-record
                 fn-replay-apply-retention-event fn-store-retention-event-p
                 fn-stxe-p fn-stxk-p fn-stxa-p fn-hstxa-p
                 fn-cpe-eventp fn-th-topic-eventp fn-sn-record-bindsp
                 fn-cpe-projection-step fn-th-prefix-step
                 fn-osr-enabled-completion-is-next-event)))))

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
                 (:instance fn-osr-neutral-step-is-advance
                            (ctx (fn-sn-identity-context s))
                            (event (fn-sn-completion-record s))))
           :in-theory
           (e/d (fn-sn-finish)
                (fn-sn-identity-context fn-osr-context-view
                 fn-sn-advance-identity-next fn-sn-update-indexed
                 fn-sn-update-accepted fn-replay-identity-advance
                 fn-sn-make-v6 fn-sn-finish-identity fn-sn-completion-enabledp
                 fn-sn-completion-record fn-sn-statep fn-sf-statep
                 fn-csi-livep fn-replay-identity-step fn-cpe-projection-step
                 fn-th-prefix-step fn-replay-apply-record
                 fn-replay-apply-retention-event fn-sn-composite-delta
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp
                 fn-osr-enabled-completion-is-next-event
                 fn-osr-enabled-identity-step-ok)))))

(defthm fn-osr-step-kind-congruence
  (implies (equal (fn-osr-context-view a) (fn-osr-context-view b))
           (equal (fn-stxk-context-kind (fn-replay-identity-step a event))
                  (fn-stxk-context-kind (fn-replay-identity-step b event))))
  :rule-classes nil
  :hints (("Goal" :use fn-osr-context-view-step-congruence
           :in-theory (e/d (fn-osr-context-view)
                           (fn-replay-identity-step)))))

(defthm fn-osr-finish-preserves-identity-prefix
  (implies (and (fn-osr-identity-prefixp s) (fn-csi-livep s))
           (fn-osr-identity-prefixp (fn-sn-finish s)))
  :hints (("Goal"
           :do-not '(preprocess)
           :cases ((fn-sn-completion-enabledp s))
           :use (fn-sn-finish-disabled-is-no-op
                 fn-snt-finish-image
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
           :in-theory
           (e/d (fn-osr-identity-prefixp fn-csi-livep
                 fn-csi-completion-lastp fn-sn-identity-sequencep
                 fn-sf-completion-phasep)
                (fn-sn-finish fn-sn-completion-enabledp fn-replay-identity
                 fn-replay-identity-step fn-sn-statep fn-sf-statep
                 fn-osr-identity-append-one fn-osr-enabled-completion-is-next-event
                 fn-osr-enabled-identity-step-ok fn-osr-finish-context-view)))))

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
           :in-theory
           (e/d (fn-osr-identity-prefixp fn-csi-livep
                 fn-sn-identity-sequencep fn-sf-completion-phasep)
                (fn-replay-identity fn-sn-statep fn-sf-statep)))))

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
           :in-theory
           (e/d (fn-sti-livep fn-sti-completed-prefixp fn-csi-livep
                 fn-sn-identity-sequencep fn-sf-completion-phasep)
                (fn-th-prefix-project fn-sn-statep fn-sf-statep)))))

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
           :in-theory
           (e/d (fn-sn-completion-record fn-sti-livep fn-sti-completed-prefixp fn-csi-livep
                 fn-csi-completed-prefixp fn-csi-completion-lastp
                 fn-sn-identity-sequencep fn-osr-identity-prefixp)
                (fn-sn-find-record fn-cpo-configure-durable fn-sn-statep fn-sf-statep
                 fn-replay-identity fn-th-prefix-step fn-th-prefix-project
                 fn-cpe-projection-replay fn-osr-configure-durable-keeps-projections)))))

(in-theory (disable fn-osr-livep))


; Recovery construction typing; no successful-open premise.
(local
 (defthm fn-osr-verdict-listp-of-replay-verdict-pairs
   (fn-sn-verdict-listp (fn-replay-verdict-pairs events))
   :hints (("Goal" :induct (fn-replay-verdict-pairs events)
            :in-theory (enable fn-replay-verdict-pairs fn-sn-verdict-listp
                               fn-stx-make-verdict fn-stx-verdict-token
                               fn-stx-verdict-generation fn-stxe-tokenp
                               fn-stxe-p fn-record-msgidp fn-record-uint32p)))))

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
   :hints (("Goal" :in-theory
            (enable fn-sn-statep fn-sn-shapep fn-sn-with-consumer
                    fn-sn-make-v6 fn-sn-groups fn-sn-capacity fn-sn-files
                    fn-sn-node fn-sn-keyring fn-sn-keyring-generation
                    fn-sn-verdicts fn-sn-keyring-snapshots
                    fn-sn-identity-next)))))

(local
 (defthm fn-osr-with-topic-preserves-state
   (implies (fn-sn-statep s)
            (fn-sn-statep (fn-sn-with-topic s topic)))
   :hints (("Goal" :in-theory
            (enable fn-sn-statep fn-sn-shapep fn-sn-with-topic
                    fn-sn-make-v6 fn-sn-groups fn-sn-capacity fn-sn-files
                    fn-sn-node fn-sn-keyring fn-sn-keyring-generation
                    fn-sn-verdicts fn-sn-keyring-snapshots
                    fn-sn-identity-next)))))

(local
 (defthm fn-osr-with-event-index-preserves-state
   (implies (fn-sn-statep s)
            (fn-sn-statep (fn-sn-with-event-index s event-index)))
   :hints (("Goal" :in-theory
            (enable fn-sn-statep fn-sn-shapep fn-sn-with-event-index
                    fn-sn-make-v6 fn-sn-groups fn-sn-capacity fn-sn-files
                    fn-sn-node fn-sn-keyring fn-sn-keyring-generation
                    fn-sn-verdicts fn-sn-keyring-snapshots
                    fn-sn-identity-next)))))

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
           :in-theory
           (e/d (fn-osr-livep fn-sti-livep fn-osr-capture
                 fn-cpo-history-relation fn-cpo-open-observed fn-cpo-install
                 fn-sn-open-okp fn-sn-open-ok fn-sn-open-shapep fn-sn-open-state
                 fn-sn-open-kind fn-sn-keyring fn-sn-keyring-generation
                 fn-sn-with-event-index fn-sn-with-topic fn-sn-with-consumer
                 fn-sn-update-replayed fn-sn-observed-seed fn-sn-make
                 fn-sn-make-v2 fn-osr-context-view fn-sn-identity-context
                 fn-stxk-context fn-sn-observed-topic-okp)
                (fn-osr-ready-has-configured-history
                 fn-osr-ready-identity-exact-view fn-csi-live-ready-exact-replay
                 fn-osr-ready-topic-exact
                 fn-sti-current-records-topic-ok-including-completed
                 fn-sn-make-v6 fn-sn-with-configuration fn-sn-statep
                 fn-cnode-statep fn-cpr-replay fn-cpr-loop fn-replay-identity
                 fn-replay-identity-loop fn-replay-advance-txid fn-sf-make
                 fn-node-initial-state fn-cnode-make fn-cnode-node fn-cnode-config
                 fn-cnode-domain-of fn-cfg-capacity fn-cfg-value
                 fn-th-at fn-th-prefix-project fn-cpe-projection-replay
                 fn-stx-index-empty fn-replay-verdict-pairs fn-csi-livep
                 fn-sti-completed-prefixp)))))

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
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-open-observed fn-sn-open-okp fn-cpo-install
                 fn-sn-with-event-index fn-sn-with-topic fn-sn-with-consumer
                 fn-sn-update-replayed fn-sn-open-ok fn-sn-open-state fn-sn-open-kind)
                (fn-sn-make-v6 fn-sn-with-configuration fn-sn-statep
                 fn-cnode-statep fn-cpr-replay fn-replay-identity
                 fn-cpe-projection-replay fn-th-prefix-project
                 fn-sn-observed-seed fn-replay-advance-txid)))))

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
           :in-theory
           (e/d (fn-osr-livep fn-sti-livep fn-sti-completed-prefixp
                 fn-csi-livep fn-csi-completed-prefixp fn-csi-completion-lastp
                 fn-sn-identity-sequencep fn-osr-identity-prefixp
                 fn-osr-context-view fn-osr-context-canonicalp
                 fn-sn-identity-context fn-stxk-context
                 fn-th-prefix-project fn-th-prefix-state
                 fn-sn-observed-historyp fn-sf-completion-phasep
                 fn-sf-record-phasep)
                (fn-sn-statep fn-sf-statep fn-cst-relation fn-cpo-open-observed
                 fn-replay-identity fn-replay-identity-loop fn-cpe-projection-replay
                 fn-th-prefix-loop fn-th-prefix-step
                 fn-replay-identity-ok-next-is-record-count
                 fn-osr-identity-ok-has-canonical-context
                 fn-cstp-prefix-loop-next fn-sn-open-state)))))

(defthm fn-osr-known-abort-preserves-topic-live
  (implies (fn-sti-livep s) (fn-sti-livep (fn-sn-known-abort s)))
  :hints (("Goal"
           :use (fn-sti-known-abort-preserves-consumer-live)
           :in-theory
           (e/d (fn-sti-livep fn-sti-completed-prefixp fn-sn-known-abort
                 fn-sn-known-abort-files fn-sn-known-abort-file-start
                 fn-sf-prepublish-abort fn-sf-abort-completion
                 fn-sf-record-file-result fn-sn-completion-record)
                (fn-sn-update fn-sn-find-record fn-sn-statep fn-sf-statep
                 fn-csi-livep fn-replay-advance-txid fn-node-complete
                 fn-th-prefix-project fn-th-prefix-step fn-th-topic-eventp)))))

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
  :hints (("Goal" :in-theory
           (e/d (fn-osr-independent-livep fn-snrt-step fn-snt-step)
                (fn-sti-livep fn-sn-prepare fn-sn-prepare-retention fn-sn-prepare-identity
                 fn-sn-prepare-consumer fn-sn-prepare-topic fn-sn-io fn-sn-finish
                 fn-sn-refuse-reservation fn-sn-known-abort fn-sn-statep
                 fn-csi-livep fn-sti-completed-prefixp fn-th-prefix-step
                 fn-th-topic-eventp fn-osr-identity-prefixp)))))

(defthm fn-osr-store-trace-preserves-independent-live
  (implies (and (fn-osr-independent-livep s) (fn-csi-no-crash-eventsp events))
           (fn-osr-independent-livep (fn-snrt-run s events)))
  :hints (("Goal" :induct (fn-snrt-run s events)
           :in-theory (e/d (fn-csi-no-crash-eventsp fn-snrt-run)
                           (fn-osr-independent-livep fn-snrt-step)))))

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
           :in-theory
           (e/d (fn-osr-livep fn-osr-capture fn-osr-context-view
                 fn-sn-identity-context fn-stxk-context fn-cpo-history-relation
                 fn-cnode-domain)
                (fn-cpo-open-observed fn-sn-statep fn-cst-relation fn-sti-livep
                 fn-osr-identity-prefixp fn-csi-livep fn-sf-statep fn-cpr-replay
                 fn-replay-identity fn-cpe-projection-replay fn-th-prefix-project
                 fn-cnode-statep fn-replay-advance-okp fn-replay-advance-txid
                 fn-osr-live-ready-capture-opens fn-osr-ready-identity-exact-view
                 fn-osr-ready-topic-exact fn-osr-ready-has-configured-history
                 fn-csi-live-ready-exact-replay
                 fn-cpo-open-success-has-historical-relation)))))
