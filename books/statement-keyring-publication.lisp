; Retained snapshot resolution is a carried invariant, established at open.
; The live publication applies one event; it does not recontext history.
(in-package "ACL2")
(include-book "hybrid-lifecycle-store-invariants")
(include-book "statement-recover-stream")

(defun fn-skp-resolvedp (s)
 (declare (xargs :guard t))
 (and (equal (fn-sn-keyring s) (fn-ssk-keyring-of-snapshots (fn-sn-keyring-snapshots s)))
      (equal (fn-sn-keyring-generation s) (fn-ssk-generation (fn-sn-keyring-snapshots s)))))

; A completed snapshot either prepends a genuinely new snapshot or retains
; the old snapshot list. A historical repeat advances only the cursor.
(local (defthm fn-skp-snapshot-step-has-exact-snapshot-effect
 (implies (fn-stxk-p record)
  (equal (fn-stxk-context-snapshots (fn-replay-identity-step (fn-sn-identity-context s) record))
   (if (equal (fn-stxk-context-current-generation
                (fn-replay-identity-step (fn-sn-identity-context s) record))
              (fn-stxk-context-current-generation (fn-sn-identity-context s)))
       (fn-sn-keyring-snapshots s)
     (cons record (fn-sn-keyring-snapshots s)))))
 :hints (("Goal" :in-theory
  (e/d (fn-replay-identity-step fn-sn-identity-context fn-replay-identity-wire
        fn-stxk-apply-snapshot fn-stxk-fault fn-stxk-context fn-stxk-p
        fn-record-uint32p)
       (fn-stxe-p fn-stxa-p fn-hsig-keyring-snapshot-value
        fn-replay-identity-advance))))))

(defthm fn-skp-finish-identity-snapshot-preserves-resolution
 (implies (and (fn-skp-resolvedp s) (fn-stxk-p record))
  (fn-skp-resolvedp (fn-sn-finish-identity s files record node)))
 :hints (("Goal" :in-theory
  (e/d (fn-skp-resolvedp fn-sn-finish-identity fn-ssk-generation)
       (fn-stxk-p fn-replay-identity-step fn-sn-identity-context
        fn-ssk-apply-snapshot fn-ssk-keyring-of-snapshots)))))
(local (defthm fn-skp-resolution-of-with-consumer
 (equal (fn-skp-resolvedp (fn-sn-with-consumer s c)) (fn-skp-resolvedp s))
 :hints (("Goal" :in-theory (enable fn-skp-resolvedp)))))
(local (defthm fn-skp-resolution-of-with-topic
 (equal (fn-skp-resolvedp (fn-sn-with-topic s c)) (fn-skp-resolvedp s))
 :hints (("Goal" :in-theory (enable fn-skp-resolvedp)))))
(defthm fn-skp-finish-snapshot-preserves-resolution
 (implies (and (fn-skp-resolvedp s) (fn-stxk-p (fn-sn-completion-record s)))
  (fn-skp-resolvedp (fn-sn-finish s)))
 :hints (("Goal" :use ((:instance fn-hls-snapshot-disjoint-from-other-store-events
                              (event (fn-sn-completion-record s))))
  :in-theory (e/d (fn-sn-finish)
    (fn-skp-resolvedp fn-sn-completion-enabledp fn-stxk-p fn-stxe-p fn-stxa-p
     fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp fn-sn-finish-identity
     fn-ssk-keyring-of-snapshots fn-ssk-generation)))))
(local (defthm fn-skp-nonsnapshot-keeps-snapshots
 (implies (not (fn-stxk-p record))
  (equal (fn-stxk-context-snapshots (fn-replay-identity-step (fn-sn-identity-context s) record))
         (fn-sn-keyring-snapshots s)))
 :hints (("Goal" :in-theory
  (e/d (fn-replay-identity-step fn-sn-identity-context fn-replay-identity-wire
        fn-stxk-fault fn-stxk-context fn-stxk-apply-verdict
        fn-replay-identity-advance fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict)
       (fn-stxk-p fn-stxe-p fn-stxa-p fn-stxk-apply-snapshot
        fn-hsig-keyring-snapshot-value fn-stxe-decode-exact))))))
(defthm fn-skp-finish-identity-preserves-resolution
 (implies (fn-skp-resolvedp s)
  (fn-skp-resolvedp (fn-sn-finish-identity s files record node)))
 :hints (("Goal" :cases ((fn-stxk-p record))
  :in-theory (e/d (fn-skp-resolvedp fn-sn-finish-identity fn-ssk-generation)
   (fn-stxk-p fn-replay-identity-step fn-sn-identity-context
    fn-ssk-keyring-of-snapshots fn-ssk-apply-snapshot)))))


(local (defthm fn-skp-resolution-of-update-indexed
 (equal (fn-skp-resolvedp (fn-sn-update-indexed s files node index)) (fn-skp-resolvedp s))
 :hints (("Goal" :in-theory (enable fn-skp-resolvedp fn-sn-update-indexed)))))
(local (defthm fn-skp-resolution-of-update-accepted
 (equal (fn-skp-resolvedp (fn-sn-update-accepted s files node index msgid verdict))
        (fn-skp-resolvedp s))
 :hints (("Goal" :in-theory (enable fn-skp-resolvedp fn-sn-update-accepted)))))
(local (defthm fn-skp-resolution-of-advance
 (equal (fn-skp-resolvedp (fn-sn-advance-identity-next s)) (fn-skp-resolvedp s))
 :hints (("Goal" :in-theory (enable fn-skp-resolvedp fn-sn-advance-identity-next)))))
(defthm fn-skp-finish-preserves-resolution
 (implies (fn-skp-resolvedp s) (fn-skp-resolvedp (fn-sn-finish s)))
 :hints (("Goal" :in-theory (e/d (fn-sn-finish)
   (fn-skp-resolvedp fn-sn-completion-enabledp fn-sn-completion-record
    fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp fn-stxk-p fn-stxe-p fn-stxa-p
    fn-sn-finish-identity fn-sn-advance-identity-next fn-sn-update-indexed fn-sn-update-accepted
    fn-ssk-generation fn-ssk-keyring-of-snapshots)))))

(defthm fn-skp-replay-establishes-resolution
 (fn-skp-resolvedp (fn-sn-update-replayed s files node index identity))
 :hints (("Goal" :in-theory (e/d (fn-skp-resolvedp)
  (fn-ssk-keyring-of-snapshots fn-ssk-generation fn-sn-update-replayed)))))
(in-theory (disable fn-skp-resolvedp))
