; fn: the topic prepare's consumer-projection refusal is unreachable on every
; Store the consumer relation holds of (lane host-decisions-2, 2026-09-27;
; the open question of planning/evidence/host-decisions-2026-09-27.md item 3).
;
; books/owner-prepare-served.lisp fn-psrv-prepare-topic (the host's topic
; entry, through host/owner-host.lisp fn-owner-prepare-topic and
; books/owner-prepare-outcome.lisp fn-pout-prepare-topic) stages E only when
; the carried consumer projection admits E at the Store's next sequence,
; which fn-sn-prepare-topic does not test.  The question was whether that
; refusal arm is reachable.  Answer, in two parts:
;
;   * UNREACHABLE under the consumer relation: on a Store with fn-sn-statep
;     and fn-snt-consumerp (the carried consumer projection is the replay of
;     the record list and the next sequence is its length), whenever
;     fn-sn-prepare-topic would stage E the projection admits E
;     (fn-pout-staged-topic-passes-the-consumer-projection); so the entry's
;     Store is fn-sn-prepare-topic's exactly
;     (fn-pout-topic-entry-is-the-store-prepare-under-the-consumer-relation).
;     The u32 ceiling is not an exception: a staged candidate's sequence is
;     below it (fn-csi-candidate-sequence-below-max).  fn-csi-full-relationp,
;     which conjoins fn-snt-consumerp with the history relation, is preserved
;     by the Store's normal steps, crash and recovery
;     (books/consumer-store-invariants.lisp).
;   * NOT unreachable under the owner's carried invariant alone:
;     fn-lgoc-invariantp does not carry fn-snt-consumerp, so the test is what
;     lets fn-psrv-prepare-topic-preserves-invariant hold without it; the
;     corrupted-state witness in tests/acl2/owner-prepare-outcome-topic-tests
;     keeps fn-lgoc-invariantp, breaks the consumer frontier, and reaches the
;     refusal.
;
; This book shares the prefix `fn-pout-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "owner-prepare-outcome")
(include-book "consumer-store-invariants")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-snt-consumerp))))
(local
 (defthm fn-pout-consumer-frontier-of-replay
   (implies (and (equal (fn-cpe-projection-replay nil records 0) (list :ok c)) c)
            (equal (fn-cp-nth 3 c) (len records)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-csi-replay-keeps-frontier-aligned
                                    (s nil) (expected 0)))
            :in-theory (e/d (fn-csi-second-of-ok-by-definition)
                            (fn-cpe-projection-replay fn-cp-nth))))))

(defthm fn-pout-staged-topic-passes-the-consumer-projection
  (implies (and (fn-sn-statep s)
                (fn-snt-consumerp s)
                (not (equal (fn-sn-prepare-topic s e) s)))
           (eq (car (fn-cpe-projection-step (fn-sn-consumer s) e (fn-sn-identity-next s)))
               :ok))
  :hints (("Goal"
           :use ((:instance fn-psrv-sf-prepare-record-staged
                            (files (fn-sn-files s)) (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s)))
                 (:instance fn-pout-consumer-frontier-of-replay
                            (records (fn-sf-records (fn-sn-files s)))
                            (c (fn-sn-consumer s)))
                 (:instance fn-csi-topic-candidate-preserves-consumer-frontier
                            (records (fn-sf-records (fn-sn-files s)))
                            (frontier (fn-sf-frontier (fn-sn-files s)))
                            (event e) (consumer (fn-sn-consumer s)))
                 (:instance fn-cstp-sn-statep-files (st s)))
           :in-theory '(fn-sn-prepare-topic fn-snt-consumerp fn-sf-statep
                        fn-cstp-sn-update-fields fn-sf-record-phasep member-equal
                        fn-csi-second-of-ok-by-definition
                        car-cons cdr-cons
                        (:executable-counterpart equal)
                        (:executable-counterpart member-equal)
                        (:executable-counterpart fn-sf-record-phasep)
                        (:executable-counterpart natp)))))

(local
 (defthm fn-pout-projection-ok-is-a-store-event
   (implies (eq (car (fn-cpe-projection-step c e expected)) :ok)
            (fn-store-event-p e))
   :rule-classes nil
   :hints (("Goal" :in-theory '(fn-cpe-projection-step car-cons
                                (:executable-counterpart equal))))))

; The host's topic entry (fn-pout-prepare-topic, over fn-psrv-prepare-topic)
; leaves the Store fn-sn-prepare-topic leaves, on every Store the consumer
; relation holds of: its projection arm refuses nothing fn-sn-prepare-topic
; would stage.
(defthm fn-pout-topic-entry-is-the-store-prepare-under-the-consumer-relation
  (implies (and (fn-sn-statep (fn-sbud-oc-store oc))
                (fn-snt-consumerp (fn-sbud-oc-store oc)))
           (equal (fn-sbud-oc-store (mv-nth 1 (fn-pout-prepare-topic oc e)))
                  (fn-sn-prepare-topic (fn-sbud-oc-store oc) e)))
  :hints (("Goal"
           :use ((:instance fn-pout-prepare-topic-answers-the-store-change)
                 (:instance fn-psrv-prepare-topic-cases)
                 (:instance fn-pout-staged-topic-passes-the-consumer-projection
                            (s (fn-sbud-oc-store oc)))
                 (:instance fn-pout-projection-ok-is-a-store-event
                            (c (fn-sn-consumer (fn-sbud-oc-store oc)))
                            (expected (fn-sn-identity-next (fn-sbud-oc-store oc)))))
           :in-theory '(fn-sbud-oc-store fn-lgoc-store-of-owner-with-store))))
