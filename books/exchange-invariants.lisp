; fn exchange ingest invariants.
;
; These theorems concern the pure finite fact-store transition in exchange.lisp.
; They do not model batch serialization, durable acceptance, signatures, or a
; peer's honesty.  In particular, capacity is charged by distinct retained facts
; in this model, not by bytes or storage obligations.
;
; The exchange recognizers, ingest and the set lemmas are opened locally;
; nothing here opens a record.  The traces carry `fn-exchange-statep'.

(in-package "ACL2")

(include-book "exchange")

(local (in-theory (enable fn-exchange-factp fn-exchange-policyp
                          fn-exchange-statep fn-exchange-initial-state
                          fn-exchange-admissible-batchp fn-exchange-ingest
                          fn-exchange-set-vocabulary)))

; -----------------------------------------------------------------------------
; Set and well-formedness facts used by the ingest transition.

(defthm fn-exchange-batch-validp-implies-fact-listp
  (implies (fn-exchange-batch-validp batch policy)
           (fn-exchange-fact-listp batch))
  :hints (("Goal" :induct (fn-exchange-batch-validp batch policy)
           :in-theory (enable fn-exchange-batch-validp
                              fn-exchange-fact-listp
                              fn-exchange-validatep))))

(defthm fn-exchange-add-fact-preserves-fact-listp
  (implies (and (fn-exchange-factp fact)
                (fn-exchange-fact-listp facts))
           (fn-exchange-fact-listp (fn-exchange-add-fact fact facts)))
  :hints (("Goal" :in-theory (enable fn-exchange-add-fact
                                      fn-exchange-fact-listp))))

(defthm fn-exchange-add-fact-preserves-no-duplicatesp
  (implies (fn-exchange-no-duplicatesp facts)
           (fn-exchange-no-duplicatesp (fn-exchange-add-fact fact facts)))
  :hints (("Goal" :cases ((member-equal fact facts))
           :in-theory (enable fn-exchange-add-fact
                              fn-exchange-no-duplicatesp))))

(defthm fn-exchange-merge-preserves-fact-listp
  (implies (and (fn-exchange-batch-validp batch policy)
                (fn-exchange-fact-listp facts))
           (fn-exchange-fact-listp (fn-exchange-merge batch facts)))
  :hints (("Goal" :induct (fn-exchange-merge batch facts)
           :in-theory (enable fn-exchange-merge
                              fn-exchange-batch-validp
                              fn-exchange-validatep))))

(defthm fn-exchange-merge-preserves-no-duplicatesp
  (implies (fn-exchange-no-duplicatesp facts)
           (fn-exchange-no-duplicatesp (fn-exchange-merge batch facts)))
  :hints (("Goal" :induct (fn-exchange-merge batch facts)
           :in-theory (enable fn-exchange-merge))))

(defthm fn-exchange-add-fact-length
  (equal (len (fn-exchange-add-fact fact facts))
         (if (member-equal fact facts)
             (len facts)
           (+ 1 (len facts))))
  :hints (("Goal" :in-theory (enable fn-exchange-add-fact))))

; `new-facts' uses the same evolving membership test as `merge'.  Thus this is
; an exact distinct-fact charge, including duplicates within the batch.
(defthm fn-exchange-merge-length-is-old-plus-new
  (equal (len (fn-exchange-merge batch facts))
         (+ (len facts) (len (fn-exchange-new-facts batch facts))))
  :hints (("Goal" :induct (fn-exchange-merge batch facts)
           :in-theory (enable fn-exchange-merge
                              fn-exchange-new-facts
                              fn-exchange-add-fact))))

(defthm fn-exchange-subsetp-merge-right
  (fn-exchange-subsetp facts (fn-exchange-merge batch facts))
  :hints (("Goal" :induct (fn-exchange-subsetp
                             facts (fn-exchange-merge batch facts))
           :in-theory (enable fn-exchange-subsetp
                              fn-exchange-merge-member))))

(defthm fn-exchange-subsetp-transitive
  (implies (and (fn-exchange-subsetp xs ys)
                (fn-exchange-subsetp ys zs))
           (fn-exchange-subsetp xs zs))
  :hints (("Goal" :induct (fn-exchange-subsetp xs ys)
           :in-theory (enable fn-exchange-subsetp))))

; -----------------------------------------------------------------------------
; One actual ingest: state preservation, capacity accounting, and evidence.

(defthm fn-exchange-ingest-preserves-statep
  (implies (fn-exchange-statep s)
           (fn-exchange-statep (fn-exchange-ingest s batch policy)))
  :hints
  (("Goal" :cases ((fn-exchange-admissible-batchp s batch policy))
    :use ((:instance fn-exchange-merge-preserves-fact-listp
                     (facts (fn-exchange-facts s)))
          (:instance fn-exchange-merge-preserves-no-duplicatesp
                     (facts (fn-exchange-facts s)))
          (:instance fn-exchange-merge-length-is-old-plus-new
                     (facts (fn-exchange-facts s)))))))

(defthm fn-exchange-admitted-ingest-exact-distinct-count
  (implies (fn-exchange-admissible-batchp s batch policy)
           (equal (len (fn-exchange-facts (fn-exchange-ingest s batch policy)))
                  (+ (len (fn-exchange-facts s))
                     (len (fn-exchange-new-facts
                           batch (fn-exchange-facts s))))))
  :hints (("Goal" :use ((:instance fn-exchange-merge-length-is-old-plus-new
                                   (facts (fn-exchange-facts s)))))))

(defthm fn-exchange-ingest-preserves-existing-facts
  (implies (fn-exchange-statep s)
           (fn-exchange-subsetp
            (fn-exchange-facts s)
            (fn-exchange-facts (fn-exchange-ingest s batch policy))))
  :hints (("Goal" :cases ((fn-exchange-admissible-batchp s batch policy)))))

(defthm fn-exchange-ingest-retains-existing-fact
  (implies (and (fn-exchange-statep s)
                (member-equal fact (fn-exchange-facts s)))
           (member-equal fact
                         (fn-exchange-facts
                          (fn-exchange-ingest s batch policy))))
  :hints (("Goal" :use ((:instance fn-exchange-ingest-preserves-existing-facts))
           :in-theory (enable fn-exchange-subsetp))))

; If an admitted batch carries an object whose message identity conflicts with
; a stored object, both pieces of evidence remain.  The conclusion deliberately
; says nothing about selecting a winner.
(defthm fn-exchange-admitted-ingest-retains-conflicting-evidence
  (implies
   (and (fn-exchange-admissible-batchp s batch policy)
        (member-equal stored (fn-exchange-facts s))
        (member-equal incoming batch)
        (fn-exchange-object-for-messagep message-id stored)
        (fn-exchange-object-for-messagep message-id incoming)
        (not (equal (fn-exchange-content-id stored)
                    (fn-exchange-content-id incoming))))
   (and (member-equal stored
                      (fn-exchange-facts (fn-exchange-ingest s batch policy)))
        (member-equal incoming
                      (fn-exchange-facts (fn-exchange-ingest s batch policy)))))
  :hints (("Goal"
           :use ((:instance fn-exchange-admitted-ingest-member (x stored))
                 (:instance fn-exchange-admitted-ingest-member (x incoming)))
           :in-theory (disable fn-exchange-ingest
                               fn-exchange-admissible-batchp))))

; Validation refusal is atomic, before capacity is considered.
(defthm fn-exchange-invalid-batch-refuses-atomically
  (implies (not (fn-exchange-batch-validp batch policy))
           (equal (fn-exchange-ingest s batch policy) s))
  :hints (("Goal" :use ((:instance fn-exchange-ingest-refusal-is-no-op)))))

(defthm fn-exchange-unknown-schema-batch-refuses-atomically
  (implies (not (fn-exchange-known-schemap
                 (fn-exchange-schema fact) policy))
           (equal (fn-exchange-ingest s (cons fact batch) policy) s))
  :hints (("Goal" :use ((:instance fn-exchange-invalid-batch-refuses-atomically
                                   (batch (cons fact batch))))
           :in-theory (enable fn-exchange-batch-validp
                              fn-exchange-validatep))))

(defthm fn-exchange-unauthorized-batch-refuses-atomically
  (implies (not (fn-exchange-authorizedp
                 (fn-exchange-provenance fact) policy))
           (equal (fn-exchange-ingest s (cons fact batch) policy) s))
  :hints (("Goal" :use ((:instance fn-exchange-invalid-batch-refuses-atomically
                                   (batch (cons fact batch))))
           :in-theory (enable fn-exchange-batch-validp
                              fn-exchange-validatep))))

; -----------------------------------------------------------------------------
; Finite traces of actual calls to `fn-exchange-ingest'.

(defun fn-exchange-ingest-trace (s batches policy)
  (declare (xargs :guard (fn-exchange-statep s)
                  :guard-hints (("Goal" :in-theory (disable fn-exchange-statep
                                                            fn-exchange-ingest)))))
  (if (consp batches)
      (fn-exchange-ingest-trace
       (fn-exchange-ingest s (car batches) policy)
       (cdr batches)
       policy)
    s))

(defthm fn-exchange-ingest-trace-preserves-statep
  (implies (fn-exchange-statep s)
           (fn-exchange-statep
            (fn-exchange-ingest-trace s batches policy)))
  :hints (("Goal" :induct (fn-exchange-ingest-trace s batches policy)
           :in-theory (disable fn-exchange-statep fn-exchange-ingest))))

(defthm fn-exchange-ingest-trace-preserves-facts
  (implies (fn-exchange-statep s)
           (fn-exchange-subsetp
            (fn-exchange-facts s)
            (fn-exchange-facts
             (fn-exchange-ingest-trace s batches policy))))
  :hints
  (("Goal" :induct (fn-exchange-ingest-trace s batches policy)
    :in-theory (disable fn-exchange-statep fn-exchange-ingest))
   ("Subgoal *1/1"
    :use ((:instance fn-exchange-ingest-preserves-existing-facts)
          (:instance fn-exchange-subsetp-transitive
                     (xs (fn-exchange-facts s))
                     (ys (fn-exchange-facts
                          (fn-exchange-ingest s (car batches) policy)))
                     (zs (fn-exchange-facts
                          (fn-exchange-ingest-trace
                           (fn-exchange-ingest s (car batches) policy)
                           (cdr batches) policy))))))))

; A policy trace permits the authority policy to change between actual ingest
; calls.  It stops when either finite input list ends.
(defun fn-exchange-policy-ingest-trace (s batches policies)
  (declare (xargs :guard (fn-exchange-statep s)
                  :guard-hints (("Goal" :in-theory (disable fn-exchange-statep
                                                            fn-exchange-ingest)))))
  (if (and (consp batches) (consp policies))
      (fn-exchange-policy-ingest-trace
       (fn-exchange-ingest s (car batches) (car policies))
       (cdr batches)
       (cdr policies))
    s))

(defthm fn-exchange-policy-ingest-trace-preserves-statep
  (implies (fn-exchange-statep s)
           (fn-exchange-statep
            (fn-exchange-policy-ingest-trace s batches policies)))
  :hints (("Goal" :induct (fn-exchange-policy-ingest-trace s batches policies)
           :in-theory (disable fn-exchange-statep fn-exchange-ingest))))

(defthm fn-exchange-policy-ingest-trace-preserves-facts
  (implies (fn-exchange-statep s)
           (fn-exchange-subsetp
            (fn-exchange-facts s)
            (fn-exchange-facts
             (fn-exchange-policy-ingest-trace s batches policies))))
  :hints
  (("Goal" :induct (fn-exchange-policy-ingest-trace s batches policies)
    :in-theory (disable fn-exchange-statep fn-exchange-ingest))
   ("Subgoal *1/1"
    :use ((:instance fn-exchange-ingest-preserves-existing-facts
                     (batch (car batches)) (policy (car policies)))
          (:instance fn-exchange-subsetp-transitive
                     (xs (fn-exchange-facts s))
                     (ys (fn-exchange-facts
                          (fn-exchange-ingest s (car batches) (car policies))))
                     (zs (fn-exchange-facts
                          (fn-exchange-policy-ingest-trace
                           (fn-exchange-ingest s (car batches) (car policies))
                           (cdr batches) (cdr policies)))))))))

; This describes the observable effect of a changed policy that refuses its
; current batch: the trace continues from the exact old state.
(defthm fn-exchange-policy-ingest-trace-invalid-head-is-no-op
  (implies (and (consp batches)
                (consp policies)
                (not (fn-exchange-batch-validp (car batches) (car policies))))
           (equal (fn-exchange-policy-ingest-trace s batches policies)
                  (fn-exchange-policy-ingest-trace s
                                                   (cdr batches)
                                                   (cdr policies))))
  :hints (("Goal"
           :use ((:instance fn-exchange-invalid-batch-refuses-atomically
                            (batch (car batches))
                            (policy (car policies))))
           :in-theory (disable fn-exchange-ingest
                               fn-exchange-invalid-batch-refuses-atomically))))

; -----------------------------------------------------------------------------
; Export.  Keystones stay enabled: the ingest preservation, count, retention
; and refusal theorems and the four trace theorems.  The set and length lemmas
; are proof vocabulary and are withdrawn.
(deftheory fn-exchange-invariants-vocabulary
  '(fn-exchange-batch-validp-implies-fact-listp
    fn-exchange-add-fact-preserves-fact-listp
    fn-exchange-add-fact-preserves-no-duplicatesp
    fn-exchange-merge-preserves-fact-listp
    fn-exchange-merge-preserves-no-duplicatesp
    fn-exchange-add-fact-length
    fn-exchange-merge-length-is-old-plus-new
    fn-exchange-subsetp-merge-right
    fn-exchange-subsetp-transitive))
(in-theory (disable fn-exchange-invariants-vocabulary))
