; fn: replay the two physical journals in their actual coordinate systems.
;
; Configuration records have a dense sequence of their own and name the next
; unconsumed Store transaction id. Store events have their own dense sequence
; and consume a transaction id. A configuration at the same id precedes the
; event; several such configurations are ordered by their own sequence. This
; preserves the existing on-disk formats, including stores written before
; live reconfiguration. This fold runs only at recovery, never per command.

(in-package "ACL2")
(include-book "config-stream")

(defun fn-cpr-config-firstp (configs events)
  (declare (xargs :guard t))
  (and (consp configs)
       (or (not (consp events))
           (<= (nfix (fn-cfg-record-txid (car configs)))
               (nfix (fn-store-event-txid (car events)))))))

(defthm fn-cpr-config-firstp-has-config
  (implies (fn-cpr-config-firstp configs events) (consp configs))
  :hints (("Goal" :in-theory (enable fn-cpr-config-firstp))))

(defun fn-cpr-event-servedp (cn event)
  ; The served-domain check belongs only to events that create an article.
  ; A retention or identity-neutral event has no selected group; applying
  ; fn-cnode-apply-record to it would incorrectly refuse every such event.
  (declare (xargs :guard t))
  (cond ((fn-record-p event)
         (fn-cnode-selection-servedp (fn-cnode-config cn)
                                     (fn-record-groups event)))
        ((fn-stxa-p event)
         (fn-cnode-selection-servedp
          (fn-cnode-config cn)
          (fn-record-groups (fn-replay-composite-record event))))
        (t t)))

; The node invariant is carried, not re-checked (AGENTS.md: no whole-state
; revalidation; the pattern of `fn-replay-loop', books/replay.lisp).  The guard
; is (fn-cnode-statep cn); the :logic bodies are the original total ones, so
; every theorem about this fold keeps its statement.  The executable path
; tests the recognizer on neither the incoming node nor the one-record
; result: under the guard a result is a configured node exactly when it is
; non-NIL (`fn-cpr-apply-event-statep-iff-consp', below).  Before this, the
; fold ran the whole-node recognizer three times per replayed event, so the
; per-record replay cost grew with the history (planning/evidence/
; bounds-p3-2026-09-25.md, finding 2).
(defun fn-cpr-apply-event (cn event)
  ; Replay uses the same Store-event interpreter as the standalone Store.
  (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil))
  (if (and (mbe :logic (fn-cnode-statep cn) :exec t)
           (fn-store-event-p event)
           (fn-cpr-event-servedp cn event))
      (let ((next (fn-replay-apply-record (fn-cnode-node cn) event)))
        (if (and (consp next)
                 (mbe :logic (fn-node-statep next) :exec t))
            (fn-cnode-make next (fn-cnode-config cn))
          nil))
    nil))

(verify-guards fn-cpr-apply-event
  :hints (("Goal"
           :use ((:instance fn-replay-apply-record-non-nil-is-node-state
                            (node (fn-cnode-node cn)) (record event)))
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-event-servedp fn-record-p fn-stxa-p
                            fn-store-event-p fn-node-statep
                            fn-replay-apply-record
                            fn-replay-apply-record-non-nil-is-node-state)))))

; -----------------------------------------------------------------------------
; The carried invariant: one event preserves it.

(local (defthm fn-cpr-advance-keeps-groups
  (equal (fn-state-groups
          (fn-node-acceptance (fn-replay-advance-txid node recorded-txid)))
         (fn-state-groups (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

(local
 (defthm fn-cpr-retain-release-keeps-capacity-by-definition
   (equal (fn-retain-capacity
           (fn-retain-release retention id subject kind evidence))
          (fn-retain-capacity retention))
   :hints (("Goal" :in-theory (enable fn-retain-release)))))

(local
 (defthm fn-cpr-retain-admit-keeps-capacity-by-definition
   (equal (fn-retain-capacity
           (fn-retain-admit retention id subject kind evidence charge))
          (fn-retain-capacity retention))
   :hints (("Goal" :in-theory (enable fn-retain-admit)))))

; The same fact node-config proves locally for fn-cnode-apply-record
; (fn-cnode-replay-apply-record-keeps-groups-and-capacity), restated here
; because that book keeps it local.
(local (defthm fn-cpr-replay-apply-record-keeps-groups-and-capacity
  (implies (and (fn-node-statep node)
                (consp (fn-replay-apply-record node record)))
           (and (equal (fn-state-groups
                        (fn-node-acceptance (fn-replay-apply-record node record)))
                       (fn-state-groups (fn-node-acceptance node)))
                (equal (fn-retain-capacity
                        (fn-node-retention (fn-replay-apply-record node record)))
                       (fn-retain-capacity (fn-node-retention node)))))
  :hints (("Goal"
           :in-theory (e/d (fn-replay-apply-record
                            fn-node-prepare-preserves-state
                            fn-replay-advance-preserves-node-statep
                            fn-cnode-node-complete-keeps-groups-and-capacity
                            fn-cnode-node-prepare-keeps-groups-and-capacity)
                           (fn-node-prepare fn-node-complete
                            fn-node-pending-matchesp
                            fn-replay-advance-txid
                            fn-record-record-vocabulary
                            fn-record-shape-vocabulary
                            fn-stxa-p fn-stxe-p fn-stxk-p
                            fn-store-retention-event-p
                            fn-replay-composite-record))))))

; KEYSTONE of the carried fold.  A replayed event that is not refused
; leaves a configured node: the step runs only from a configured node, the
; one-record step is the node machine's
; (fn-replay-apply-record-non-nil-is-node-state), and it keeps the groups
; and the capacity the configuration fixes.  (A configured incoming node is
; not a hypothesis: the logical body tests it, so a non-configured node is
; refused.)
(defthm fn-cpr-apply-event-preserves-cnode-statep
  (implies (consp (fn-cpr-apply-event cn event))
           (fn-cnode-statep (fn-cpr-apply-event cn event)))
  :hints (("Goal"
           :use ((:instance fn-replay-apply-record-non-nil-is-node-state
                            (node (fn-cnode-node cn)) (record event)))
           :in-theory (e/d (fn-cpr-apply-event fn-cnode-statep fn-cnode-domain)
                           (fn-node-statep fn-replay-apply-record
                            fn-cpr-event-servedp fn-store-event-p
                            fn-replay-apply-record-non-nil-is-node-state)))))

; What the fold's :exec test relies on: the one-event result is a
; configured node exactly when it is non-NIL.
(defthm fn-cpr-apply-event-statep-iff-consp
  (iff (fn-cnode-statep (fn-cpr-apply-event cn event))
       (consp (fn-cpr-apply-event cn event)))
  :rule-classes nil
  :hints (("Goal" :use fn-cpr-apply-event-preserves-cnode-statep
           :in-theory (e/d (fn-cnode-statep)
                           (fn-cpr-apply-event
                            fn-cpr-apply-event-preserves-cnode-statep)))))

; The guard carries the node invariant; the initial node is checked once
; (`fn-cpr-replay', `fn-sco-cpr-finish'), and the per-event :exec test is
; the refusal's NIL.  Configuration records keep their recognizer checks:
; there are few, and each one changes the configuration the node is checked
; against.
(defun fn-cpr-loop (cn configs events config-sequence event-sequence)
  (declare (xargs :guard (fn-cnode-statep cn) :verify-guards nil
                  :measure (+ (len configs) (len events))))
  (let ((position (+ (nfix config-sequence) (nfix event-sequence))))
    (if (mbe :logic (not (fn-cnode-statep cn)) :exec nil)
        (fn-replay-fault cn position :invalid-node)
      (if (fn-cpr-config-firstp configs events)
          (let* ((record (car configs))
                 (txid (fn-cfg-record-txid record))
                 (node (fn-cnode-node cn)))
            (cond ((not (fn-cfg-recordp record))
                   (fn-replay-fault cn position :invalid-config-record))
                  ((not (equal (fn-cfg-record-sequence record) config-sequence))
                   (fn-replay-fault cn position :config-sequence))
                  ((not (fn-replay-advance-okp node txid))
                   (fn-replay-fault cn position :config-txid))
                  (t (let ((at (fn-cnode-make
                                (fn-replay-advance-txid node txid)
                                (fn-cnode-config cn))))
                       (if (not (fn-cnode-statep at))
                           (fn-replay-fault cn position :invalid-node)
                         (if (not (fn-cnode-record-acceptablep
                                   at record (fn-cnode-line-ceiling)))
                             (fn-replay-fault cn position :config-refusal)
                           (fn-cpr-loop
                            (fn-cnode-apply-config
                             at record (fn-cnode-line-ceiling))
                            (cdr configs) events
                            (+ 1 (nfix config-sequence)) event-sequence)))))))
        (if (consp events)
            (let ((event (car events)))
              (cond ((not (fn-store-event-p event))
                     (fn-replay-fault cn position :invalid-event))
                    ((not (equal (fn-store-event-sequence event) event-sequence))
                     (fn-replay-fault cn position :event-sequence))
                    (t (let ((next (fn-cpr-apply-event cn event)))
                         (if (mbe :logic (not (fn-cnode-statep next))
                                  :exec (not (consp next)))
                             (fn-replay-fault cn position :event-refusal)
                           (fn-cpr-loop next configs (cdr events)
                                        config-sequence
                                        (+ 1 (nfix event-sequence))))))))
          (if (and (null configs) (null events))
              (fn-replay-ok cn position)
            (fn-replay-fault cn position :improper-history)))))))

(defun fn-cpr-replay (configs events)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cpr-loop (fn-cnode-initial (fn-cfg-initial)) configs events 0 0))

; A successful fold has not merely parsed two byte streams. It has checked
; each configuration at the reservation total produced by all earlier Store
; events, and its resulting node remains one coherent configured state.
(defthm fn-cpr-loop-ok-is-configured
  (implies (equal (fn-replay-result-kind
                  (fn-cpr-loop cn configs events config-sequence
                               event-sequence))
                 :ok)
           (fn-cnode-statep
            (fn-replay-result-node
             (fn-cpr-loop cn configs events config-sequence
                          event-sequence))))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events config-sequence
                                     event-sequence)
           :in-theory (e/d (fn-cpr-loop)
                           (fn-cnode-statep fn-cnode-apply-config
                            fn-cpr-apply-event fn-cnode-record-acceptablep
                            fn-store-event-p fn-cfg-recordp)))))

(defthm fn-cpr-replay-ok-is-configured
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
           (fn-cnode-statep
            (fn-replay-result-node (fn-cpr-replay configs events))))
  :hints (("Goal" :use ((:instance fn-cpr-loop-ok-is-configured
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (config-sequence 0) (event-sequence 0)))
           :in-theory (disable fn-cpr-loop-ok-is-configured))))

(defthm fn-cpr-apply-event-keeps-configuration
  (implies (consp (fn-cpr-apply-event cn event))
           (equal (fn-cnode-config (fn-cpr-apply-event cn event))
                  (fn-cnode-config cn)))
  :hints (("Goal" :in-theory
           (e/d (fn-cpr-apply-event)
                (fn-replay-apply-record fn-cpr-event-servedp
                 fn-cnode-statep fn-store-event-p)))))

(defthm fn-cpr-loop-success-counts-configurations
  (implies
   (and (natp config-sequence)
        (equal (fn-cfg-generation (fn-cnode-config cn)) config-sequence)
        (equal (fn-replay-result-kind
                (fn-cpr-loop cn configs events config-sequence event-sequence))
               :ok))
   (equal (fn-cfg-generation
           (fn-cnode-config
            (fn-replay-result-node
             (fn-cpr-loop cn configs events config-sequence event-sequence))))
          (+ config-sequence (len configs))))
  :hints (("Goal"
           :induct (fn-cpr-loop cn configs events config-sequence event-sequence)
           :in-theory (e/d (fn-cpr-loop
                            fn-cnode-apply-config-bumps-the-generation)
                           (fn-cnode-statep fn-cnode-apply-config
                            fn-cpr-apply-event fn-cpr-event-servedp
                            fn-replay-apply-record
                            fn-cnode-record-acceptablep fn-store-event-p
                            fn-cfg-recordp)))))

(defthm fn-cpr-replay-success-counts-configurations
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
           (equal (fn-cfg-generation
                   (fn-cnode-config
                    (fn-replay-result-node (fn-cpr-replay configs events))))
                  (len configs)))
  :hints (("Goal"
           :use ((:instance fn-cpr-loop-success-counts-configurations
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (config-sequence 0) (event-sequence 0)))
           :in-theory (disable fn-cpr-loop-success-counts-configurations))))

; Every fold result's node is a configured node when the fold starts from
; one: a fault keeps the last good node, success the last node.  This is the
; fact carried in place of the per-event recognizer.
(defthm fn-cpr-loop-preserves-cnode-statep
  (implies (fn-cnode-statep cn)
           (fn-cnode-statep
            (fn-replay-result-node
             (fn-cpr-loop cn configs events config-sequence event-sequence))))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events config-sequence
                                       event-sequence)
           :in-theory (e/d (fn-cpr-loop fn-cnode-apply-config-preserves-state
                            fn-replay-result-node fn-replay-fault fn-replay-ok)
                           (fn-cnode-statep fn-cnode-apply-config
                            fn-cpr-apply-event fn-cnode-record-acceptablep
                            fn-store-event-p fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid)))))

(local
 (defthm fn-cpr-cnode-statep-has-node-statep
   (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cnode-statep)))))

(verify-guards fn-cpr-loop
  :hints (("Goal"
           :use ((:instance fn-cpr-apply-event-statep-iff-consp
                            (event (car events))))
           :in-theory (e/d (fn-cnode-apply-config-preserves-state)
                           (fn-cnode-statep fn-cpr-config-firstp fn-cpr-apply-event
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cfg-recordp fn-store-event-p)))))

; The initial configured node is checked once, here, by evaluation.
(defthm fn-cpr-initial-cnode-statep
  (fn-cnode-statep (fn-cnode-initial (fn-cfg-initial))))

(verify-guards fn-cpr-replay)

(deftheory fn-cpr-vocabulary
  '(fn-cpr-config-firstp fn-cpr-event-servedp fn-cpr-apply-event
    fn-cpr-loop fn-cpr-replay))
(in-theory (disable fn-cpr-vocabulary))
