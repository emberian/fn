; Actual private output ledger receipt/free-row trace.
(in-package "ACL2")
(include-book "../../books/resource-output")

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-install 1073741824 536870912 nil nil 4 fn-resource-ledger)
   (if (eq word :output-resources-unconfigured)
       (mv nil '(value-triple :absence-stays-partial) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 fn-resource-ledger)
   (if (and (eq word :installed) (fn-rlo-drainedp fn-resource-ledger) (equal (fn-rl-next fn-resource-ledger) 2) (equal (fn-rl-idsi 2 fn-resource-ledger) 3) (equal (fn-rl-idsi 3 fn-resource-ledger) 0))
       (mv nil '(value-triple :explicit-pool-startup) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word token fn-resource-ledger)
   (fn-rlo-issue 7 11 8 :issued fn-resource-ledger)
   (if (and (eq word :drawn) (equal token '(:resource (:connection 7 11) 2 1)) (not (fn-rlo-drainedp fn-resource-ledger)) (equal (fn-rl-next fn-resource-ledger) 3))
       (mv nil '(value-triple :fund-before-materialization) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-output '(:resource (:connection 7 12) 2 1) 8 :discarded fn-resource-ledger)
   (if (and (eq word :stale) (equal (fn-rl-elensi 2 fn-resource-ledger) 0) (not (fn-rlo-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :wrong-connection-generation) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-output '(:resource (:connection 8 11) 2 1) 8 :discarded fn-resource-ledger)
   (if (and (eq word :stale) (equal (fn-rl-elensi 2 fn-resource-ledger) 0) (not (fn-rlo-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :wrong-cid) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-output '(:resource (:connection 7 11) 2 1) 9 :discarded fn-resource-ledger)
   (if (and (eq word :stale) (equal (fn-rl-elensi 2 fn-resource-ledger) 0) (not (fn-rlo-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :wrong-operation) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-output '(:resource (:connection 7 11) 2 1) 8 :discarded fn-resource-ledger)
   (if (and (eq word :pending) (equal (fn-rl-elensi 2 fn-resource-ledger) 1) (equal (fn-rl-trailersi 2 fn-resource-ledger) 0) (not (fn-rlo-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :output-alone-retains-physical-custody) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-physical '(:resource (:connection 7 11) 2 1) 8 :timeout fn-resource-ledger)
   (if (and (eq word :pending) (equal (fn-rl-trailersi 2 fn-resource-ledger) 0) (not (fn-rlo-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :timeout-keeps-debit) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word token fn-resource-ledger)
   (fn-rlo-issue 9 15 12 :none fn-resource-ledger)
   (if (and (eq word :drawn) (equal token '(:resource (:connection 9 15) 3 1)) (equal (fn-rl-next fn-resource-ledger) 0))
       (mv nil '(value-triple :second-shared-window) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word token fn-resource-ledger)
   (fn-rlo-issue 10 16 13 :none fn-resource-ledger)
   (if (and (eq word :no-output-window) (null token) (not (fn-rlo-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :pool-slot-pressure-refuses) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-output '(:resource (:connection 9 15) 3 1) 12 :drained fn-resource-ledger)
   (if (and (eq word :settled) (equal (fn-rl-next fn-resource-ledger) 3) (not (fn-rlo-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :synchronous-window-frees-one-row) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-physical '(:resource (:connection 7 11) 2 1) 8 :terminal fn-resource-ledger)
   (if (and (eq word :settled) (equal (fn-rl-next fn-resource-ledger) 2) (fn-rlo-drainedp fn-resource-ledger))
       (mv nil '(value-triple :physical-and-output-settle) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word token fn-resource-ledger)
   (fn-rlo-issue 7 12 9 :issued fn-resource-ledger)
   (if (and (eq word :drawn) (equal token '(:resource (:connection 7 12) 2 2)))
       (mv nil '(value-triple :row-reuse-new-draw-generation) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-physical '(:resource (:connection 7 11) 2 1) 8 :terminal fn-resource-ledger)
   (if (and (eq word :stale) (equal (fn-rl-trailersi 2 fn-resource-ledger) 0))
       (mv nil '(value-triple :old-receipt-cannot-settle-reuse) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-physical '(:resource (:connection 7 12) 2 2) 9 :no-actor-created fn-resource-ledger)
   (if (and (eq word :pending) (equal (fn-rl-trailersi 2 fn-resource-ledger) 1) (not (fn-rlo-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :no-child-still-waits-for-output-discard) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-rlo-output '(:resource (:connection 7 12) 2 2) 9 :discarded fn-resource-ledger)
   (if (and (eq word :settled) (fn-rlo-drainedp fn-resource-ledger))
       (mv nil '(value-triple :reverse-order-settles) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

; Literal typed-result keystone teeth. Corrupted-state removals deliberately
; refuse without repairing input; these do not claim free-chain/bank validity.

(defthm rot-install-keeps-representation-witness
 (let* ((ledger (create-fn-resource-ledger)) (result (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 ledger)) (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (eq (car result) :installed)
       (fn-resource-ledgerp after) (fn-rl-wfp after)))
 :rule-classes nil)

(defthm rot-install-representation-without-type-corrupted-state-witness
 (let* ((ledger (update-fn-rl-worker-physical 2 (create-fn-resource-ledger))) (after (mv-nth 1 (fn-rlo-install 0 0 nil nil 4 ledger))))
  (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger)
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rot-install-representation-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (create-fn-resource-ledger))) (after (mv-nth 1 (fn-rlo-install 0 0 nil nil 4 ledger))))
  (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rot-issue-keeps-representation-witness
 (let* ((ledger (mv-nth 1 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (create-fn-resource-ledger)))) (result (fn-rlo-issue 7 11 8 :issued ledger)) (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (eq (car result) :drawn)
       (fn-resource-ledgerp after) (fn-rl-wfp after)))
 :rule-classes nil)

(defthm rot-issue-representation-without-type-corrupted-state-witness
 (let* ((ledger (update-fn-rl-worker-physical 2 (create-fn-resource-ledger))) (after (mv-nth 2 (fn-rlo-issue -1 0 0 :none ledger))))
  (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger)
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rot-issue-representation-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (create-fn-resource-ledger))) (after (mv-nth 2 (fn-rlo-issue -1 0 0 :none ledger))))
  (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rot-output-keeps-representation-witness
 (let* ((ledger (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (mv-nth 1 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (create-fn-resource-ledger)))))) (result (fn-rlo-output '(:resource (:connection 7 11) 2 1) 8 :discarded ledger)) (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (eq (car result) :pending)
       (fn-resource-ledgerp after) (fn-rl-wfp after)))
 :rule-classes nil)

(defthm rot-output-representation-without-type-corrupted-state-witness
 (let* ((ledger (update-fn-rl-worker-physical 2 (create-fn-resource-ledger))) (after (mv-nth 1 (fn-rlo-output nil 0 :discarded ledger))))
  (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger)
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rot-output-representation-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (create-fn-resource-ledger))) (after (mv-nth 1 (fn-rlo-output nil 0 :discarded ledger))))
  (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rot-physical-keeps-representation-witness
 (let* ((ledger (mv-nth 1 (fn-rlo-output '(:resource (:connection 7 11) 2 1) 8 :discarded (mv-nth 2 (fn-rlo-issue 7 11 8 :issued (mv-nth 1 (fn-rlo-install 1073741824 536870912 nil '(16777216 1048576) 4 (create-fn-resource-ledger)))))))) (result (fn-rlo-physical '(:resource (:connection 7 11) 2 1) 8 :terminal ledger)) (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (eq (car result) :settled)
       (fn-resource-ledgerp after) (fn-rl-wfp after)))
 :rule-classes nil)

(defthm rot-physical-representation-without-type-corrupted-state-witness
 (let* ((ledger (update-fn-rl-worker-physical 2 (create-fn-resource-ledger))) (after (mv-nth 1 (fn-rlo-physical nil 0 :terminal ledger))))
  (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger)
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rot-physical-representation-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (create-fn-resource-ledger))) (after (mv-nth 1 (fn-rlo-physical nil 0 :terminal ledger))))
  (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)
