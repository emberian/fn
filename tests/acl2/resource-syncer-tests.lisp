; Actual typed ledger trace.  The event retains its live stobj between
; requests: outcome and physical receipts may arrive in either order.
(in-package "ACL2")
(include-book "../../books/resource-syncer")

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-ros-install-syncer 80 1048576 fn-resource-ledger)
   (if (and (eq word :installed) (fn-ros-drainedp fn-resource-ledger)
            (equal (fn-rv-budget (fn-rl-bank fn-resource-ledger))
                   '(5242880 0 0 1 0 0 0 0 0)))
       (mv nil '(value-triple :actual-qualified-syncer-projection) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word token fn-resource-ledger)
   (fn-ros-issue 7 fn-resource-ledger)
   (if (and (eq word :drawn) (equal token '(:resource :owner 2 1))
            (not (fn-ros-drainedp fn-resource-ledger))
            (equal (fn-rv-drawn (fn-rl-bank fn-resource-ledger))
                   '(5242880 0 0 1 0 0 0 0 0)))
       (mv nil '(value-triple :funded-before-spawn) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (word token fn-resource-ledger)
     (fn-ros-issue 8 fn-resource-ledger)
     (if (and (eq word :slot-busy) (null token)
              (equal (fn-rl-bank fn-resource-ledger) before)
              (equal (fn-rl-worker-operation fn-resource-ledger) 7))
         (mv nil '(value-triple :second-spawn-refused-before-effect) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (word fn-resource-ledger)
     (fn-ros-physical '(:resource :owner 2 1) :timeout fn-resource-ledger)
     (if (and (eq word :pending) (equal (fn-rl-bank fn-resource-ledger) before)
              (equal (fn-rl-worker-physical fn-resource-ledger) 0))
         (mv nil '(value-triple :timeout-keeps-worker-charge) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (word fn-resource-ledger)
     (fn-ros-outcome '(:resource :owner 2 1) 7 fn-resource-ledger)
     (if (and (eq word :pending) (equal (fn-rl-bank fn-resource-ledger) before)
              (equal (fn-rl-worker-outcome fn-resource-ledger) 1)
              (equal (fn-rl-worker-physical fn-resource-ledger) 0))
         (mv nil '(value-triple :outcome-without-join-retains-charge) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-ros-physical '(:resource :owner 2 1) :terminal fn-resource-ledger)
   (if (and (eq word :settled) (fn-ros-drainedp fn-resource-ledger)
            (equal (fn-rv-drawn (fn-rl-bank fn-resource-ledger)) *fn-rv-zero*))
       (mv nil '(value-triple :both-receipts-return-worker) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word token fn-resource-ledger)
   (fn-ros-issue 8 fn-resource-ledger)
   (if (and (eq word :drawn) (equal token '(:resource :owner 2 2)))
       (mv nil '(value-triple :new-generation) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (word fn-resource-ledger)
     (fn-ros-physical '(:resource :owner 2 1) :terminal fn-resource-ledger)
     (if (and (eq word :stale) (equal (fn-rl-bank fn-resource-ledger) before)
              (equal (fn-rl-worker-physical fn-resource-ledger) 0))
         (mv nil '(value-triple :replayed-join-does-not-settle-reused-slot) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (word fn-resource-ledger)
     (fn-ros-outcome '(:resource :owner 2 2) 7 fn-resource-ledger)
     (if (and (eq word :stale) (equal (fn-rl-bank fn-resource-ledger) before)
              (equal (fn-rl-worker-outcome fn-resource-ledger) 0))
         (mv nil '(value-triple :wrong-operation-does-not-settle) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-ros-physical '(:resource :owner 2 2) :terminal fn-resource-ledger)
   (if (and (eq word :pending) (not (fn-ros-drainedp fn-resource-ledger)))
       (mv nil '(value-triple :join-before-outcome-retains-charge) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

(make-event
 (mv-let (word fn-resource-ledger)
   (fn-ros-outcome '(:resource :owner 2 2) 8 fn-resource-ledger)
   (if (and (eq word :settled) (fn-ros-drainedp fn-resource-ledger))
       (mv nil '(value-triple :reverse-order-settles-once) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

; The declaration checks the actual entry's one cost row and draw arguments.
; Projection remains partial and cannot turn on full admission accounting.
(include-book "../../books/def-cost")
(definterface fn-ros-issue :class :ideal
  :operation (:stage :projection :funding fn-ros-install-syncer
              :tariff fn-ros-worker-vector :draw fn-rl-draw :principal :owner
              :slot 2 :physical fn-ros-physical :outcome fn-ros-outcome
              :retention :physical-and-operation :coverage (:resident :workers)
              :unaccounted (fn-rl-wfp fn-rl-draw mv-nth)))
(def-cost fn-ros-issue :unaccounted (fn-rl-wfp fn-rl-draw mv-nth))
(def-operation-check fn-ros-issue)
(assert-event
 (equal (fn-cost-get :unaccounted
                    (cdr (assoc-eq 'fn-ros-issue (table-alist 'fn-cost (w state)))))
        '(fn-rl-wfp fn-rl-draw mv-nth)))

; Refused: hidden unknown.
(encapsulate ()
 (local (definterface fn-ros-issue :class :ideal
          :operation (:stage :projection :funding fn-ros-install-syncer :tariff fn-ros-worker-vector :draw fn-rl-draw :principal :owner :slot 2 :physical fn-ros-physical :outcome fn-ros-outcome :retention :physical-and-operation :coverage (:resident :workers) :unaccounted (fn-rl-draw))))
 (local (assert-event (fn-cost-operation-problem 'fn-ros-issue (w state)))))

; Refused: wrong slot.
(encapsulate ()
 (local (definterface fn-ros-issue :class :ideal
          :operation (:stage :projection :funding fn-ros-install-syncer :tariff fn-ros-worker-vector :draw fn-rl-draw :principal :owner :slot 1 :physical fn-ros-physical :outcome fn-ros-outcome :retention :physical-and-operation :coverage (:resident :workers) :unaccounted (fn-rl-wfp fn-rl-draw mv-nth))))
 (local (assert-event (fn-cost-operation-problem 'fn-ros-issue (w state)))))

; Refused: wrong tariff.
(encapsulate ()
 (local (definterface fn-ros-issue :class :ideal
          :operation (:stage :projection :funding fn-ros-install-syncer :tariff fn-ros-token :draw fn-rl-draw :principal :owner :slot 2 :physical fn-ros-physical :outcome fn-ros-outcome :retention :physical-and-operation :coverage (:resident :workers) :unaccounted (fn-rl-wfp fn-rl-draw mv-nth))))
 (local (assert-event (fn-cost-operation-problem 'fn-ros-issue (w state)))))

; Refused: unfunded metadata.
(encapsulate ()
 (local (definterface fn-ros-issue :class :ideal
          :operation (:stage :projection :funding fn-ros-missing-producer :tariff fn-ros-worker-vector :draw fn-rl-draw :principal :owner :slot 2 :physical fn-ros-physical :outcome fn-ros-outcome :retention :physical-and-operation :coverage (:resident :workers) :unaccounted (fn-rl-wfp fn-rl-draw mv-nth))))
 (local (assert-event (fn-cost-operation-problem 'fn-ros-issue (w state)))))

; Refused: full accounting annotation.
(encapsulate ()
 (local (definterface fn-ros-issue :class :ideal
          :operation (:stage :accounted :funding fn-ros-install-syncer :tariff fn-ros-worker-vector :draw fn-rl-draw :principal :owner :slot 2 :physical fn-ros-physical :outcome fn-ros-outcome :retention :physical-and-operation :coverage (:resident :workers) :unaccounted (fn-rl-wfp fn-rl-draw mv-nth))))
 (local (assert-event (fn-cost-operation-problem 'fn-ros-issue (w state)))))

; Refused: unknown dimension.
(encapsulate ()
 (local (definterface fn-ros-issue :class :ideal
          :operation (:stage :projection :funding fn-ros-install-syncer :tariff fn-ros-worker-vector :draw fn-rl-draw :principal :owner :slot 2 :physical fn-ros-physical :outcome fn-ros-outcome :retention :physical-and-operation :coverage (:resident :invented) :unaccounted (fn-rl-wfp fn-rl-draw mv-nth))))
 (local (assert-event (fn-cost-operation-problem 'fn-ros-issue (w state)))))

; Duplicate contract keys cannot hide a second producer or tariff.
(assert-event
 (not (fn-di-operation-formp '(:stage :projection :funding fn-ros-install-syncer :tariff fn-ros-worker-vector :draw fn-rl-draw :principal :owner :slot 2 :physical fn-ros-physical :outcome fn-ros-outcome :retention :physical-and-operation :coverage (:resident :workers) :unaccounted (fn-rl-wfp fn-rl-draw mv-nth) :slot 9))))
