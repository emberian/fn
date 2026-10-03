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
