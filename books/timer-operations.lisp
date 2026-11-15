; One declaration/factory for the actual CNS and TLS timer faces.
; Production and reference proof consumers include the same materialization.
(in-package "ACL2")
(include-book "sched-timers")
(include-book "machine-arms")

(defcost fn2-cns-arm-wait-timer :child fn2-sched-arm-delay-ms
 :answers (:ok :bounds :state) :tables (fn2-core-sched fn2-core-control)
 :doc "Arm this live request's one-shot wait timer, converting milliseconds to an absolute monotonic deadline without wrapping.")
(defcost fn2-cns-clear-wait-timer :child fn2-sched-clear-deadline
 :answers (:ok :bounds) :tables (fn2-core-sched)
 :doc "Disarm a request's timer before reclaiming its machine row; clear its expired bit as well.")
(defcost fn2-cns-wait-expired-p :child fn2-sched-timer-expired-p
 :doc "Whether the request's registered timer expired.")
(defcost fn2-tls-arm-timer :child fn2-sched-arm-delay-ms
 :answers (:ok :bounds :state) :tables (fn2-core-sched fn2-core-control)
 :doc "Arm the connection deadline before sending the STARTTLS handoff reply.")
(defcost fn2-tls-clear-timer :child fn2-sched-clear-deadline
 :answers (:ok :bounds) :tables (fn2-core-sched)
 :doc "Clear handshake deadline and expiration before resuming or reclaiming a connection.")
(defcost fn2-tls-expired-p :child fn2-sched-timer-expired-p
 :doc "The scheduler's handshake-deadline observation.")

(defconst *fn2-timer-core-operations*
 '((fn2-cns-arm-wait-timer . fn2-sched-arm-delay-ms)
   (fn2-cns-clear-wait-timer . fn2-sched-clear-deadline)
   (fn2-cns-wait-expired-p . fn2-sched-timer-expired-p)
   (fn2-tls-arm-timer . fn2-sched-arm-delay-ms)
   (fn2-tls-clear-timer . fn2-sched-clear-deadline)
   (fn2-tls-expired-p . fn2-sched-timer-expired-p)))
(defun fn2-timer-core-face-events (operations world)
 (declare (xargs :verify-guards nil))
 (if (atom operations) nil
  (let* ((op (caar operations)) (child (cdar operations))
         (row (fn2-decl-row (list :cost op) world)))
   (if (not (and (equal (fn2-decl-get :child row) child)
                 (function-symbolp child world)
                 (not (function-symbolp op world))))
       (er hard 'fn2-timer-core-face-events
           "Timer declaration, child or unique materialization differs: ~x0." op)
     (append (fn2-arms-op-face-events op child world)
             (fn2-timer-core-face-events (cdr operations) world))))))
(defmacro fn2-timer-core-events ()
 `(make-event (value (cons 'progn
   (fn2-timer-core-face-events *fn2-timer-core-operations* (w state))))))
