; Core operations for the connection machine's XFNC carrier.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "sched-timers")

(defcost fn2-xfnc-policy
 :doc "Read the pinned request/discard bounds and body timeout; all zero when XFNC is off.")
(defcost fn2-xfnc-fc-row :answers (:ok :bounds)
 :doc "Resolve the NNTP connection's private format row and check room for its field and hash workspace.")
(defcost fn2-xfnc-arm-timer :child fn2-sched-arm-delay-ms
 :answers (:ok :bounds :state) :tables (fn2-core-sched fn2-core-control)
 :doc "Arm the connection's counted-body deadline against the monotonic scheduler clock.")
(defcost fn2-xfnc-clear-timer :child fn2-sched-clear-deadline
 :answers (:ok :bounds) :tables (fn2-core-sched)
 :doc "Clear the counted-body deadline and expiration before moving on or reclaiming the connection.")
(defcost fn2-xfnc-expired-p :child fn2-sched-timer-expired-p
 :doc "Whether the counted-body deadline has expired.")

;; The connection kind's auto-emitter only scans its own declaration book.
;; Generate these faces here so the counted arms see the scheduler contracts.
(make-event
 (value (cons 'progn
              (append (fn2-arms-op-face-events 'fn2-xfnc-arm-timer 'fn2-sched-arm-delay-ms (w state))
                      (fn2-arms-op-face-events 'fn2-xfnc-clear-timer 'fn2-sched-clear-deadline (w state))
                      (fn2-arms-op-face-events 'fn2-xfnc-expired-p 'fn2-sched-timer-expired-p (w state))))))

(defun fn2-xfnc-policy (fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                 :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
 (stobj-let ((fn2-xfnc-config (fn2-core-xfnc-config fn2-core))) (request discard timeout)
   (if (< 0 (fn2-xfnc-config-rows fn2-xfnc-config))
       (mv (nfix (fn2-xfnc-config-request-max 0 fn2-xfnc-config))
           (nfix (fn2-xfnc-config-discard-max 0 fn2-xfnc-config))
           (nfix (fn2-xfnc-config-body-ms 0 fn2-xfnc-config)))
     (mv 0 0 0))
   (mv request discard timeout)))

(defun fn2-xfnc-private-fc-row (pull conn fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                 :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
 (b* (((unless (eq (if pull (fn2-peer-pull-snapshot-read-code conn fn2-core)
                            (fn2-conn-snapshot-read-code conn fn2-core)) :ok)) (mv :bounds 0))
      (slot (fn2-machine-slot conn fn2-core))
      ((mv first count)
       (stobj-let ((fn2-xfnc-config (fn2-core-xfnc-config fn2-core))) (first count)
         (if (< 0 (fn2-xfnc-config-rows fn2-xfnc-config))
             (mv (nfix (if pull (fn2-xfnc-config-pull-first 0 fn2-xfnc-config) (fn2-xfnc-config-first-row 0 fn2-xfnc-config)))
                 (nfix (if pull (fn2-xfnc-config-pull-count 0 fn2-xfnc-config) (fn2-xfnc-config-row-count 0 fn2-xfnc-config))))
           (mv 0 0))
         (mv first count)))
      ((unless (and (natp slot) (< slot count))) (mv :bounds 0))
      (row (+ first slot))
      (field-rows (stobj-let ((fn2-fields (fn2-core-fields fn2-core))) (n) (fn2-fields-rows fn2-fields) n))
      (ready (stobj-let ((fn2-b3 (fn2-core-b3 fn2-core))
                         (fn2-digests (fn2-core-digests fn2-core))) (ok)
               (fn2-b3-ready row fn2-b3 fn2-digests) ok)))
   (if (and ready (<= (* 128 (+ 1 row)) (nfix field-rows))) (mv :ok row) (mv :bounds 0))))

(defun fn2-xfnc-fc-row (conn fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (fn2-xfnc-private-fc-row nil conn fn2-core))
(defun fn2-peer-pull-fc-row (id fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (fn2-xfnc-private-fc-row t id fn2-core))
(defthm fn2-peer-pull-fc-row-natp
 (natp (mv-nth 1 (fn2-peer-pull-fc-row id fn2-core))) :rule-classes :type-prescription)
(defthm fn2-peer-pull-fc-row-ok-room
 (implies (eq (mv-nth 0 (fn2-peer-pull-fc-row id fn2-core)) :ok)
          (<= (+ (* 128 (mv-nth 1 (fn2-peer-pull-fc-row id fn2-core))) 128)
              (nfix (fn2-fields-rows (fn2-core-fields fn2-core)))))
 :rule-classes nil)
(in-theory (disable fn2-peer-pull-fc-row))

(defthm fn2-xfnc-fc-row-natp
 (natp (mv-nth 1 (fn2-xfnc-fc-row conn fn2-core))) :rule-classes :type-prescription)
(defthm fn2-xfnc-fc-row-ok-room
 (implies (eq (mv-nth 0 (fn2-xfnc-fc-row conn fn2-core)) :ok)
          (<= (+ (* 128 (mv-nth 1 (fn2-xfnc-fc-row conn fn2-core))) 128)
              (nfix (fn2-fields-rows (fn2-core-fields fn2-core)))))
 :rule-classes nil)
(in-theory (disable fn2-xfnc-policy fn2-xfnc-fc-row))
