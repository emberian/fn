; Earliest required host wake for the current observed clock view. Layer A
; has no machine timer heap: callers explicitly register the next requirement.
(in-package "ACL2")
(include-book "executor-access")

(defun fn2-request-wake (deadline fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (unsigned-byte-p 60 deadline)
           (< deadline (fn2-exec-idle-deadline fn2-core)))
      (fn2-exec-set-idle-deadline deadline fn2-core)
    fn2-core))
(fn2-core-preserves fn2-request-wake (deadline fn2-core) :rows nil :prefix "")

(defun fn2-exec-wake-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (< (fn2-exec-idle-deadline fn2-core) *fn2-no-deadline*)
       (not (= (fn2-exec-idle-deadline fn2-core)
               (fn2-exec-armed-deadline fn2-core)))
       (fn2-exec-credit-p fn2-core)))

(defun fn2-exec-arm (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (fn2-exec-wake-p fn2-core)) (mv 0 fn2-core)
    (let ((deadline (fn2-exec-idle-deadline fn2-core))
          (generation (fn2-exec-wake-generation fn2-core)))
      (mv-let (code slot gen fn2-core)
        (fn2-issue-arm-wake deadline generation fn2-core)
        (declare (ignore slot gen))
        (if (eq code :ok)
            (let ((fn2-core (fn2-exec-set-armed-deadline deadline fn2-core)))
              (mv 1 fn2-core))
          (mv 0 fn2-core))))))
(fn2-core-preserves fn2-exec-arm (fn2-core) :position 1 :rows nil)
(defthm fn2-exec-arm-count-natp
  (natp (car (fn2-exec-arm fn2-core)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-exec-arm))))
(defthm fn2-exec-arm-count-bound
  (<= (car (fn2-exec-arm fn2-core)) 1)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn2-exec-arm))))
(in-theory (disable fn2-exec-arm))

(defun fn2-exec-clock (mono fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (unsigned-byte-p 60 mono)) fn2-core
    (let* ((now (max mono (fn2-exec-now fn2-core)))
           (generation (fn2-exec-wake-generation fn2-core))
           (deadline (fn2-exec-idle-deadline fn2-core))
           (fn2-core (fn2-exec-set-now now fn2-core))
           (fn2-core (fn2-exec-set-armed-deadline *fn2-no-deadline* fn2-core))
           (fn2-core (if (<= deadline now)
                         (fn2-exec-set-idle-deadline *fn2-no-deadline* fn2-core)
                       fn2-core)))
      ; A token never wraps: stop before another observation could reuse it.
      (if (= generation *fn2-u60-max*)
          (fn2-core-stop *fn2-stop-reason-clock-exhausted* fn2-core)
        (fn2-exec-set-wake-generation (+ generation 1) fn2-core)))))
(fn2-core-preserves fn2-exec-clock (mono fn2-core) :rows nil :prefix "")

(assert-event
 (fn2-assert-compliant-p
  '(fn2-request-wake fn2-exec-wake-p fn2-exec-arm fn2-exec-clock) (w state)))

;; The executor's scalar writers keep the ops and pool children, so the
;; mailbox writes ops only through take-clock and take-signal.
(defthm fn2-exec-clock-ops-frame
  (equal (fn2-core-ops (fn2-exec-clock mono core)) (fn2-core-ops core))
  :hints (("Goal" :in-theory (enable fn2-exec-clock fn2-core-stop fn2-exec-set-now fn2-exec-set-armed-deadline
                                     fn2-exec-set-idle-deadline fn2-exec-set-wake-generation))))
(defthm fn2-exec-trace-actions-ops-frame
  (equal (fn2-core-ops (fn2-exec-trace-actions left ordinal start core)) (fn2-core-ops core))
  :hints (("Goal" :in-theory (enable fn2-exec-trace-actions))))
(defthm fn2-exec-record-ops-frame
  (equal (fn2-core-ops (fn2-exec-record kind id principal position bytes steps actions runnable wake start core))
         (fn2-core-ops core))
  :hints (("Goal" :in-theory (e/d (fn2-exec-record fn2-core-stop) (fn2-exec-trace-actions)))))
(defthm fn2-exec-clock-pool-frame
  (equal (fn2-core-pool (fn2-exec-clock mono core)) (fn2-core-pool core))
  :hints (("Goal" :in-theory (enable fn2-exec-clock fn2-core-stop fn2-exec-set-now fn2-exec-set-armed-deadline
                                     fn2-exec-set-idle-deadline fn2-exec-set-wake-generation))))
(defthm fn2-exec-trace-actions-pool-frame
  (equal (fn2-core-pool (fn2-exec-trace-actions left ordinal start core)) (fn2-core-pool core))
  :hints (("Goal" :in-theory (enable fn2-exec-trace-actions))))
(defthm fn2-exec-record-pool-frame
  (equal (fn2-core-pool (fn2-exec-record kind id principal position bytes steps actions runnable wake start core))
         (fn2-core-pool core))
  :hints (("Goal" :in-theory (e/d (fn2-exec-record fn2-core-stop) (fn2-exec-trace-actions)))))
;; The mailbox: one posted clock or signal, taken from the ops child and
;; recorded. It reads no machine, so it sits below the dispatcher.
(defun fn2-exec-mailbox (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (b* ((clockp (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
                (yes) (= 1 (fn2-ops-clock-posted fn2-ops)) yes))
       (start (fn2-exec-queued fn2-core))
       (fn2-core
        (if clockp
            (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
              (posted mono real flags fn2-ops) (fn2-take-clock fn2-ops)
              (let ((unused-posted posted) (unused-real real) (unused-flags flags))
                (declare (ignore unused-posted unused-real unused-flags))
                (fn2-exec-clock mono fn2-core)))
          (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
            (bits fn2-ops) (fn2-take-signal fn2-ops)
            (if (< 0 (nfix bits)) (fn2-core-stop *fn2-stop-reason-signal* fn2-core) fn2-core))))
       (fn2-core (fn2-exec-record (if clockp *fn2-trace-kind-clock* *fn2-trace-kind-signal*) *fn2-none* 0 0 0 *fn2-work-mailbox* 0
                                 nil *fn2-none* start fn2-core)))
    (mv 1 0 0 0 *fn2-work-mailbox* fn2-core)))
(fn2-core-preserves fn2-exec-mailbox (fn2-core) :position 5 :rows nil :prefix "" :hints (("Goal" :in-theory (enable fn2-core-wfp))))
