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
  (natp (mv-nth 0 (fn2-exec-arm fn2-core)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-exec-arm))))
(defthm fn2-exec-arm-count-bound
  (<= (mv-nth 0 (fn2-exec-arm fn2-core)) 1)
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
