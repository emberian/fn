; Executor-wide scalar fields; no indexed singleton row.
(in-package "ACL2")
(include-book "columns")
(include-book "profile")

(make-event
 (value (fn2-declare '(:operation-set fn2-stop-codes) nil nil
          (fn2-columns-enum-events '((stop-reason (:enum fn2-stop-reason
     (:none :issue-unreserve :issue-range :issue-capability :issue-storage
      :issue-cancel-target :issue-enqueue :harvest-fifo :harvest-input
      :harvest-output :harvest-finish :wake-bounds :wake-state :machine-write
      :machine-observation :machine-phase :pool-release :signal
      :clock-exhausted :work-overflow :issue-wake :machine-contract :account :engine-genesis))))))))
(defcolumns fn2-control nil
  :init-name fn2-control-columns-init
  :extra-fields
  ((fn2-control-h :type (unsigned-byte 32) :initially 0 :why "One executor harvest budget shared by all visits.")
   (fn2-control-k :type (unsigned-byte 32) :initially 0 :why "One executor visit budget shared by all principals.")
   (fn2-control-aturn :type (unsigned-byte 32) :initially 0 :why "One turn descriptor cap shared by all machines.")
   (fn2-control-stop :type (unsigned-byte 1) :initially 0 :why "One terminal posture for the composed core.")
   (fn2-control-stop-reason :type (unsigned-byte 8) :initially 0 :why "First failure reason belongs to the core, not a machine row.")
   (fn2-control-idle-deadline :type (unsigned-byte 60) :initially *fn2-no-deadline* :why "Earliest wake request across the core.")
   (fn2-control-wake-generation :type (unsigned-byte 60) :initially 0 :why "Global host wake incarnation prevents stale delivery.")
   (fn2-control-armed-deadline :type (unsigned-byte 60) :initially *fn2-no-deadline* :why "The single outstanding host wake deadline.")
   (fn2-control-now :type (unsigned-byte 60) :initially 0 :why "Latest monotonic observation shared by all machines.")
   (fn2-control-timer-cursor :type (unsigned-byte 32) :initially 0 :why "One resumable scan position for timer service.")
   (fn2-control-turn-bytes :type (unsigned-byte 60) :initially 0 :why "Aggregate byte charge of the current turn.")
   (fn2-control-turn-steps :type (unsigned-byte 60) :initially 0 :why "Aggregate step charge of the current turn.")))

(defun fn2-control-init (profile fn2-control)
  (declare (xargs :stobjs fn2-control :guard (fn2-profilep profile)
                  :guard-hints (("Goal" :in-theory (enable fn2-profilep)))))
  (let* ((fn2-control (fn2-control-columns-init 0 fn2-control))
         (fn2-control (update-fn2-control-h (fn2-profile-h profile) fn2-control))
         (fn2-control (update-fn2-control-k (fn2-profile-k profile) fn2-control))
         (fn2-control (update-fn2-control-aturn (fn2-profile-aturn profile) fn2-control))
         (fn2-control (update-fn2-control-stop 0 fn2-control))
         (fn2-control (update-fn2-control-idle-deadline *fn2-no-deadline* fn2-control))
         (fn2-control (update-fn2-control-wake-generation 0 fn2-control))
         (fn2-control (update-fn2-control-armed-deadline *fn2-no-deadline* fn2-control))
         (fn2-control (update-fn2-control-now 0 fn2-control))
         (fn2-control (update-fn2-control-timer-cursor 0 fn2-control))
         (fn2-control (update-fn2-control-turn-bytes 0 fn2-control))
         (fn2-control (update-fn2-control-turn-steps 0 fn2-control)))
    fn2-control))
(defthm fn2-control-init-type
  (implies (and (fn2-controlp fn2-control) (fn2-profilep profile))
           (fn2-controlp (fn2-control-init profile fn2-control)))
  :hints (("Goal" :in-theory (enable fn2-profilep))))
(defthm fn2-control-init-wfp
  (implies (fn2-profilep profile)
           (fn2-control-wfp (fn2-control-init profile fn2-control))))
(in-theory (disable fn2-control-init))
(assert-event (eq (symbol-class 'fn2-control-init (w state)) :common-lisp-compliant))
