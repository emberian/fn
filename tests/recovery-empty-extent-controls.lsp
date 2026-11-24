; One byte of debris in an otherwise empty extent, observed after a fresh
; process starts recovery. No submitted batch or captured manifest is needed.
(in-package "ACL2")
(include-book "sim/check-recovery")

(defun fn2-recovery-empty-extent-run (unit kind fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* ((profile (fn2-b-test-profile *fn2-profile-tiny* 0))
       (model (fn2-cm-profile kind t t nil 0 0))
       (fn2-core (fn2-core-init profile fn2-core))
       (fn2-sim (fn2-sim-init 1 :none "recovery discovery" profile fn2-sim))
       (fn2-own (fn2-own-init profile fn2-own))
       (fn2-sim
        (if (natp unit)
            (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
              (fn2-sim-storage)
              (fn2-storage-corrupt-byte (+ (* *fn2-commit-unit-bytes* unit) 100) 1 fn2-sim-storage)
              fn2-sim)
          fn2-sim))
       ((mv status class outcome & & fn2-core fn2-sim fn2-own)
        (fn2-b-crash-recover profile model nil nil nil *fn2-fault-none* 0
                             fn2-core fn2-sim fn2-own)))
    (mv (list status class outcome) fn2-core fn2-sim fn2-own)))

(defun fn2-recovery-empty-extent-observation (unit kind)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (result fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (result fn2-core fn2-sim fn2-own)
              (fn2-recovery-empty-extent-run unit kind fn2-core fn2-sim fn2-own)
              (mv result fn2-core fn2-sim)))
          (mv result fn2-core)))
      result)))

:q
(handler-case
    (progn
      (assert (equal (fn2-recovery-empty-extent-observation nil :broad) '(:done :intact :none)))
      (loop for unit below *fn2-storage-extent-units* do
        (assert (equal (fn2-recovery-empty-extent-observation unit :broad) '(:done :unknown :none))))
      (assert (equal (fn2-recovery-empty-extent-observation 3 :crash-only) '(:done :torn-tail :none)))
      (format t "Recovery classified the clean extent and debris in every physical unit.~%")
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "Recovery extent control failed: ~A~%" condition)
    (sb-ext:exit :code 1)))
