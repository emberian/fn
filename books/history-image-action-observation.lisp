; Scheduling gate for observations returned by the actual private executor.
; This gate does not authenticate an ACK: FnHPITick still checks its exact
; pending effect, source, stage, serial, generation and retained grant.
(in-package "ACL2")
(include-book "snapshot-source-token")

(defun fn-hpi-effect-observation-disposition (observation)
  (declare (xargs :guard t))
  (let* ((tag (fn-omk-at 0 observation))
         (complete (case tag
                     (:written (fn-omk-widthp observation 6))
                     (:spool-written (fn-omk-widthp observation 8))
                     ((:image-read :spool-read) (fn-omk-widthp observation 9))
                     (otherwise nil)))
         (outcome (fn-omk-at (if (eq tag :written) 5 7) observation)))
    (cond ((and complete (eq outcome :ok)) :ready)
          ((and (fn-omk-widthp observation 2) (eq tag :refused)) :refused)
          (t :recovery-required))))

(defthm fn-hpi-effect-observation-ready-unfolds
  (implies (equal (fn-hpi-effect-observation-disposition observation) :ready)
           (and (case (fn-omk-at 0 observation)
                  (:written (fn-omk-widthp observation 6))
                  (:spool-written (fn-omk-widthp observation 8))
                  ((:image-read :spool-read) (fn-omk-widthp observation 9))
                  (otherwise nil))
                (equal (fn-omk-at (if (equal (fn-omk-at 0 observation) :written) 5 7)
                                  observation) :ok)))
  :rule-classes nil)

(in-theory (disable fn-hpi-effect-observation-disposition))
