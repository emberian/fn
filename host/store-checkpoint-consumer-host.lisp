; Same successful loader's R child2 consumer value. No live-account STATE
; fallback and no authorization/canonical/operation admission is issued here.
(in-package "ACL2")
(include-book "store-checkpoint-context-host")
(include-book "../books/store-checkpoint-consumer-publication")
(include-book "../books/consumer-account-publication-state")

(defun fn-store-sco-consumer-publication-value (state)
 (declare (xargs :stobjs state :mode :program))
 (let ((checkpoint (fn-store-sco-current state))
       (source (fn-store-sco-recovery-source-value state))
       (generation (fn-store-sco-recovery-source-generation-value state)))
  (if (and checkpoint source (natp generation))
      (let ((publication (fn-cpub-readout (fn-omk-at 4 checkpoint))))
       (if (eq (fn-omk-at 0 publication) :ok)
           (list :checkpoint-consumer generation publication)
         publication))
    '(:unavailable :checkpoint-consumer))))

(defun fn-store-sco-consumer-publication (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-store-sco-consumer-publication-value state)))
