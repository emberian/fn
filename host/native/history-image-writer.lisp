; WIP actual checkpoint writer wrapper. Loaded after native extent/IO.
; The outer maintenance constructor supplies its admitted fixed buffers.
; This adapter allocates no page arrays, recomputes no budget/key or offsets,
; and performs no staging IO. The producer executes only returned effects.
(in-package "ACL2")

(defstruct (fnn-hpi-writer (:constructor %make-fnn-hpi-writer))
  cursor q0 q1 q2 q3 pool digest)

(defun fnn-hpi-retain (cursor q0 q1 q2 q3 pool digest)
  "Retain the exact core continuation and already-admitted buffers."
  (%make-fnn-hpi-writer :cursor cursor :q0 q0 :q1 q1 :q2 q2 :q3 q3
                        :pool pool :digest digest))

(defun fnn-hpi-step (writer observation)
  "One actual funded core step. Caller holds the extent/pool serialization;
no owner mutex is acquired here. Returned buffers replace all prior aliases."
  (destructuring-bind (word effect cursor q0 q1 q2 q3 pool digest read-pool)
      (fnn-core-page-read-pool 'fn-owner-history-image-tick
       (fnn-hpi-writer-cursor writer) observation
       (fnn-hpi-writer-q0 writer) (fnn-hpi-writer-q1 writer)
       (fnn-hpi-writer-q2 writer) (fnn-hpi-writer-q3 writer)
       (fnn-hpi-writer-pool writer) (fnn-hpi-writer-digest writer))
    (declare (ignore read-pool))
    (setf (fnn-hpi-writer-cursor writer) cursor (fnn-hpi-writer-q0 writer) q0
          (fnn-hpi-writer-q1 writer) q1 (fnn-hpi-writer-q2 writer) q2
          (fnn-hpi-writer-q3 writer) q3 (fnn-hpi-writer-pool writer) pool
          (fnn-hpi-writer-digest writer) digest)
    (values word effect)))

(defun fnn-hpi-offer (writer ordinal source row-token completed-new-key)
  "Core checks actual retained live receipt before allocating a child."
  (destructuring-bind (word cursor read-pool)
      (fnn-core-page-read-pool 'fn-owner-history-image-offer
       (fnn-hpi-writer-cursor writer) ordinal source row-token completed-new-key)
    (declare (ignore read-pool))
    (setf (fnn-hpi-writer-cursor writer) cursor)
    word))

(defun fnn-hpi-action (writer stage observation)
  "One returned action of the retained private writer. Caller holds the job
ACTION-LOCK through this call and retains the returned observation for the
NEXT core step. The extent lock covers the core transition, then is released
before the single issued positional syscall. This function issues no source,
INITIAL, stage or publication authority and never retries an issued effect."
  (multiple-value-bind (word effect)
      (sb-thread:with-mutex (*fnn-extent-lock*)
        (fnn-hpi-step writer observation))
    (values word effect
            (when (member word '(:write :io))
              (fnn-hpi-execute-effect writer stage effect)))))
