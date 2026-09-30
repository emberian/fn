; Private image I/O executor. The constructor retains already-admitted
; file descriptors and fixed conversion vector, never allocates backing.
; The outer snapshot job owns close/delete/publication and definite joins.
(in-package "ACL2")
(defstruct (fnn-hpi-stage (:constructor fnn-hpi-stage-retain
                           (id target data-spool table-spool scratch)))
  id target data-spool table-spool scratch)

(defun fnn-hpi-page-pwrite (fd octets offset count)
  "One syscall at the exact core-issued coordinates. Return signed got."
  (sb-sys:with-pinned-objects (octets)
    (sb-alien:alien-funcall
      (sb-alien:extern-alien "pwrite"
        (function sb-alien:long sb-alien:int sb-alien:system-area-pointer
                  sb-alien:unsigned-long sb-alien:long))
      fd (sb-sys:vector-sap octets) count offset)))

(defun fnn-hpi-execute-effect (writer stage effect)
  "Caller holds the job ACTION-LOCK until this synchronous action returns.
Core authorizes the live issued effect under extent/pool lock; that lock is
released before I/O. The retained writer/page generation cannot change until
its exact observation is consumed. Short/error is uncertain, never retry."
  (let* ((cursor (fnn-hpi-writer-cursor writer))
         (plan (sb-thread:with-mutex (*fnn-extent-lock*)
                 (fnn-core-page-read-pool 'fn-owner-history-image-effect-plan
                                         cursor effect (fnn-hpi-stage-id stage))))
         (data (fnn-hpi-stage-scratch stage))
         (got -1) (status :error) (bytes nil))
    (unless (eq (first plan) :io)
      (return-from fnn-hpi-execute-effect plan))
    (destructuring-bind (tag operation role offset count buffer payload) plan
      (declare (ignore tag))
      (let ((fd (ecase role (:target (fnn-hpi-stage-target stage))
                  (:data-spool (fnn-hpi-stage-data-spool stage))
                  (:table-spool (fnn-hpi-stage-table-spool stage)))))
        (when (eq operation :write)
          (if buffer
              (sb-thread:with-mutex (*fnn-extent-lock*)
                (dotimes (i 16384)
                  (destructuring-bind (word byte)
                      (fnn-core-page-read-pool 'fn-owner-history-image-effect-byte
                       cursor effect (fnn-hpi-stage-id stage) i
                       (fnn-hpi-writer-q0 writer) (fnn-hpi-writer-q1 writer)
                       (fnn-hpi-writer-q2 writer) (fnn-hpi-writer-q3 writer)
                       (fnn-hpi-writer-pool writer))
                    (unless (eq word :octet)
                      (return-from fnn-hpi-execute-effect '(:refused :image-scratch)))
                    (setf (aref data i) byte))))
            (loop for byte in payload for i from 0 do (setf (aref data i) byte))))
        (handler-case
            (progn
              (setf got (ecase operation
                          (:write (fnn-hpi-page-pwrite fd data offset count))
                          (:read (fnn-extent-page-pread fd data offset count)))
                    status :ok))
          (error () (setf got -1 status :error)))
        (when (eq operation :read)
          (let ((returned (sb-thread:with-mutex (*fnn-extent-lock*)
                            (fnn-core-page-read-pool 'fn-owner-history-image-effect-read-count
                             cursor effect (fnn-hpi-stage-id stage) got status))))
            ; This is a bounded representation copy of core-selected <=64
            ; verified returned octets, never a page/history materialization.
            (setf bytes (fnn-octet-list (subseq data 0 returned)))))))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (fnn-core-page-read-pool 'fn-owner-history-image-effect-result
                               cursor effect (fnn-hpi-stage-id stage) got status bytes))))
