;; The host boundary's ops entries: the adapter's posts, acks and finishes
;; into the ops child and its scalar reads of it, over the live core. Only
;; the assembled core and its ops child are needed, so the books that reason about these
;; entries include this one rather than the whole boundary.
(in-package "ACL2")
(include-book "assembly-core")

(local (in-theory (enable fn2-core-wfp)))

(defmacro fn2-host-ops-update (name target args)
  `(defun ,name (,@args fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
       (fn2-ops) (,target ,@args fn2-ops) fn2-core)))
(fn2-host-ops-update fn2-host-post-result fn2-post-result
  (cell slot gen evkind outcome reason count aux0 aux1))
(fn2-host-ops-update fn2-host-post-accept-result fn2-post-accept-result
  (slot gen outcome reason cap-index cap-nonce family port w0 w1 w2 w3))
(fn2-host-ops-update fn2-host-post-clock fn2-post-clock (mono real flags))
(fn2-host-ops-update fn2-host-post-signal fn2-post-signal (bits))
(fn2-host-ops-update fn2-host-count-stray fn2-count-stray ())

(defmacro fn2-host-ops-code-update (name target args)
  `(defun ,name (,@args fn2-core)
     (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
     (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
       (code fn2-ops) (,target ,@args fn2-ops) (mv code fn2-core))))
(fn2-host-ops-code-update fn2-host-outbox-ack fn2-outbox-ack (n))
(fn2-host-ops-code-update fn2-host-op-finish fn2-op-finish (slot gen))

(defun fn2-host-outbox-queued (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (count) (fn2-outbox-queued fn2-ops) count))

(defun fn2-host-stray (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (count) (fn2-ops-stray fn2-ops) count))

(defun fn2-host-outbox-peek (k fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code slot gen) (fn2-outbox-peek k fn2-ops) (mv code slot gen)))

; Fixed-width multiple values: no descriptor list and no byte list. A slot
; outside the table is the adapter's error, answered :bounds with no fields.
(defun fn2-host-action (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code kind cap-index cap-nonce range-slot range-gen range-off range-len
          storage-offset fua may-release cancel-slot cancel-gen
          wake-deadline wake-observation-gen)
    (if (not (fn2-op-slotp slot fn2-ops))
        (mv :bounds 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (b* (((mv cap-index cap-nonce) (fn2-op-capability slot fn2-ops))
           ((mv range-slot range-gen range-off range-len) (fn2-op-range slot fn2-ops))
           ((mv storage-offset fua) (fn2-op-storage slot fn2-ops))
           ((mv cancel-slot cancel-gen) (fn2-op-cancel-target slot fn2-ops))
           ((mv wake-deadline wake-observation-gen) (fn2-op-wake slot fn2-ops)))
        (mv :ok (fn2-op-kind slot fn2-ops) cap-index cap-nonce
            range-slot range-gen range-off range-len storage-offset fua
            (fn2-op-may-release slot fn2-ops) cancel-slot cancel-gen
            wake-deadline wake-observation-gen)))
    (mv code kind cap-index cap-nonce range-slot range-gen range-off range-len
        storage-offset fua may-release cancel-slot cancel-gen
        wake-deadline wake-observation-gen)))
