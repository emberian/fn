(in-package "ACL2")
(include-book "../books/boot")

(defun fn2-checkpoint-geometry-fields-equalp (left a b fn2-fields)
 (declare (xargs :stobjs fn2-fields :verify-guards nil :measure (nfix left)))
 (if (zp left) t
  (and (equal (fn2-fields-value a fn2-fields) (fn2-fields-value b fn2-fields))
       (fn2-checkpoint-geometry-fields-equalp (- left 1) (+ a 1) (+ b 1) fn2-fields))))

; Exact generated-codec roundtrip for every geometry scalar and truncation
; control. This is a source fixture; no admission or execution is claimed.
(defun fn2-checkpoint-geometry-codec-test-body (fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
 (b* ((fn2-fields (fn2-fields-init 384 fn2-fields))
      (fn2-pool (fn2-pool-init '((1 . 512)) 1 100 fn2-pool))
      ((mv reserved slot gen fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
      ((unless (eq reserved :ok)) (mv nil fn2-fields fn2-pool))
      (fn2-fields (fn2-boot-geometry-fields (* 4096 12) 1 1 fn2-fields))
      ((mv encoded end fn2-pool)
       (fn2-checkpoint-geometry-record-encode 256 slot gen 0 1 0 1 fn2-fields fn2-pool))
      ((unless (eq encoded :ok)) (mv nil fn2-fields fn2-pool))
      ((mv decoded next fn2-fields)
       (fn2-checkpoint-geometry-record-decode 0 slot gen 0 end 1 0 1 fn2-fields fn2-pool))
      (roundtrip (and (eq decoded :ok) (equal next end)
                     (fn2-checkpoint-geometry-fields-equalp *fn2-checkpoint-geometry-record-num-fields* 0 256 fn2-fields)))
      ((mv truncated & fn2-fields)
       (fn2-checkpoint-geometry-record-decode 0 slot gen 0 (- end 1) 1 0 1 fn2-fields fn2-pool)))
  (mv (and roundtrip (not (eq truncated :ok))) fn2-fields fn2-pool)))
(defun fn2-checkpoint-geometry-codec-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (answer fn2-fields)
   (with-local-stobj fn2-pool
    (mv-let (answer fn2-fields fn2-pool)
     (fn2-checkpoint-geometry-codec-test-body fn2-fields fn2-pool) (mv answer fn2-fields))) answer)))
(assert-event (fn2-checkpoint-geometry-codec-test))
(assert-event (equal (length *fn2-checkpoint-geometry-domain*) 21))
