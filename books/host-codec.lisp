; Codec records use the submitted, unposted incarnation of the actual loan.
(in-package "ACL2")
(include-book "host-loan")
(include-book "tls-transport-reservation")
(local (in-theory (enable fn2-core-wfp)))
(local
 (in-theory
  (disable fn2-ops-rows fn2-ops-gen fn2-ops-phase fn2-ops-kind
           fn2-ops-range-slot fn2-ops-range-gen fn2-ops-range-off fn2-ops-range-len
           fn2-ops-owner-kind fn2-ops-owner-slot fn2-ops-owner-gen
           fn2-pool-rows fn2-pool-gen fn2-pool-cap fn2-pool-base
           fn2-pool-data-length fn2-pool-lease-off fn2-pool-lease-len
           fn2-pool-state fn2-pool-out-count fn2-pool-fill
           fn2-pool-ownerp fn2-pool-input-code)))

(defun fn2-host-codec-op (op gen fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (mv-let (span-code address length) (fn2-host-op-span op gen fn2-core)
  (if (not (eq span-code :ok)) (mv span-code 0 0 0 0 0)
   (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code kind cap nonce)
    (cond
     ((not (and (natp op) (< op (fn2-ops-rows fn2-ops)))) (mv :bounds 0 0 0))
     ((not (equal gen (fn2-ops-gen op fn2-ops))) (mv :stale 0 0 0))
     ((or (not (equal (fn2-ops-phase op fn2-ops) *fn2-op-phase-submitted*))
          (not (equal (fn2-ops-c0-posted op fn2-ops) 0))) (mv :state 0 0 0))
     ((not (member-equal (fn2-ops-kind op fn2-ops)
                         (list *fn2-action-send* *fn2-action-receive*)))
      (mv :kind 0 0 0))
     (t (mv-let (cap nonce) (fn2-op-capability op fn2-ops)
          (mv :ok (fn2-ops-kind op fn2-ops) cap nonce))))
    (if (eq code :ok) (mv :ok kind cap nonce address length)
      (mv code 0 0 0 0 0))))))

(defun fn2-host-tls-record-select (op gen fn2-tls-transport fn2-core)
 (declare (xargs :stobjs (fn2-tls-transport fn2-core) :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core)
              (fn2-tls-transport-wfp fn2-tls-transport)
              (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (mv-let (code kind cap nonce address length) (fn2-host-codec-op op gen fn2-core)
  (cond
   ((not (eq code :ok)) (mv code 0 0 0 0 fn2-tls-transport))
   ((not (and (natp address) (unsigned-byte-p 32 length)))
    (mv :bounds 0 0 0 0 fn2-tls-transport))
   (t
    (let* ((writep (equal kind *fn2-action-send*))
           (count (min length (fn2-tls-transport-quantum 0 fn2-tls-transport)))
           (action (if writep 13 12)))
     (mv-let (code serial fn2-tls-transport)
      (fn2-tls-transport-select cap nonce op gen action
       (if writep 4 0) 0 (if writep count 0) (if writep length 0)
       (if writep 0 5) 0 (if writep 0 count) (if writep 0 length)
       fn2-tls-transport)
      (if (eq code :ok) (mv :ok action address count serial fn2-tls-transport)
       (mv code 0 0 0 0 fn2-tls-transport))))))))

(verify-guards fn2-host-tls-record-select
 :hints (("Goal" :in-theory
  (set-difference-theories (disable fn2-host-codec-op fn2-tls-transport-select)
                          (theory 'fn2-tls-transport-readers)))))
