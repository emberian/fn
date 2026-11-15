; Codec records use the submitted, unposted incarnation of the actual loan.
(in-package "ACL2")
(include-book "host-loan")
(include-book "tls-stack")
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

(defun fn2-host-active-op (op gen fn2-core)
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
     (t (mv-let (cap nonce) (fn2-op-capability op fn2-ops)
          (mv :ok (fn2-ops-kind op fn2-ops) cap nonce))))
    (if (eq code :ok) (mv :ok kind cap nonce address length)
      (mv code 0 0 0 0 0))))))





(defun fn2-host-codec-op (op gen fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (mv-let (code kind cap nonce address length) (fn2-host-active-op op gen fn2-core)
  (cond ((not (eq code :ok)) (mv code 0 0 0 0 0))
        ((not (member-equal kind (list *fn2-action-send* *fn2-action-receive*)))
         (mv :kind 0 0 0 0 0))
        (t (mv :ok kind cap nonce address length)))))

; External application loan entry. Child/private windows use the stack bridge.
(defun fn2-host-tls-record-next (op gen room pending fn2-tls-transport fn2-tls-record fn2-core)
 (declare (xargs :stobjs (fn2-tls-transport fn2-tls-record fn2-core) :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core) (fn2-tls-transport-wfp fn2-tls-transport)
              (= (fn2-tls-transport-rows fn2-tls-transport) 1) (fn2-tls-record-wfp fn2-tls-record))))
 (mv-let (code kind cap nonce address length) (fn2-host-codec-op op gen fn2-core)
  (if (not (and (eq code :ok) (natp address) (unsigned-byte-p 32 length)))
      (mv (if (eq code :ok) :bounds code) 0 0 0 0 0 fn2-tls-transport fn2-tls-record)
   (mv-let (bound fn2-tls-record)
    (fn2-tls-record-start cap nonce op gen length 0 (equal kind *fn2-action-send*) fn2-tls-record)
    (if (not (eq bound :ok)) (mv bound 0 0 0 0 0 fn2-tls-transport fn2-tls-record)
     (mv-let (status action offset count serial fn2-tls-transport fn2-tls-record)
      (fn2-tls-record-next room pending fn2-tls-transport fn2-tls-record)
      (mv status action
          (if (and (eq status :act) (member-equal action '(12 13))) (+ address offset) address)
          offset count serial fn2-tls-transport fn2-tls-record)))))))

; The core operation authorizes the upper codec; the pending upper action
; authorizes the lower private span. Application progress stays in the upper op.
(defun fn2-host-tls-child-next
 (op gen room pending fn2-compress-transport fn2-tls-transport fn2-tls-record fn2-core)
 (declare (xargs :stobjs (fn2-compress-transport fn2-tls-transport fn2-tls-record fn2-core)
  :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core)
              (fn2-compress-transport-wfp fn2-compress-transport) (= (fn2-compress-transport-rows fn2-compress-transport) 1)
              (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1)
              (fn2-tls-record-wfp fn2-tls-record))))
 (mv-let (code kind cap nonce address length) (fn2-host-codec-op op gen fn2-core)
  (declare (ignore kind address length))
  (mv-let (parent channel base extent parent-serial)
   (fn2-compress-tls-parent cap nonce op gen fn2-compress-transport)
   (declare (ignore base))
   (if (not (and (eq code :ok) (eq parent :ok)))
       (mv :stale 0 0 0 0 0 fn2-tls-transport fn2-tls-record)
    (mv-let (bound fn2-tls-record)
     (fn2-tls-record-start cap nonce op gen extent parent-serial (= channel 3) fn2-tls-record)
     (if (not (eq bound :ok)) (mv bound 0 0 0 0 0 fn2-tls-transport fn2-tls-record)
      (mv-let (status action offset count serial fn2-tls-transport fn2-tls-record)
       (fn2-tls-record-next room pending fn2-tls-transport fn2-tls-record)
       (if (and (eq status :act) (member-equal action '(12 13)))
           (mv-let (span private-channel private-offset private-count)
            (fn2-compress-tls-span cap nonce op gen serial action offset count
             fn2-compress-transport fn2-tls-transport fn2-tls-record)
            (mv (if (eq span :ok) :act span) action private-channel private-offset private-count serial
                fn2-tls-transport fn2-tls-record))
         (mv status action 0 offset count serial fn2-tls-transport fn2-tls-record)))))))))
