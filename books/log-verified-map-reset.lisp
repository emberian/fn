; Reopen discards volatile verification knowledge before accepting reads.
(in-package "ACL2")
(include-book "log-verified-map-invariants")

(defun fn-lb-vmap-clear (fn-lb-vmap)
 (declare (xargs :stobjs fn-lb-vmap :guard t))
 (let ((fn-lb-vmap (fn-lb-vmap-bits-clear fn-lb-vmap)))
  (update-fn-lb-vmap-index nil fn-lb-vmap)))

(defthm fn-lb-verified-invp-of-clear
 (fn-lb-verified-invp log (fn-lb-vmap-clear fn-lb-vmap-v))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-verified-invp fn-lb-vmap-clear fn-lb-vmap-bits-clear
    update-fn-lb-vmap-index fn-lb-verified-entries-invp fn-lb-vmap-index-covers
    nth update-nth zp)))))
