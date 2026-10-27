; The carried served invariant survives authentication of an entry.
(in-package "ACL2")
(include-book "catalog-columns-served")
(include-book "log-verified-map-reset")
(include-book "catalog-columns-served-establishment")

; Model variables permit explicit ground proofs of these proof-only predicates.
; The subject is the same guard-verified stobj writer the host invokes.
(defthm fn-lb-served-log-invp-of-mark
 (implies (fn-lb-served-log-invp log fn-lb-vmap-v fn-lbc-v rows)
  (fn-lb-served-log-invp log
   (fn-lb-vmap-mark seg entry log fn-lb-vmap-v) fn-lbc-v rows))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-served-log-invp fn-lb-verified-invp-of-mark)))))

(defthm fn-lb-served-log-invp-of-clear-verification
 (implies (fn-lb-served-log-invp log fn-lb-vmap-v fn-lbc-v rows)
  (fn-lb-served-log-invp log (fn-lb-vmap-clear fn-lb-vmap-v) fn-lbc-v rows))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-served-log-invp fn-lb-verified-invp-of-clear)))))

(defthm fn-lb-served-log-invp-of-reopen-clear
 (implies (and (fn-lbc-p fn-lbc-v) (fn-held-listp rows)
               (fn-lbc-rows-log-guardp rows log) (fn-lb-log-layoutp log)
               (fn-lb-log-model-segsp log) (fn-lb-log-rows-sourcep rows log))
  (fn-lb-served-log-invp log (fn-lb-vmap-clear fn-lb-vmap-v)
   (fn-lbc-open-rebuild rows log fn-lbc-v) rows))
 :hints (("Goal" :use ((:instance fn-lb-served-log-invp-of-open-rebuild
  (fn-lbc fn-lbc-v) (fn-lb-vmap (fn-lb-vmap-clear fn-lb-vmap-v))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-verified-invp-of-clear)))))
