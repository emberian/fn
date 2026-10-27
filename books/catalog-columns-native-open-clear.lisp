; Native open establishes verification after clearing volatile knowledge.
(in-package "ACL2")
(include-book "catalog-columns-native-open-invariant")
(include-book "log-verified-map-reset")
(defthm fn-lb-native-open-establishes-served-log-invp-after-clear
(implies (and (fn-arena-p fn-arena) (natp generation) (fn-lbc-p fn-lbc)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (unsigned-byte-p 64 target)
 (fn-lb-log-handles-below log (fn-arena-count fn-arena))
 (fn-lb-open-records-guardp ws keyring generation (fn-arena-count fn-arena))

 (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad))
 (fn-lbc-rows-log-guardp (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))) (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log)))
 (fn-lb-served-log-invp (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log) (fn-lb-vmap-clear fn-lb-vmap) (fn-lbc-open-rebuild (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))) (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log) fn-lbc) (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lb-native-open-establishes-served-log-invp
   (fn-lb-vmap (fn-lb-vmap-clear fn-lb-vmap))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-verified-invp-of-clear)))))
