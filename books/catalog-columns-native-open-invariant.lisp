; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-log-domains")

(local (defthm fn-lbnoi-arena-count-natural
 (natp (fn-arena-count fn-arena)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len natp))))))

(defthm fn-lb-native-open-establishes-served-log-invp
 (implies (and (fn-arena-p fn-arena) (natp generation) (fn-lbc-p fn-lbc)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (unsigned-byte-p 64 target)
 (fn-lb-log-handles-below log (fn-arena-count fn-arena))
 (fn-lb-open-records-guardp ws keyring generation (fn-arena-count fn-arena))
 (fn-lb-verified-invp log fn-lb-vmap)
 (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad))
 (fn-lbc-rows-log-guardp (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))) (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log)))
 (fn-lb-served-log-invp (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log) fn-lb-vmap (fn-lbc-open-rebuild (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))) (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log) fn-lbc) (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-model-open-sources-interned-rows)
 (:instance fn-lb-open-interned-rows-have-held-type)
 (:instance fn-lb-served-log-invp-of-open-rebuild (rows (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))) (log (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-layoutp-of-open-events fn-lb-log-model-segsp-of-open-events
 fn-lb-verified-invp-of-open-events fn-lbnoi-arena-count-natural)))))

(defthm fn-lb-native-open-establishes-column-read-domains
 (implies (and (natp generation) (fn-lbc-p fn-lbc)
 (fn-lb-log-homes-guardp log) (fn-lb-log-append-guardp log)
 (fn-lb-open-records-guardp ws keyring generation (fn-arena-count fn-arena))
 (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad))
 (fn-lbc-rows-log-guardp (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))) (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log)))
 (and (fn-cat$ap (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))) (fn-lb-log-homes-guardp (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log)) (fn-lb-log-read-guardp (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log))
 (fn-lbc-p (fn-lbc-open-rebuild (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))) (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log) fn-lbc))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lb-open-interned-rows-have-held-type))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-held-listp-implies-cat-rowsp fn-cat$ap
 fn-lb-log-homes-guardp-of-open-events fn-lb-log-read-guardp-of-open-events fn-lbc-p-of-open-rebuild)))))
