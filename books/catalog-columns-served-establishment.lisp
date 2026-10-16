; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-catalog-locator-resolution")
(include-book "catalog-columns-served")

(defthm fn-lb-served-log-invp-from-correspondence
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-held-listp rows)
 (fn-lbc-corr fn-lbc rows log) (fn-lb-verified-invp log fn-lb-vmap))
 (fn-lb-served-log-invp log fn-lb-vmap fn-lbc rows))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-served-log-invp fn-lc-locators-resolve-from-catalog-corr)))))

(defthm fn-lb-served-log-invp-of-open-rebuild
 (implies (and (fn-lbc-p fn-lbc) (fn-held-listp rows) (fn-lbc-rows-log-guardp rows log)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (fn-lb-log-rows-sourcep rows log)
 (fn-lb-verified-invp log fn-lb-vmap))
 (fn-lb-served-log-invp log fn-lb-vmap (fn-lbc-open-rebuild rows log fn-lbc) rows))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-served-log-invp-from-correspondence
 (fn-lbc (fn-lbc-open-rebuild rows log fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-corr-of-open-rebuild fn-lbc-p-of-open-rebuild fn-held-listp-implies-cat-rowsp fn-cat$ap)))))
