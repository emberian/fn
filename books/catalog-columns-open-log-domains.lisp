; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-held-types")
(include-book "lb-log-guard-invariants")

(local (defthm fn-lbold-record-payload-octets
 (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-record-p fn-record-payloadp))))))

(defthm fn-lb-log-model-segsp-of-open-events
 (implies (and (natp h) (unsigned-byte-p 64 target) (fn-lb-log-model-segsp log)
 (fn-lb-open-records-guardp ws keyring generation h))
 (fn-lb-log-model-segsp (fn-lb-log-model-open-events ws keyring generation h target log)))
 :hints (("Goal" :induct (fn-lb-log-model-open-events ws keyring generation h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-open-records-guardp fn-lb-log-append-preserves-type
 fn-lbold-record-payload-octets fn-lb-open-wire-article-is-record natp)))))

(defthm fn-lb-verified-invp-of-open-events
 (implies (fn-lb-verified-invp log fn-lb-vmap)
 (fn-lb-verified-invp (fn-lb-log-model-open-events ws keyring generation h target log) fn-lb-vmap))
 :hints (("Goal" :induct (fn-lb-log-model-open-events ws keyring generation h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-verified-invp-of-append)))))

(defthm fn-lb-log-append-guardp-of-open-events
 (implies (fn-lb-log-append-guardp log)
 (fn-lb-log-append-guardp (fn-lb-log-model-open-events ws keyring generation h target log)))
 :hints (("Goal" :induct (fn-lb-log-model-open-events ws keyring generation h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-log-append-guardp-of-append)))))

(defthm fn-lb-log-read-guardp-of-open-events
 (implies (and (fn-lb-log-homes-guardp log) (fn-lb-log-append-guardp log)
 (fn-lb-open-records-guardp ws keyring generation h))
 (fn-lb-log-read-guardp (fn-lb-log-model-open-events ws keyring generation h target log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-home-and-append-domains-give-read-domain
 (log (fn-lb-log-model-open-events ws keyring generation h target log))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-homes-guardp-of-open-events fn-lb-log-append-guardp-of-open-events)))))
