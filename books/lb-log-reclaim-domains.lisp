; Carried structural domains for the actual reclaim LOG fold.
(in-package "ACL2")
(include-book "lb-log-reclaim-guard-properties")
(include-book "catalog-columns-log-type-preservation")
(include-book "lb-log-layout")
(local (defthm fn-lbrd-record-payload-octets
 (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero) '(fn-record-p fn-record-payloadp))))))
(defthm fn-lb-log-model-reclaim-preserves-layout
 (implies (fn-lb-log-layoutp log)
 (fn-lb-log-layoutp (fn-lb-log-model-reclaim-events rows id h target log)))
 :hints (("Goal" :induct (fn-lb-log-model-reclaim-events rows id h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-reclaim-events fn-lb-log-model-append-preserves-layout)))))
(defthm fn-lb-log-model-reclaim-preserves-type
 (implies (and (fn-lb-reclaim-records-guardp rows id h)
 (unsigned-byte-p 64 target) (fn-lb-log-model-segsp log))
 (fn-lb-log-model-segsp (fn-lb-log-model-reclaim-events rows id h target log)))
 :hints (("Goal" :induct (fn-lb-log-model-reclaim-events rows id h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-reclaim-events fn-lb-reclaim-records-guardp
 fn-lbrd-record-payload-octets fn-lb-log-append-preserves-type)))))
