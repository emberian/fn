; Typed home-domain preservation for the actual reclaim LOG producer.
(in-package "ACL2")
(include-book "lb-log-guard-invariants")
(include-book "lb-log-reclaim-model")
(defthm fn-lb-log-homes-guardp-of-reclaim-events
 (implies (and (fn-lb-reclaim-records-guardp rows id h) (fn-lb-log-homes-guardp log))
 (fn-lb-log-homes-guardp (fn-lb-log-model-reclaim-events rows id h target log)))
 :hints (("Goal" :induct (fn-lb-log-model-reclaim-events rows id h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-reclaim-events fn-lb-reclaim-records-guardp fn-lb-log-homes-guardp-of-append)))))
