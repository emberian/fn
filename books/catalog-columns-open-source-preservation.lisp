; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-source-preservation")
(include-book "lb-log-handle-allocation")
(include-book "lb-log-open-model")

(local (defthm fn-lbosp-intern-row-at-payload
 (equal (fn-record-payload (fn-intern-row-at w keyring generation h)) h)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-row-at fn-held-make fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbosp-new-entry-allocation
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (fn-lb-log-handles-below
  (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) payload target log) (+ 1 h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-handles-below-of-append (n h) (newn (+ 1 h)) (row (fn-intern-row-at w keyring generation h))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbosp-intern-row-at-payload natp))))))

(local (defthm fn-lbosp-intern-row-key-fresh
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (not (fn-lb-log-model-row-entry (fn-intern-row-at w keyring generation h) log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-handles-below-gives-fresh-key
 (row (fn-intern-row-at w keyring generation h)) (n h)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbosp-intern-row-at-payload natp nfix))))))

(defthm fn-lb-log-rows-sourcep-preserved-by-open-events
 (implies (and (natp h) (fn-lb-log-handles-below log h)
               (fn-cat-rowsp rows) (fn-lb-log-rows-sourcep rows log))
 (fn-lb-log-rows-sourcep rows (fn-lb-log-model-open-events ws keyring generation h target log)))
 :hints (("Goal" :induct (fn-lb-log-model-open-events ws keyring generation h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-log-rows-sourcep-of-fresh-append-old
 fn-lbosp-new-entry-allocation fn-lbosp-intern-row-key-fresh natp)))))

(defthm fn-lb-log-layoutp-of-open-events
 (implies (fn-lb-log-layoutp log)
 (fn-lb-log-layoutp (fn-lb-log-model-open-events ws keyring generation h target log)))
 :hints (("Goal" :induct (fn-lb-log-model-open-events ws keyring generation h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-log-model-append-preserves-layout)))))
