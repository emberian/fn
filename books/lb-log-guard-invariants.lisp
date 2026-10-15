; Guard domains derived from actual LOG constructors, never served revalidation.
; This core has no generic catalog/reclaim-owner dependency.
(in-package "ACL2")
(include-book "lb-log-open-model")

(local (defthm fn-lbhg-model-home-fields-domain
 (implies (fn-lb-value-treep (fn-lb-log-model-homes row))
 (fn-lb-home-fields-guardp (fn-lb-log-model-homes row)))
 :hints (("Goal" :do-not-induct t
 :in-theory (enable fn-lb-home-fields-guardp fn-lb-log-model-homes)))))

(local (defthm fn-lbhg-entries-of-append
 (equal (fn-lb-entries-homes-guardp (append a b))
 (and (fn-lb-entries-homes-guardp a) (fn-lb-entries-homes-guardp b)))
 :hints (("Goal" :induct (append a b)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-entries-homes-guardp binary-append))))))

(local (defthm fn-lbhg-appended-segment-homes
 (implies (and (fn-lb-value-treep (fn-lb-log-model-homes row))
 (fn-lb-entries-homes-guardp (caddr segment)))
 (and (true-listp (fn-lb-log-model-append-to-segment row payload segment))
 (fn-lb-entries-homes-guardp (caddr (fn-lb-log-model-append-to-segment row payload segment)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-to-segment fn-lbhg-entries-of-append fn-lb-entries-homes-guardp
   fn-lbhg-model-home-fields-domain nth true-listp))))))

(local (defthm fn-lbhg-empty-entry-homes
 (fn-lb-entries-homes-guardp nil)
 :hints (("Goal" :in-theory '(fn-lb-entries-homes-guardp)))))

(defthm fn-lb-log-homes-guardp-of-append
 (implies (and (fn-lb-log-homes-guardp log) (fn-lb-value-treep (fn-lb-log-model-homes row)))
 (fn-lb-log-homes-guardp (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lb-log-homes-guardp fn-lbhg-appended-segment-homes fn-lbhg-empty-entry-homes)))))

(defthm fn-lb-log-homes-guardp-of-recycle
 (implies (fn-lb-log-homes-guardp log)
 (fn-lb-log-homes-guardp (fn-lb-log-model-recycle victim log)))
 :hints (("Goal" :induct (fn-lb-log-model-recycle victim log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-recycle fn-lb-log-homes-guardp)))))

(defthm fn-lb-log-homes-guardp-of-open-events
 (implies (and (fn-lb-open-records-guardp ws keyring generation h) (fn-lb-log-homes-guardp log))
 (fn-lb-log-homes-guardp (fn-lb-log-model-open-events ws keyring generation h target log)))
 :hints (("Goal" :induct (fn-lb-log-model-open-events ws keyring generation h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-open-records-guardp fn-lb-log-homes-guardp-of-append)))))

(local (defthm fn-lbhg-homes-entries-lists
 (implies (fn-lb-entries-homes-guardp entries) (true-list-listp (true-list-fix entries)))
 :hints (("Goal" :induct (fn-lb-entries-homes-guardp entries)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-entries-homes-guardp true-list-listp true-list-fix))))))

(defthm fn-lb-log-homes-guardp-gives-entries
 (implies (fn-lb-log-homes-guardp log) (fn-lb-log-entries-guardp log))
 :hints (("Goal" :induct (fn-lb-log-homes-guardp log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-homes-guardp fn-lb-log-entries-guardp fn-lbhg-homes-entries-lists)))))

(defthm fn-lb-log-home-and-append-domains-give-read-domain
 (implies (and (fn-lb-log-homes-guardp log) (fn-lb-log-append-guardp log))
 (fn-lb-log-read-guardp log))
 :hints (("Goal" :induct (fn-lb-log-homes-guardp log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-homes-guardp fn-lb-log-append-guardp fn-lb-log-read-guardp fn-lbhg-homes-entries-lists)))))
