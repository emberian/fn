; NOV text-list pool effects, derived from the actual native writer.
; The logical concatenation uses DEF-LOOP's house :concat instance. Neither
; this model nor these pool length equalities are LB6 work counters.
(in-package "ACL2")
(include-book "catalog-columns-pool-refinement")
(include-book "def-loop")

(local (defthm fn-lbpt-append-associative
 (equal (append (append xs ys) zs) (append xs (append ys zs)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append)))))

(local (defthm fn-lbpt-len-append
 (equal (len (append xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(local (defthm fn-lbpt-append-nil
 (implies (true-listp xs) (equal (append xs nil) xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append true-listp)))))

(def-loop fn-lbc-texts-octets-model (texts)
 :shape :concat :over texts
 :body (true-list-fix (fn-record-string-octets (car texts)))
 :guard t :guard-theory (true-list-fix))

(defthm fn-lbc-append-nov-texts-is-model-append
 (equal (fn-lbc-overview-pool-model (fn-lbc-append-nov-texts texts fn-lbc))
        (append (fn-lbc-overview-pool-model fn-lbc) (fn-lbc-texts-octets-model texts)))
 :hints (("Goal" :induct (fn-lbc-append-nov-texts texts fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-append-nov-texts fn-lbc-texts-octets-model
    fn-lbc-overview-pool-append-is-model-append fn-lbpt-append-associative fn-lbpt-append-nil
    (:type-prescription fn-lbc-overview-pool-model-true-listp))))))

(defthm fn-lbc-overview-pool-count-of-append-nov-texts
 (equal (fn-lbc-overview-pool-count (fn-lbc-append-nov-texts texts fn-lbc))
        (+ (fn-lbc-overview-pool-count fn-lbc) (len (fn-lbc-texts-octets-model texts))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count-is-model-length fn-lbc-append-nov-texts-is-model-append
    fn-lbpt-len-append)))))
