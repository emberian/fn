; Link operation counts to the existing available-number result, not a separate oracle.
(in-package "ACL2")
(include-book "catalog-columns-command-cost")
(include-book "catalog-columns-command-refinement")

(defthm fn-lbc-over-eligible-count-is-listgroup-count
 (equal (len (fn-lbc-over-eligible group v lo hi fn-lbc))
        (len (fn-lbc-listgroup group v lo hi fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-over-eligible group v lo hi fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-over-eligible fn-lbc-listgroup len)))))

(defthm fn-lbc-over-fetches-available-reference-numbers
 (implies (and (fn-lbc-p fn-lbc-v) (fn-cat$ap rows) (fn-lbc-corr fn-lbc-v rows log) (natp v))
  (equal (fn-lbc-over-row-fetches group v lo hi fn-lbc-v)
         (len (fn-scat-available-numbers group lo hi v rows))))
 :hints (("Goal" :use ((:instance fn-lbc-over-eligible-count-is-listgroup-count (fn-lbc fn-lbc-v))
                      (:instance fn-lbc-listgroup-is-available-numbers (fn-lbc fn-lbc-v)))
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-over-fetches-exactly-eligible)))))
