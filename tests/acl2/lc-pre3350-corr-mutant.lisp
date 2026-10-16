; Exact top-level correspondence predicate from pre-LB 47f5cc20b.
; TEST MUTANT: the directory-count and log-SEGSP conjuncts are absent.
(in-package "ACL2")
(include-book "../../books/catalog-columns")
(defun-nx lct-pre3350-corr (fn-lbc rows log)
  (and (equal (fn-lbc-count fn-lbc) (len rows))
       (equal (fn-lbc-summary-groups fn-lbc) (fn-lbc-row-group-keys rows))
       (fn-lbc-rows-corr 0 rows 0 fn-lbc log)
       (fn-lbc-tables-corr fn-lbc rows)
       (fn-lbc-number-rows-covered rows rows fn-lbc)
       (fn-lbc-slots-corr fn-lbc rows)
       (fn-lbc-summaries-corr (fn-lbc-row-group-keys rows) rows fn-lbc)))
