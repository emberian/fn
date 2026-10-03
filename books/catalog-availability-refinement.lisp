; Actual recovery/reclaim loader keeps the byte-fact invariant F.
(in-package "ACL2")
(include-book "catalog-availability-owner-load")
(include-book "served-columns")

(defun fn-scol-history-okp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp rows)
      (and (or (not (fn-cat-rowp (car rows)))
               (fn-scol-row-okp (car rows) fn-arena))
           (or (not (fn-sca-composite-shapep (car rows)))
               (fn-scol-row-okp (fn-hstxa-held (car rows)) fn-arena))
           (fn-scol-history-okp (cdr rows) fn-arena))
    t))

(defthm fn-cat-prepare-row-availability-keeps-byte-facts
  (implies (fn-scol-row-okp h fn-arena)
           (fn-scol-row-okp (fn-cat-prepare-row-availability h fn-arena) fn-arena))
  :hints (("Goal" :in-theory
           (e/d (fn-scol-row-okp fn-cat-prepare-row-availability)
                (fn-held-with-facts fn-held-facts-of fn-hf-nov)))))

(local (defthm fn-sca-classified-row-keeps-byte-facts
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-cat-rowp r) (fn-scol-row-okp r fn-arena))
           (fn-scol-okp fn-arena (fn-sca-load-held-row r view-index fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-sca-load-held-row)
                (fn-sca-composite-shapep fn-cat-rowp fn-held-with-withdrawn
                 fn-cat-commit-is-append fn-midx-lookup fn-scol-okp))))))

(local (defthm fn-sca-available-row-keeps-byte-facts
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-history-okp (list r) fn-arena))
           (fn-scol-okp fn-arena
             (fn-sca-load-held-available-row r view-index fn-arena fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-sca-load-held-available-row fn-sca-composite-shapep fn-scol-history-okp)
                (fn-scol-okp fn-cat-rowp fn-scol-row-okp
                 fn-cat-prepare-row-availability fn-sca-load-held-row fn-held-p))))))

(defthm fn-sca-load-held-available-from-keeps-byte-facts
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-history-okp rows fn-arena))
           (fn-scol-okp fn-arena
             (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)
           :in-theory
           (e/d (fn-sca-load-held-available-from fn-sca-held-rowsp fn-scol-history-okp)
                (fn-scol-okp fn-scol-row-okp fn-sca-load-held-available-row
                 fn-cat-rowp fn-sca-composite-shapep)))))

; Actual public loader, including legacy missing facts.
(defthm fn-sca-load-held-rows-establishes-byte-facts
  (implies (and (fn-arena-p fn-arena)
                (fn-scol-history-okp rows fn-arena))
           (fn-scol-okp fn-arena (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance fn-sca-load-held-available-from-keeps-byte-facts (fn-cat nil))
                        (:instance fn-scol-okp-of-clear))
           :in-theory
           (e/d (fn-sca-load-held-rows)
                (fn-scol-okp fn-scol-row-okp fn-scol-history-okp
                 fn-sca-held-rowsp fn-sca-load-held-available-from
                 fn-sca-load-held-available-from-keeps-byte-facts)))))
