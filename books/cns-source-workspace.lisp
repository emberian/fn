;; The existing CNS item lease also holds a streamed source's immutable
;; descriptor and two disjoint physical windows; no additional pool loan.
(in-package "ACL2")
(include-book "ordered")
(fn2-book-layer :c)
(defconst *fn2-cns-item-fixed* 22)
;; Original declaration, moved unchanged from cns.lisp.
(defconst *fn2-cns-item-workspace-bytes*
 (+ 32 (* 2 *fn2-commit-unit-bytes*) (* 2 *fn2-overview-octets-max*) *fn2-cns-item-fixed*))
(defconst *fn2-cns-source-vector-offset* 0)
(defconst *fn2-cns-source-original-offset* *fn2-article-location-hashes-max*)
(defconst *fn2-cns-source-stored-offset* (+ *fn2-cns-source-original-offset* 32))
(defconst *fn2-cns-source-prefix* (+ *fn2-cns-source-stored-offset* 32))
(defconst *fn2-cns-source-manifest-offset* *fn2-cns-source-prefix*)
(defconst *fn2-cns-source-data-offset* (+ *fn2-cns-source-prefix* *fn2-commit-unit-bytes*))
(defconst *fn2-cns-source-workspace-bytes* (+ *fn2-cns-source-data-offset* *fn2-commit-unit-bytes*))
(defthm fn2-cns-source-windows-within-item-workspace
 (and (<= (+ *fn2-cns-source-vector-offset* *fn2-article-location-hashes-max*) *fn2-cns-source-original-offset*)
      (<= (+ *fn2-cns-source-original-offset* 32) *fn2-cns-source-stored-offset*)
      (<= (+ *fn2-cns-source-stored-offset* 32) *fn2-cns-source-manifest-offset*)
      (<= (+ *fn2-cns-source-manifest-offset* *fn2-commit-unit-bytes*) *fn2-cns-source-data-offset*)
      (<= *fn2-cns-source-workspace-bytes* *fn2-cns-item-workspace-bytes*))
 :rule-classes nil)
