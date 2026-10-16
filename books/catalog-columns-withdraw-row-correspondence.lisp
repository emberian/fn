; The actual resident row update agrees with the logical withdrawal effect.
; Summary cells are handled separately by the catalog writer.
(in-package "ACL2")
(include-book "catalog-columns-withdraw-row-projection")

(defthm fn-lbc-row-corr-of-set-withdrawal
 (implies (and (fn-lbc-p fn-lbc-v) (fn-cat-rowp row)
               (natp i) (< i (fn-lbc-count fn-lbc-v))
               (natp version) (natp by)
               (fn-lbc-row-corr i row pm fn-lbc-v log))
  (fn-lbc-row-corr i (fn-held-with-withdrawn row (cons version by)) pm
   (fn-lbc-set-withdrawal i version by fn-lbc-v) log))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-row-corr fn-lbc-loc0-of-set-withdrawal-by-definition
     fn-lbc-loc1-of-set-withdrawal-by-definition fn-lbc-home-entry-of-set-withdrawal-by-definition
     fn-lbc-served-row-of-set-withdrawal-by-definition
     fn-lbc-flag-4-of-set-withdrawal-by-definition fn-lbc-flag-5-of-set-withdrawal-by-definition
     fn-lbc-value-prefix-max-of-set-withdrawal-by-definition
     fn-lbc-value-head-length-of-set-withdrawal-by-definition
     fn-lbc-word-msgid-hash-of-set-withdrawal-by-definition
     fn-lbc-xref-shift-prefix-of-set-withdrawal-by-definition
     fn-lbc-directory-value-of-set-withdrawal-by-definition
     fn-lbc-render-nov-of-set-withdrawal-by-definition
     fn-lbcwd-logical-key-of-withdrawal-by-definition
     fn-lbcwd-logical-homes-of-withdrawal-by-definition
     fn-lbcwd-logical-home-frame-of-withdrawal-by-definition
     fn-lbcwd-logical-payload-of-withdrawal-by-definition
     fn-lbcwd-logical-projection-of-withdrawal-by-definition fn-held-withdrawnp)))))

(defthm fn-lbc-row-corr-other-of-set-withdrawal
 (implies (and (fn-lbc-p fn-lbc-v) (natp i) (< i (fn-lbc-count fn-lbc-v))
               (natp j) (< j (fn-lbc-count fn-lbc-v)) (not (equal i j))
               (fn-lbc-row-corr j row pm fn-lbc-v log))
  (fn-lbc-row-corr j row pm (fn-lbc-set-withdrawal i version by fn-lbc-v) log))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-row-corr fn-lbc-loc0-of-set-withdrawal-by-definition
     fn-lbc-loc1-of-set-withdrawal-by-definition fn-lbc-home-entry-of-set-withdrawal-by-definition
     fn-lbc-served-row-of-set-withdrawal-by-definition
     fn-lbc-flag-4-of-set-withdrawal-by-definition fn-lbc-flag-5-of-set-withdrawal-by-definition
     fn-lbc-value-prefix-max-of-set-withdrawal-by-definition
     fn-lbc-value-head-length-of-set-withdrawal-by-definition
     fn-lbc-word-msgid-hash-of-set-withdrawal-by-definition
     fn-lbc-xref-shift-prefix-of-set-withdrawal-by-definition
     fn-lbc-directory-value-of-set-withdrawal-by-definition
     fn-lbc-render-nov-of-set-withdrawal-by-definition)))))
