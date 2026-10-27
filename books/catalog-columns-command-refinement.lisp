; Command candidate selection refines the existing available-number reference.
(in-package "ACL2")
(include-book "catalog-columns-command-availability")
(include-book "catalog-columns-row-correspondence")
(include-book "catalog-columns-selector-properties")
(include-book "catalog-available-readers")



(local (defthm fn-lbccr-id-test-is-abstract
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
               (natp i) (< i (len rows)))
  (equal (fn-nntp-article-idp (fn-lbc-id-article i fn-lbc))
         (fn-scat-msgid-idp (fn-record-msgid (nth i rows)))))
 :hints (("Goal" :use fn-lbc-served-fields-are-abstract
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-id-article fn-nntp-article-idp fn-scat-msgid-idp fn-make-article fn-article-msgid))))))

(defthm fn-lbc-command-row-is-available-number
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log) (natp v))
  (iff (fn-lbc-command-row group number v fn-lbc) (fn-scv-keptp group number v rows)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-command-row-observes-original-nov)
        (:instance fn-lbc-number-get-is-abstract)
        (:instance fn-lbc-corr-count-is-length)
        (:instance fn-lbc-original-nov-is-abstract (i (fn-lbc-number-get group number fn-lbc)))
        (:instance fn-lbccr-id-test-is-abstract (i (fn-lbc-number-get group number fn-lbc)))
        (:instance fn-lbc-visible-is-row-visible-total-version (i (fn-lbc-number-get group number fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-scv-keptp fn-cat-group-number-is-number-seq fn-cat-count-is-len fn-cat-at-is-nth
     fn-cat-visible-at-is-visiblep fn-cat-row-availablep fn-cat-row-facts-decidedp natp nfix)))))

(defthm fn-lbc-listgroup-is-available-numbers
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log) (natp v))
  (equal (fn-lbc-listgroup group v lo hi fn-lbc)
         (fn-scat-available-numbers group lo hi v rows)))
 :hints (("Goal" :induct (fn-lbc-listgroup group v lo hi fn-lbc)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-listgroup fn-scat-available-numbers fn-lbc-command-row-is-available-number)))))
