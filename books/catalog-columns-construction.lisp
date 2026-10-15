; Constructor representation invariants: derived from the actual producers.
; This pure book must not include generic CATALOG, the attachment's consumer.
(in-package "ACL2")
(include-book "catalog-columns-writer-frames")

(defthm fn-lbc-slot-count-of-clear-columns
 (equal (fn-lbc-slot-count (fn-lbc-clear-columns fn-lbc)) 0)
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-lbc-slot-count fn-lbc-clear-columns) (fn-lbc-p)))))

(defthm fn-lbc-corr-of-clear-columns
 (equal (fn-lbc-corr (fn-lbc-clear-columns fn-lbc) nil log)
        (fn-lb-log-model-segsp log))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-lbc-corr fn-lbc-clear-columns fn-lbc-count fn-lbc-slot-count make-list-ac fn-lbc-rows-corr fn-lbc-row-group-keys
  fn-lbc-directory-count-is-len fn-lbc-tables-corr fn-lbc-number-rows-covered fn-lbc-slots-corr fn-lbc-summaries-corr
  fn-lbc-slot-cells-corr fn-lbc-canonical-slots fn-lbc-canonical-slots-from
  fn-lbc-number-cells-corr fn-lbc-summary-cells-corr)
 (fn-lbc-p)))))

(defun-nx fn-lb-columns-directory-alignedp (fn-lbc)
 ; Proof-only layout, carried by constructors; never a served validation walk.
 (equal (len (nth *fn-lbc-directory-store* fn-lbc)) (fn-lbc-count fn-lbc)))

(defthm fn-lb-columns-directory-alignedp-of-clear-columns
 (fn-lb-columns-directory-alignedp (fn-lbc-clear-columns fn-lbc))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-lb-columns-directory-alignedp fn-lbc-clear-columns fn-lbc-count) (fn-lbc-p)))))

; BEGIN actual directory append preservation
(local
   (defthm fn-lbdd-len-append-singleton
    (equal (len (append xs (list value))) (+ 1 (len xs)))
    :hints (("Goal" :induct (len xs)
             :in-theory (union-theories (theory 'ground-zero) '(binary-append len))))))

(defthm fn-lbc-append-row-directory-count
   (equal (len (nth *fn-lbc-directory-store* (fn-lbc-append-row row log fn-lbc)))
          (+ 1 (len (nth *fn-lbc-directory-store* fn-lbc))))
   :hints (("Goal" :do-not '(preprocess) :do-not-induct t
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(fn-lbc-append-row update-fn-lbc-row-store update-fn-lbc-directory-store
        fn-lbc-row-store fn-lbc-directory-store fn-lbc-directory-append-is-append
        fn-dm-nth-update-nth fn-lbdd-len-append-singleton
        fn-lbwf-msgid-pool-append-field fn-lbwf-overview-pool-append-field
        fn-lbwf-append-nov-texts-field fn-lbwf-append-nov-field
        fn-lbwf-append-memberships-field fn-lbwf-escape-store-put-field
        (:executable-counterpart member-equal) (:executable-counterpart natp)
        (:executable-counterpart nfix) (:executable-counterpart equal)
        (:executable-counterpart not) (:executable-counterpart car)
        (:executable-counterpart cdr) car-cons cdr-cons
        (:type-prescription len))))))

(defthm fn-lb-columns-directory-alignedp-of-append-row
   (implies (fn-lb-columns-directory-alignedp fn-lbc)
            (fn-lb-columns-directory-alignedp (fn-lbc-append-row row log fn-lbc)))
   :hints (("Goal" :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
     '(fn-lb-columns-directory-alignedp fn-lbc-append-row-directory-count
       fn-lbc-count-of-append-row)))))
