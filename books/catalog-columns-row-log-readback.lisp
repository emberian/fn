; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-old-row-corr-readback")

(defthm fn-lbc-locator-of-append-row-new
 (implies (fn-lbc-row-log-guardp row log)
  (let ((a (fn-lbc-loc0 (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc)))
        (b (fn-lbc-loc1 (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc))))
   (and (fn-locp a b)
        (equal (fn-loc-segment a b) (fn-lb-log-model-row-segment row log))
        (equal (fn-loc-offset a b) (nth 3 (fn-lb-log-model-row-entry row log)))
        (equal (fn-loc-len a b) (nth 4 (fn-lb-log-model-row-entry row log))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-loc-accessors-of-make
          (seg (fn-lb-log-model-row-segment row log))
          (off (nth 3 (fn-lb-log-model-row-entry row log)))
          (len (nth 4 (fn-lb-log-model-row-entry row log)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-log-guardp fn-lbc-loc0-of-append-row-new fn-lbc-loc1-of-append-row-new)))))

(local (defthm fn-lbrlr-append-proper-tail
 (implies (true-listp b) (true-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append true-listp)))))

(local (defthm fn-lbrlr-prefix-proper
 (true-listp (fn-lb-xref-shift-prefix payload))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-xref-shift-prefix fn-lbrlr-append-proper-tail))))))

(local (defthm fn-lbrlr-fix-proper
 (implies (true-listp x) (equal (true-list-fix x) x))
 :hints (("Goal" :induct (true-list-fix x) :in-theory (enable true-list-fix true-listp)))))

(defthm fn-lbc-xref-shift-prefix-of-append-row-new
 (equal (fn-lbc-xref-shift-prefix (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc))
        (fn-lb-xref-shift-prefix (fn-lb-log-payload row log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-xref-shift-prefix fn-lbc-escape fn-lbc-escape-store-get-of-append-row-new
     fn-lbc-row-cell-extra-xref-body-prefix fn-lb-log-payload fn-lbrlr-prefix-proper
     fn-lbrlr-fix-proper car-cons cdr-cons (:executable-counterpart cdr)
     (:executable-counterpart true-list-fix))))))
