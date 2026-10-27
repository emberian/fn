; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-row-source")

(local (defthm fn-lbrca-pointer-step
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lb-columns-row-pointersp i fn-lbc))
 (and (fn-lb-column-row-pointerp i fn-lbc) (fn-lb-columns-row-pointersp (+ 1 i) fn-lbc)))
 :hints (("Goal" :expand ((fn-lb-columns-row-pointersp i fn-lbc))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbrca-len-cons
 (implies (consp xs) (equal (len xs) (+ 1 (len (cdr xs)))))
 :hints (("Goal" :in-theory (enable len)))))

(defthm fn-lbc-rows-corr-of-append-row-old
 (implies (and (natp i) (<= (+ i (len rows)) (fn-lbc-count fn-lbc))
 (fn-lb-columns-row-pointersp i fn-lbc) (fn-lb-columns-directory-alignedp fn-lbc)
 (fn-lb-columns-pool-layoutp fn-lbc))
 (equal (fn-lbc-rows-corr i rows prefix-max (fn-lbc-append-row added-row log fn-lbc) log)
        (fn-lbc-rows-corr i rows prefix-max fn-lbc log)))
 :hints (("Goal" :induct (fn-lbc-rows-corr i rows prefix-max fn-lbc log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rows-corr fn-lbc-row-corr-of-append-row-old fn-lbrca-pointer-step fn-lbrca-len-cons)))))
