; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-msgid-prefix-readback")

(local (defthm fn-lbrorr-nfix-natural
 (natp (nfix x))
 :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbrorr-pointer-msgid
 (implies (fn-lb-column-row-pointerp i fn-lbc) (<= (+ (nfix (fn-lbc-value i :msgid-offset fn-lbc)) (nfix (fn-lbc-value i :msgid-length fn-lbc))) (fn-lbc-msgid-pool-count fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(local (defthm fn-lbrorr-pointer-original-nov
 (implies (fn-lb-column-row-pointerp i fn-lbc) (implies (and (not (fn-lbc-escape i :nov fn-lbc)) (not (equal (fn-lbc-directory-value i :nov-length fn-lbc) 0))) (and (natp (fn-lbc-directory-value i :nov-start fn-lbc)) (< (fn-lbc-directory-value i :nov-start fn-lbc) (fn-lbc-nov-record-count fn-lbc)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(local (defthm fn-lbrorr-pointer-render-nov
 (implies (fn-lb-column-row-pointerp i fn-lbc) (implies (not (fn-lbc-escape i :render-nov fn-lbc)) (and (natp (fn-lbc-directory-value i :render-nov-start fn-lbc)) (< (fn-lbc-directory-value i :render-nov-start fn-lbc) (fn-lbc-nov-record-count fn-lbc)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(local (defthm fn-lbrorr-pointer-groups
 (implies (fn-lb-column-row-pointerp i fn-lbc) (implies (not (fn-lbc-escape i :groups fn-lbc)) (<= (+ (nfix (fn-lbc-directory-value i :groups-start fn-lbc)) (nfix (fn-lbc-directory-value i :groups-count fn-lbc))) (fn-lbc-membership-record-count fn-lbc))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(local (defthm fn-lbrorr-pointer-numbers
 (implies (fn-lb-column-row-pointerp i fn-lbc) (implies (not (fn-lbc-escape i :numbers fn-lbc)) (<= (+ (nfix (fn-lbc-directory-value i :numbers-start fn-lbc)) (nfix (fn-lbc-directory-value i :numbers-count fn-lbc))) (fn-lbc-membership-record-count fn-lbc))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-column-row-pointerp))))))

(defthm fn-lbc-msgid-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc)
               (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-column-row-pointerp i fn-lbc))
  (equal (fn-lbc-msgid i (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-msgid i fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbrorr-pointer-msgid)) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-msgid fn-lbc-escape-of-append-row-old fn-lbc-value-of-append-row-old fn-lbc-directory-value-of-append-row-old fn-lbc-nov-at-of-append-row-prefix fn-lbc-membership-run-of-append-row-prefix fn-lbc-msgid-pool-range-of-append-row-prefix fn-lbrorr-nfix-natural (:type-prescription nfix))))))

(defthm fn-lbc-original-nov-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc)
               (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-column-row-pointerp i fn-lbc))
  (equal (fn-lbc-original-nov i (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-original-nov i fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbrorr-pointer-original-nov)) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov fn-lbc-escape-of-append-row-old fn-lbc-value-of-append-row-old fn-lbc-directory-value-of-append-row-old fn-lbc-nov-at-of-append-row-prefix fn-lbc-membership-run-of-append-row-prefix fn-lbc-msgid-pool-range-of-append-row-prefix fn-lbrorr-nfix-natural (:type-prescription nfix))))))

(defthm fn-lbc-render-nov-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc)
               (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-column-row-pointerp i fn-lbc))
  (equal (fn-lbc-render-nov i (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-render-nov i fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbrorr-pointer-render-nov)) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-render-nov fn-lbc-escape-of-append-row-old fn-lbc-value-of-append-row-old fn-lbc-directory-value-of-append-row-old fn-lbc-nov-at-of-append-row-prefix fn-lbc-membership-run-of-append-row-prefix fn-lbc-msgid-pool-range-of-append-row-prefix fn-lbrorr-nfix-natural (:type-prescription nfix))))))

(defthm fn-lbc-groups-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc)
               (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-column-row-pointerp i fn-lbc))
  (equal (fn-lbc-groups i (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-groups i fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbrorr-pointer-groups)) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-groups fn-lbc-escape-of-append-row-old fn-lbc-value-of-append-row-old fn-lbc-directory-value-of-append-row-old fn-lbc-nov-at-of-append-row-prefix fn-lbc-membership-run-of-append-row-prefix fn-lbc-msgid-pool-range-of-append-row-prefix fn-lbrorr-nfix-natural (:type-prescription nfix))))))

(defthm fn-lbc-numbers-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc)
               (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-column-row-pointerp i fn-lbc))
  (equal (fn-lbc-numbers i (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-numbers i fn-lbc)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbrorr-pointer-numbers)) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-numbers fn-lbc-escape-of-append-row-old fn-lbc-value-of-append-row-old fn-lbc-directory-value-of-append-row-old fn-lbc-nov-at-of-append-row-prefix fn-lbc-membership-run-of-append-row-prefix fn-lbc-msgid-pool-range-of-append-row-prefix fn-lbrorr-nfix-natural (:type-prescription nfix))))))

(defthm fn-lbc-served-row-of-append-row-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lb-columns-directory-alignedp fn-lbc)
               (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-column-row-pointerp i fn-lbc))
  (equal (fn-lbc-served-row i (fn-lbc-append-row row log fn-lbc))
         (fn-lbc-served-row i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-served-row fn-lbc-msgid-of-append-row-old fn-lbc-value-of-append-row-old fn-lbc-groups-of-append-row-old fn-lbc-numbers-of-append-row-old fn-lbc-withdrawn-of-append-row-old fn-lbc-directory-value-of-append-row-old fn-lbc-original-nov-of-append-row-old)))))
