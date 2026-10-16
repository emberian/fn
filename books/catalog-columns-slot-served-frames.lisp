; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-array-frames")

(local (defthm fn-lbsvf-nfix-natural
 (natp (nfix x)) :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-lbc-msgid-of-slot-put
 (equal (fn-lbc-msgid i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-msgid i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-msgid fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field fn-lbc-escape-of-slot-put-other-key fn-lbc-nov-at-of-slot-put fn-lbc-membership-run-of-slot-put fn-lbc-msgid-pool-range-of-slot-put fn-lbc-bit-2-of-slot-put fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-original-nov-of-slot-put
 (equal (fn-lbc-original-nov i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-original-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field fn-lbc-escape-of-slot-put-other-key fn-lbc-nov-at-of-slot-put fn-lbc-membership-run-of-slot-put fn-lbc-msgid-pool-range-of-slot-put fn-lbc-bit-2-of-slot-put fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-render-nov-of-slot-put
 (equal (fn-lbc-render-nov i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-render-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-render-nov fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field fn-lbc-escape-of-slot-put-other-key fn-lbc-nov-at-of-slot-put fn-lbc-membership-run-of-slot-put fn-lbc-msgid-pool-range-of-slot-put fn-lbc-bit-2-of-slot-put fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-groups-of-slot-put
 (equal (fn-lbc-groups i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-groups i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-groups fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field fn-lbc-escape-of-slot-put-other-key fn-lbc-nov-at-of-slot-put fn-lbc-membership-run-of-slot-put fn-lbc-msgid-pool-range-of-slot-put fn-lbc-bit-2-of-slot-put fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-numbers-of-slot-put
 (equal (fn-lbc-numbers i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-numbers i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-numbers fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field fn-lbc-escape-of-slot-put-other-key fn-lbc-nov-at-of-slot-put fn-lbc-membership-run-of-slot-put fn-lbc-msgid-pool-range-of-slot-put fn-lbc-bit-2-of-slot-put fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-xref-shift-prefix-of-slot-put
 (equal (fn-lbc-xref-shift-prefix i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-xref-shift-prefix i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-xref-shift-prefix fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field fn-lbc-escape-of-slot-put-other-key fn-lbc-nov-at-of-slot-put fn-lbc-membership-run-of-slot-put fn-lbc-msgid-pool-range-of-slot-put fn-lbc-bit-2-of-slot-put fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-withdrawn-of-slot-put
 (implies (fn-lbc-p fn-lbc) (equal (fn-lbc-withdrawn i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-withdrawn i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field fn-lbc-escape-of-slot-put-other-key fn-lbc-nov-at-of-slot-put fn-lbc-membership-run-of-slot-put fn-lbc-msgid-pool-range-of-slot-put fn-lbc-bit-2-of-slot-put fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-served-row-of-slot-put
 (implies (fn-lbc-p fn-lbc) (equal (fn-lbc-served-row i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-served-row i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-served-row fn-lbc-value-of-slot-put-other-field fn-lbc-directory-value-of-slot-put-other-field fn-lbc-escape-of-slot-put-other-key fn-lbc-nov-at-of-slot-put fn-lbc-membership-run-of-slot-put fn-lbc-msgid-pool-range-of-slot-put fn-lbc-bit-2-of-slot-put fn-lbsvf-nfix-natural (:executable-counterpart equal) fn-lbc-msgid-of-slot-put fn-lbc-original-nov-of-slot-put fn-lbc-render-nov-of-slot-put fn-lbc-groups-of-slot-put fn-lbc-numbers-of-slot-put fn-lbc-xref-shift-prefix-of-slot-put fn-lbc-withdrawn-of-slot-put)))))

(defthm fn-lbc-msgid-of-slot-insert
 (equal (fn-lbc-msgid i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-msgid i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-msgid fn-lbc-value-of-slot-insert-other-field fn-lbc-directory-value-of-slot-insert-other-field fn-lbc-escape-of-slot-insert-other-key fn-lbc-nov-at-of-slot-insert fn-lbc-membership-run-of-slot-insert fn-lbc-msgid-pool-range-of-slot-insert fn-lbc-bit-2-of-slot-insert fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-original-nov-of-slot-insert
 (equal (fn-lbc-original-nov i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-original-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov fn-lbc-value-of-slot-insert-other-field fn-lbc-directory-value-of-slot-insert-other-field fn-lbc-escape-of-slot-insert-other-key fn-lbc-nov-at-of-slot-insert fn-lbc-membership-run-of-slot-insert fn-lbc-msgid-pool-range-of-slot-insert fn-lbc-bit-2-of-slot-insert fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-render-nov-of-slot-insert
 (equal (fn-lbc-render-nov i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-render-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-render-nov fn-lbc-value-of-slot-insert-other-field fn-lbc-directory-value-of-slot-insert-other-field fn-lbc-escape-of-slot-insert-other-key fn-lbc-nov-at-of-slot-insert fn-lbc-membership-run-of-slot-insert fn-lbc-msgid-pool-range-of-slot-insert fn-lbc-bit-2-of-slot-insert fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-groups-of-slot-insert
 (equal (fn-lbc-groups i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-groups i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-groups fn-lbc-value-of-slot-insert-other-field fn-lbc-directory-value-of-slot-insert-other-field fn-lbc-escape-of-slot-insert-other-key fn-lbc-nov-at-of-slot-insert fn-lbc-membership-run-of-slot-insert fn-lbc-msgid-pool-range-of-slot-insert fn-lbc-bit-2-of-slot-insert fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-numbers-of-slot-insert
 (equal (fn-lbc-numbers i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-numbers i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-numbers fn-lbc-value-of-slot-insert-other-field fn-lbc-directory-value-of-slot-insert-other-field fn-lbc-escape-of-slot-insert-other-key fn-lbc-nov-at-of-slot-insert fn-lbc-membership-run-of-slot-insert fn-lbc-msgid-pool-range-of-slot-insert fn-lbc-bit-2-of-slot-insert fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-xref-shift-prefix-of-slot-insert
 (equal (fn-lbc-xref-shift-prefix i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-xref-shift-prefix i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-xref-shift-prefix fn-lbc-value-of-slot-insert-other-field fn-lbc-directory-value-of-slot-insert-other-field fn-lbc-escape-of-slot-insert-other-key fn-lbc-nov-at-of-slot-insert fn-lbc-membership-run-of-slot-insert fn-lbc-msgid-pool-range-of-slot-insert fn-lbc-bit-2-of-slot-insert fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-withdrawn-of-slot-insert
 (implies (fn-lbc-p fn-lbc) (equal (fn-lbc-withdrawn i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-withdrawn i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn fn-lbc-value-of-slot-insert-other-field fn-lbc-directory-value-of-slot-insert-other-field fn-lbc-escape-of-slot-insert-other-key fn-lbc-nov-at-of-slot-insert fn-lbc-membership-run-of-slot-insert fn-lbc-msgid-pool-range-of-slot-insert fn-lbc-bit-2-of-slot-insert fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-served-row-of-slot-insert
 (implies (fn-lbc-p fn-lbc) (equal (fn-lbc-served-row i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-served-row i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-served-row fn-lbc-value-of-slot-insert-other-field fn-lbc-directory-value-of-slot-insert-other-field fn-lbc-escape-of-slot-insert-other-key fn-lbc-nov-at-of-slot-insert fn-lbc-membership-run-of-slot-insert fn-lbc-msgid-pool-range-of-slot-insert fn-lbc-bit-2-of-slot-insert fn-lbsvf-nfix-natural (:executable-counterpart equal) fn-lbc-msgid-of-slot-insert fn-lbc-original-nov-of-slot-insert fn-lbc-render-nov-of-slot-insert fn-lbc-groups-of-slot-insert fn-lbc-numbers-of-slot-insert fn-lbc-xref-shift-prefix-of-slot-insert fn-lbc-withdrawn-of-slot-insert)))))

(defthm fn-lbc-msgid-of-index-slots
 (equal (fn-lbc-msgid i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-msgid i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-msgid fn-lbc-value-of-index-slots-other-field fn-lbc-directory-value-of-index-slots-other-field fn-lbc-escape-of-index-slots-other-key fn-lbc-nov-at-of-index-slots fn-lbc-membership-run-of-index-slots fn-lbc-msgid-pool-range-of-index-slots fn-lbc-bit-2-of-index-slots fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-original-nov-of-index-slots
 (equal (fn-lbc-original-nov i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-original-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov fn-lbc-value-of-index-slots-other-field fn-lbc-directory-value-of-index-slots-other-field fn-lbc-escape-of-index-slots-other-key fn-lbc-nov-at-of-index-slots fn-lbc-membership-run-of-index-slots fn-lbc-msgid-pool-range-of-index-slots fn-lbc-bit-2-of-index-slots fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-render-nov-of-index-slots
 (equal (fn-lbc-render-nov i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-render-nov i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-render-nov fn-lbc-value-of-index-slots-other-field fn-lbc-directory-value-of-index-slots-other-field fn-lbc-escape-of-index-slots-other-key fn-lbc-nov-at-of-index-slots fn-lbc-membership-run-of-index-slots fn-lbc-msgid-pool-range-of-index-slots fn-lbc-bit-2-of-index-slots fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-groups-of-index-slots
 (equal (fn-lbc-groups i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-groups i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-groups fn-lbc-value-of-index-slots-other-field fn-lbc-directory-value-of-index-slots-other-field fn-lbc-escape-of-index-slots-other-key fn-lbc-nov-at-of-index-slots fn-lbc-membership-run-of-index-slots fn-lbc-msgid-pool-range-of-index-slots fn-lbc-bit-2-of-index-slots fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-numbers-of-index-slots
 (equal (fn-lbc-numbers i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-numbers i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-numbers fn-lbc-value-of-index-slots-other-field fn-lbc-directory-value-of-index-slots-other-field fn-lbc-escape-of-index-slots-other-key fn-lbc-nov-at-of-index-slots fn-lbc-membership-run-of-index-slots fn-lbc-msgid-pool-range-of-index-slots fn-lbc-bit-2-of-index-slots fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-xref-shift-prefix-of-index-slots
 (equal (fn-lbc-xref-shift-prefix i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-xref-shift-prefix i fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-xref-shift-prefix fn-lbc-value-of-index-slots-other-field fn-lbc-directory-value-of-index-slots-other-field fn-lbc-escape-of-index-slots-other-key fn-lbc-nov-at-of-index-slots fn-lbc-membership-run-of-index-slots fn-lbc-msgid-pool-range-of-index-slots fn-lbc-bit-2-of-index-slots fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-withdrawn-of-index-slots
 (implies (fn-lbc-p fn-lbc) (equal (fn-lbc-withdrawn i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-withdrawn i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn fn-lbc-value-of-index-slots-other-field fn-lbc-directory-value-of-index-slots-other-field fn-lbc-escape-of-index-slots-other-key fn-lbc-nov-at-of-index-slots fn-lbc-membership-run-of-index-slots fn-lbc-msgid-pool-range-of-index-slots fn-lbc-bit-2-of-index-slots fn-lbsvf-nfix-natural (:executable-counterpart equal))))))

(defthm fn-lbc-served-row-of-index-slots
 (implies (fn-lbc-p fn-lbc) (equal (fn-lbc-served-row i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-served-row i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-served-row fn-lbc-value-of-index-slots-other-field fn-lbc-directory-value-of-index-slots-other-field fn-lbc-escape-of-index-slots-other-key fn-lbc-nov-at-of-index-slots fn-lbc-membership-run-of-index-slots fn-lbc-msgid-pool-range-of-index-slots fn-lbc-bit-2-of-index-slots fn-lbsvf-nfix-natural (:executable-counterpart equal) fn-lbc-msgid-of-index-slots fn-lbc-original-nov-of-index-slots fn-lbc-render-nov-of-index-slots fn-lbc-groups-of-index-slots fn-lbc-numbers-of-index-slots fn-lbc-xref-shift-prefix-of-index-slots fn-lbc-withdrawn-of-index-slots)))))
