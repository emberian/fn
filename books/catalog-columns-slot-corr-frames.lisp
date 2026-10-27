; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-served-frames")

(defthm fn-lbc-loc0-of-slot-put-in-bounds
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc0 i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-loc0-is-word-by-definition fn-lbc-count-of-slot-put
     fn-lbc-word-of-slot-put-other-field (:executable-counterpart equal))))))

(defthm fn-lbc-loc1-of-slot-put-in-bounds
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc1 i (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-loc1-is-word-by-definition fn-lbc-count-of-slot-put
     fn-lbc-word-of-slot-put-other-field (:executable-counterpart equal))))))

(defthm fn-lbc-home-entry-of-slot-put
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-home-entry i (fn-lbc-slot-put slot ordinal fn-lbc) log) (fn-lbc-home-entry i fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-home-entry fn-lbc-loc0-of-slot-put-in-bounds fn-lbc-loc1-of-slot-put-in-bounds)))))

(defthm fn-lbc-row-corr-of-slot-put
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-row-corr i row prefix-max (fn-lbc-slot-put slot ordinal fn-lbc) log)
         (fn-lbc-row-corr i row prefix-max fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-corr fn-lbc-home-entry-of-slot-put
     fn-lbc-loc0-of-slot-put-in-bounds fn-lbc-loc1-of-slot-put-in-bounds
     fn-lbc-served-row-of-slot-put fn-lbc-value-of-slot-put-other-field
     fn-lbc-word-of-slot-put-other-field fn-lbc-bit-4-of-slot-put fn-lbc-bit-5-of-slot-put
     fn-lbc-xref-shift-prefix-of-slot-put fn-lbc-directory-value-of-slot-put-other-field
     fn-lbc-render-nov-of-slot-put (:executable-counterpart equal))))))

(defthm fn-lbc-loc0-of-slot-insert-in-bounds
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc0 i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-loc0-is-word-by-definition fn-lbc-count-of-slot-insert
     fn-lbc-word-of-slot-insert-other-field (:executable-counterpart equal))))))

(defthm fn-lbc-loc1-of-slot-insert-in-bounds
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc1 i (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-loc1-is-word-by-definition fn-lbc-count-of-slot-insert
     fn-lbc-word-of-slot-insert-other-field (:executable-counterpart equal))))))

(defthm fn-lbc-home-entry-of-slot-insert
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-home-entry i (fn-lbc-slot-insert j slot fuel fn-lbc) log) (fn-lbc-home-entry i fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-home-entry fn-lbc-loc0-of-slot-insert-in-bounds fn-lbc-loc1-of-slot-insert-in-bounds)))))

(defthm fn-lbc-row-corr-of-slot-insert
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-row-corr i row prefix-max (fn-lbc-slot-insert j slot fuel fn-lbc) log)
         (fn-lbc-row-corr i row prefix-max fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-corr fn-lbc-home-entry-of-slot-insert
     fn-lbc-loc0-of-slot-insert-in-bounds fn-lbc-loc1-of-slot-insert-in-bounds
     fn-lbc-served-row-of-slot-insert fn-lbc-value-of-slot-insert-other-field
     fn-lbc-word-of-slot-insert-other-field fn-lbc-bit-4-of-slot-insert fn-lbc-bit-5-of-slot-insert
     fn-lbc-xref-shift-prefix-of-slot-insert fn-lbc-directory-value-of-slot-insert-other-field
     fn-lbc-render-nov-of-slot-insert (:executable-counterpart equal))))))

(defthm fn-lbc-loc0-of-index-slots-in-bounds
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc0 i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-loc0-is-word-by-definition fn-lbc-count-of-index-slots
     fn-lbc-word-of-index-slots-other-field (:executable-counterpart equal))))))

(defthm fn-lbc-loc1-of-index-slots-in-bounds
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc1 i (fn-lbc-index-slots j n fn-lbc)) (fn-lbc-loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-loc1-is-word-by-definition fn-lbc-count-of-index-slots
     fn-lbc-word-of-index-slots-other-field (:executable-counterpart equal))))))

(defthm fn-lbc-home-entry-of-index-slots
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-home-entry i (fn-lbc-index-slots j n fn-lbc) log) (fn-lbc-home-entry i fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-home-entry fn-lbc-loc0-of-index-slots-in-bounds fn-lbc-loc1-of-index-slots-in-bounds)))))

(defthm fn-lbc-row-corr-of-index-slots
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-row-corr i row prefix-max (fn-lbc-index-slots j n fn-lbc) log)
         (fn-lbc-row-corr i row prefix-max fn-lbc log)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-row-corr fn-lbc-home-entry-of-index-slots
     fn-lbc-loc0-of-index-slots-in-bounds fn-lbc-loc1-of-index-slots-in-bounds
     fn-lbc-served-row-of-index-slots fn-lbc-value-of-index-slots-other-field
     fn-lbc-word-of-index-slots-other-field fn-lbc-bit-4-of-index-slots fn-lbc-bit-5-of-index-slots
     fn-lbc-xref-shift-prefix-of-index-slots fn-lbc-directory-value-of-index-slots-other-field
     fn-lbc-render-nov-of-index-slots (:executable-counterpart equal))))))
