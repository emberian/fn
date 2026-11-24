; The successor writes the query rows. The delivered entry and its octet
; references can still be unloaded after those writes.
(in-package "ACL2")
(include-book "range-served")

(local
 (defthm fn2-range-unload-after-store
   (implies (and (natp i) (natp row) (< i row))
            (equal (fn2-run-unload-values layout row (fn2-layout-store i v slot gen off size st f) pool)
                   (fn2-run-unload-values layout row f pool)))
   :hints (("Goal" :induct (fn2-run-unload-values layout row f pool)
            :in-theory (e/d (fn2-run-unload-values fn2-layout-store nth-update-nth)
                            (nth update-nth unsigned-byte-p fn2-fields-rows fn2-run-read-bytes))))))

(local
 (defthm fn2-range-unload-after-value
   (implies (and (natp i) (natp row) (< i row))
            (equal (fn2-run-unload-values layout row (fn2-fields-set-value i v f) pool)
                   (fn2-run-unload-values layout row f pool)))
   :hints (("Goal" :induct (fn2-run-unload-values layout row f pool)
            :in-theory (e/d (fn2-run-unload-values fn2-fields-set-value update-fn2-fields-value$ai nth-update-nth)
                            (nth update-nth fn2-run-read-bytes))))))

(local
 (defthm fn2-range-unload-after-copy-row
   (implies (and (natp dst) (natp row) (< dst row))
            (equal (fn2-run-unload-values layout row (fn2-run-copy-row src dst f) pool)
                   (fn2-run-unload-values layout row f pool)))
   :hints (("Goal" :in-theory (e/d (fn2-run-copy-row) (fn2-run-unload-values fn2-layout-store))))))

(local
 (defthm fn2-range-unload-after-copy
   (implies (and (natp n) (natp dst) (natp row) (<= (+ dst n) row))
            (equal (fn2-run-unload-values layout row (mv-nth 1 (fn2-range-copy-rows n src dst f)) pool)
                   (fn2-run-unload-values layout row f pool)))
   :hints (("Goal" :induct (fn2-range-copy-rows n src dst f)
            :in-theory (e/d (fn2-range-copy-rows) (fn2-run-unload-values fn2-run-copy-row fn2-fields-rows))))))

(local
 (defthm fn2-range-unload-after-carry
   (implies (and (natp n) (natp dst) (natp row) (<= (+ dst n) row))
            (equal (fn2-run-unload-values layout row (mv-nth 1 (fn2-range-carry n dst f)) pool)
                   (fn2-run-unload-values layout row f pool)))
   :hints (("Goal" :induct (fn2-range-carry n dst f)
            :in-theory (e/d (fn2-range-carry)
                            (fn2-run-unload-values fn2-fields-set-value fn2-fields-rows fn2-fields-value unsigned-byte-p))))))

(defthmd fn2-overview-successor-preserves-delivered-row
  (implies (and (natp qb) (natp eb) (<= (+ qb 2) eb))
           (equal (fn2-run-unload-values layout eb (mv-nth 1 (fn2-range-successor 3 eb qb f)) pool)
                  (fn2-run-unload-values layout eb f pool)))
  :hints (("Goal" :in-theory (e/d (fn2-range-successor)
                                  (fn2-range-copy-rows fn2-range-carry fn2-fields-rows fn2-run-unload-values)))))
