; The served overview cutoff tests the upper key and the position limit on the delivered row.
(in-package "ACL2")
(include-book "range-served")
(include-book "range-seek-scan-proof")

(defun-nx fn2-overview-range-key-at (base f)
 (list (fn2-fields-value base f) (fn2-fields-value (+ 1 base) f)))

(defthm fn2-overview-layout-compare-keys
 (implies (and (natp a) (natp b))
          (equal (fn2-run-layout-compare 3 a b ak as ag bk bs bg f pool)
                 (list :ok (fn2-run-key-order-spec *fn2-overview-range-key*
                             (fn2-overview-range-key-at a f) (fn2-overview-range-key-at b f)))))
 :hints (("Goal" :in-theory (e/d (fn2-run-layout-compare fn2-overview-compare fn2-overview-compare-1)
                                 (fn2-fields-value nfix)))))

(local
 (defthm fn2-overview-unloaded-position
   (implies (and (natp base) (natp pf) (< pf 5))
            (equal (nfix (nth pf (fn2-run-unload-values *fn2-overview-entry* base f pool)))
                   (if (equal pf 4) 0 (nfix (fn2-fields-value (+ base pf) f)))))
   :hints (("Goal" :cases ((equal pf 0) (equal pf 1) (equal pf 2) (equal pf 3) (equal pf 4))
            :in-theory (disable fn2-fields-value fn2-run-read-bytes fn2-fields-ref-len
                                fn2-fields-ref-slot fn2-fields-ref-off fn2-fields-ref-gen)))))


(local
 (defthm fn2-overview-compare-unloaded-key
  (implies (natp eb)
   (equal (fn2-run-key-order-spec *fn2-overview-range-key* (fn2-run-unload-values *fn2-overview-entry* eb f pool) hi)
          (fn2-run-key-order-spec *fn2-overview-range-key* (fn2-overview-range-key-at eb f) hi)))
  :hints (("Goal" :in-theory (disable nfix fn2-fields-value fn2-run-read-bytes fn2-fields-ref-len
                                     fn2-fields-ref-slot fn2-fields-ref-off fn2-fields-ref-gen)))))

(local
 (defthm fn2-overview-order-reflexive
  (equal (fn2-run-key-order-spec *fn2-overview-range-key* key key) :eq)
  :hints (("Goal" :in-theory (disable nfix)))))

(local (defthm fn2-overview-natural-limit
 (implies (natp x) (equal (nfix x) x))))

(defthm fn2-overview-range-window-cutoff
 (let* ((hi-base (fn2-ranges-hbase g r))
        (hi (fn2-overview-range-key-at hi-base f))
        (key (fn2-overview-range-key-at eb f))
        (pf (fn2-ranges-pfield g r))
        (pidx (if (equal pf *fn2-range-no-position*) nil pf))
        (entry (fn2-run-unload-values *fn2-overview-entry* eb f pool))
        (limit (fn2-ranges-plimit g r)))
   (implies (and (natp g) (< g (fn2-ranges-rows r)) (equal (fn2-ranges-schema g r) 3)
                 (natp eb) (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
                 (natp hi-base) (<= (+ hi-base *fn2-run-entry-rows*) (fn2-fields-rows f))
                 (or (equal pf *fn2-range-no-position*) (and (natp pf) (< pf 5)))
                 (natp limit)
                 (implies (equal pf 4) (equal (fn2-fields-value (+ eb 4) f) 0)))
            (equal (fn2-range-past g eb ok os og r f pool)
                   (list :ok (endp (fn2-range-window-spec *fn2-overview-range-key*
                                           (list entry) key hi pidx limit))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-range-past)
                 (fn2-run-layout-compare fn2-run-key-order-spec fn2-overview-range-key-at fn2-run-unload-values
                  fn2-fields-value fn2-fields-rows fn2-ranges-hbase fn2-ranges-rows
                  fn2-ranges-plimit fn2-ranges-pfield fn2-ranges-schema nth nfix)))))
