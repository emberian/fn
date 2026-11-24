; The packing test used by the range builder accepts every admitted row
; on an empty leaf and every group of sixteen admitted index entries.
(in-package "ACL2")
(include-book "runs-page-row-budget-proof")

(local
 (defthm fn2-range-index-row-bytes
   (implies (fn2-run-values-layoutp *fn2-overview-index* row)
            (<= (len (fn2-layout-octets *fn2-overview-index* row)) 106))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn2-run-overview-admission-fits-decoder (layout *fn2-overview-index*)))
            :in-theory (disable fn2-run-values-layoutp fn2-layout-octets len)))))

(local (defthm fn2-range-index-octet-count-of-append
         (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn2-range-index-body-bytes
   (implies (fn2-run-entries-layoutp *fn2-overview-index* rows)
            (<= (len (fn2-run-entries-octets *fn2-overview-index* rows)) (* 106 (len rows))))
   :rule-classes :linear
   :hints (("Goal" :induct (len rows)
            :in-theory (e/d (fn2-run-entries-layoutp fn2-run-entries-octets)
                            (fn2-run-values-layoutp fn2-layout-octets))))))

(local
 (defthm fn2-range-directory-has-at-most-one-offset-per-row
   (<= (len (fn2-run-restart-offsets-spec layout rows i off)) (len rows))
   :rule-classes :linear
   :hints (("Goal" :induct (fn2-run-restart-offsets-spec layout rows i off)
            :in-theory (e/d (fn2-run-restart-offsets-spec) (fn2-layout-octets mod))))))

(defthmd fn2-range-empty-leaf-fits-admitted-row
  (implies (fn2-run-values-layoutp *fn2-overview-entry* row)
           (car (fn2-run-pack-bound (len (fn2-layout-octets *fn2-overview-entry* row)) *fn2-run-entries-base* 0 0 2048)))
  :hints (("Goal" :use ((:instance fn2-run-overview-admission-fits-decoder (layout *fn2-overview-entry*)))
           :in-theory (e/d (fn2-run-pack-bound) (fn2-run-values-layoutp fn2-layout-octets len)))))

(defthmd fn2-range-index-fits-sixteen-children
  (let ((body (fn2-run-entries-octets *fn2-overview-index* rows))
        (offsets (fn2-run-restart-offsets-spec *fn2-overview-index* rows 0 *fn2-run-entries-base*)))
    (implies (and (fn2-run-entries-layoutp *fn2-overview-index* rows) (< (len rows) 16)
                  (fn2-run-values-layoutp *fn2-overview-index* row))
             (car (fn2-run-pack-bound (len (fn2-layout-octets *fn2-overview-index* row))
                        (+ *fn2-run-entries-base* (len body)) (len rows) (len offsets) 2048))))
  :hints (("Goal" :in-theory (e/d (fn2-run-pack-bound)
                            (fn2-run-entries-octets fn2-run-restart-offsets-spec fn2-run-entries-layoutp
                             fn2-run-values-layoutp fn2-layout-octets len mod)))))
