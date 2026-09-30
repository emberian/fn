; Selected backing metadata, not machine attestation or memory admission.
; Host observes immutable runtime constants at startup; the core decides
; compatibility. Logical stored lengths are not bounded by this backing type.
(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

(defconst *fn-srr-observed-limits*
 '(4611686018427387903 17592186044416 17592186044416))

(defun fn-srr-observed-limits-status (positive-fixnum dimension-limit total-limit)
 (declare (xargs :guard t))
 (if (and (equal positive-fixnum 4611686018427387903)
          (equal dimension-limit 17592186044416)
          (equal total-limit 17592186044416))
     :compatible :unavailable))

(defun fn-srr-backing-span-domain-p
 (start count end total capacity dimension-limit total-limit)
 (declare (xargs :guard t))
 (and (natp start) (natp count) (natp end) (natp total) (natp capacity)
      (natp dimension-limit) (natp total-limit)
      (< capacity dimension-limit) (< capacity total-limit)
      (<= total capacity) (<= start end) (<= end total)
      (equal (+ start count) end)))

(defun fn-srr-span-scalars-fit-p (start count end total capacity positive-fixnum)
 (declare (xargs :guard t))
 (and (<= (nfix start) (nfix positive-fixnum))
      (<= (nfix count) (nfix positive-fixnum))
      (<= (nfix end) (nfix positive-fixnum))
      (<= (nfix total) (nfix positive-fixnum))
      (<= (nfix capacity) (nfix positive-fixnum))
      (equal (- (nfix end) (nfix start)) (nfix count))))

(defthm fn-srr-compatible-backed-span-scalars-by-definition
 (implies
  (and (equal (fn-srr-observed-limits-status positive-fixnum dimension-limit total-limit)
              :compatible)
       (fn-srr-backing-span-domain-p
        start count end total capacity dimension-limit total-limit))
  (fn-srr-span-scalars-fit-p start count end total capacity positive-fixnum))
 :hints (("Goal" :in-theory (enable fn-srr-observed-limits-status
                                    fn-srr-backing-span-domain-p
                                    fn-srr-span-scalars-fit-p)))
 :rule-classes nil)
