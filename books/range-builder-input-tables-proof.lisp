; Loading an admitted overview leaves the field bank and pool well formed
; for the next builder step, including when the pending row is retried.
(in-package "ACL2")
(include-book "runs-overview-source-proof")
(local (include-book "runs-load-frame-proof"))
(local (include-book "runs-layout-id-proof"))

(local
 (defthmd fn2-range-builder-scalar-widths
   (implies (fn2-run-values-layoutp *fn2-overview-entry* row)
            (and (unsigned-byte-p 60 (car row)) (unsigned-byte-p 60 (cadr row))
                 (unsigned-byte-p 60 (caddr row)) (unsigned-byte-p 60 (cadddr row))
                 (unsigned-byte-p 32 (len (car (cddddr row))))))
   :hints (("Goal" :use ((:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 0) (id 'group))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 1) (id 'group-number))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 2) (id 'article))
                         (:instance fn2-run-layout-id-width (layout *fn2-overview-entry*) (values row) (i 3) (id 'position))
                         fn2-run-admitted-line-fits-source)
            :in-theory (e/d (nth) (fn2-run-values-layoutp len))))))

(defthmd fn2-range-builder-load-keeps-typed-tables
  (let* ((r (fn2-run-load-values *fn2-overview-entry* row base src sg at 9 0 1 f pool))
         (after (mv-nth 2 r)) (p (mv-nth 3 r)))
    (implies (and (fn2-run-values-layoutp *fn2-overview-entry* row)
                  (unsigned-byte-p 32 src) (unsigned-byte-p 60 sg) (unsigned-byte-p 32 at)
                  (natp base) (<= (+ 5 base) (fn2-fields-rows f)) (fn2-fieldsp f) (fn2-fields-wfp f)
                  (fn2-poolp pool) (fn2-pool-wfp pool))
             (and (fn2-fieldsp after) (fn2-fields-wfp after) (equal (fn2-fields-rows after) (fn2-fields-rows f))
                  (fn2-poolp p) (fn2-pool-wfp p))))
  :hints (("Goal" :do-not '(preprocess)
           :use fn2-range-builder-scalar-widths
           :in-theory (e/d (fn2-run-load-values fn2-run-load-ref)
                     (fn2-run-values-layoutp fn2-fields-rows fn2-fieldsp fn2-fields-wfp
                      fn2-fields-set-value fn2-fields-set-ref-slot fn2-fields-set-ref-gen fn2-fields-set-ref-off
                      fn2-fields-set-ref-len fn2-run-load-bytes fn2-poolp fn2-pool-wfp len)))))
