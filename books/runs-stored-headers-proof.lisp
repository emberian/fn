; Both physical header reads establish the entry count, restart count and
; beginning of the directory that bound the cursor's page search.
(in-package "ACL2")
(include-book "runs-stored-header-fields-proof")
(include-book "runs-page")

(defun-nx fn2-run-page-headers-p (bvals cvals dir count nr slot gen pk ps pg pool)
  (and (fn2-run-stored-header-p *fn2-format-page-header* bvals slot gen 0 *fn2-run-header-area* pk ps pg pool)
       (fn2-run-stored-header-p *fn2-run-page-header* cvals slot gen *fn2-run-header-area* *fn2-run-entries-base* pk ps pg pool)
       (equal (nth *fn2-format-page-header-field-magic* bvals) *fn2-format-page-magic*)
       (equal (nth *fn2-format-page-header-field-header-length* bvals) *fn2-run-header-area*)
       (equal (nth *fn2-format-page-header-field-payload-length* bvals)
              (- (+ dir (* *fn2-run-restart-bytes* nr)) *fn2-run-header-area*))
       (equal (nth *fn2-run-page-header-field-entries* cvals) count)
       (equal (nth *fn2-run-page-header-field-restarts* cvals) nr)
       (equal (nth *fn2-run-page-header-field-restart-interval* cvals) *fn2-run-restart-interval*)
       (natp dir) (<= *fn2-run-entries-base* dir)
       (natp count) (equal nr (ceiling count *fn2-run-restart-interval*))
       (<= (+ dir (* *fn2-run-restart-bytes* nr)) *fn2-run-page-size*)))

(local
 (defthm fn2-run-reads-two-header-fields
   (let* ((b (fn2-format-page-header-decode rb slot gen 0 *fn2-run-header-area* pk ps pg f pool))
          (base (+ rb *fn2-run-c-header-fields*))
          (c (fn2-run-page-header-decode base slot gen *fn2-run-header-area* *fn2-run-entries-base* pk ps pg (mv-nth 2 b) pool)))
     (implies (and (fn2-run-page-headers-p bvals cvals dir count nr slot gen pk ps pg pool)
                   (natp rb) (natp watch) (< watch (+ base *fn2-run-page-header-num-fields*))
                   (<= (+ base *fn2-run-page-header-num-fields*) (fn2-fields-rows f)))
              (and (equal (car b) :ok) (equal (car c) :ok)
                   (equal (fn2-fields-value watch (mv-nth 2 c))
                          (cond ((< watch rb) (fn2-fields-value watch f))
                                ((< watch base) (nth (- watch rb) bvals))
                                (t (nth (- watch base) cvals)))))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-format-page-header-reads-stored-field (base rb) (vals bvals) (watch rb)
                             (off 0) (end *fn2-run-header-area*))
                  (:instance fn2-format-page-header-reads-stored-field (base rb) (vals bvals)
                             (off 0) (end *fn2-run-header-area*))
                  (:instance fn2-run-page-header-reads-stored-field (base (+ rb *fn2-run-c-header-fields*)) (vals cvals)
                             (off *fn2-run-header-area*) (end *fn2-run-entries-base*)
                             (f (mv-nth 2 (fn2-format-page-header-decode rb slot gen 0 *fn2-run-header-area* pk ps pg f pool)))))
            :in-theory (e/d (fn2-run-page-headers-p)
                      (fn2-run-stored-header-p fn2-format-page-header-decode fn2-run-page-header-decode
                       fn2-fields-value fn2-fields-rows fn2-layout-octets nth len ceiling))))))

(local
 (defthm fn2-run-stored-header-metadata
   (implies (fn2-run-page-headers-p bvals cvals dir count nr slot gen pk ps pg pool)
            (and (equal (nth *fn2-format-page-header-field-magic* bvals) *fn2-format-page-magic*)
                 (equal (nth *fn2-format-page-header-field-header-length* bvals) *fn2-run-header-area*)
                 (equal (nth *fn2-format-page-header-field-payload-length* bvals)
                        (- (+ dir (* *fn2-run-restart-bytes* nr)) *fn2-run-header-area*))
                 (equal (nth *fn2-run-page-header-field-entries* cvals) count)
                 (equal (nth *fn2-run-page-header-field-restarts* cvals) nr)
                 (equal (nth *fn2-run-page-header-field-restart-interval* cvals) *fn2-run-restart-interval*)
                 (natp dir) (<= *fn2-run-entries-base* dir) (natp nr) (natp count)
                 (equal nr (ceiling count *fn2-run-restart-interval*))
                 (<= (+ dir (* *fn2-run-restart-bytes* nr)) *fn2-run-page-size*)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-page-headers-p) (fn2-run-stored-header-p nth))))))

(local
 (defthm fn2-run-decoded-header-codes
   (let* ((b (fn2-format-page-header-decode rb slot gen 0 *fn2-run-header-area* pk ps pg f pool))
          (c (fn2-run-page-header-decode (+ *fn2-run-c-header-fields* rb) slot gen *fn2-run-header-area*
                  *fn2-run-entries-base* pk ps pg (mv-nth 2 b) pool)))
     (implies (and (fn2-run-page-headers-p bvals cvals dir count nr slot gen pk ps pg pool)
                   (natp rb) (<= (+ rb *fn2-run-reader-restart*) (fn2-fields-rows f)))
              (and (equal (car b) :ok) (equal (car c) :ok))))
   :hints (("Goal" :use ((:instance fn2-run-reads-two-header-fields (watch rb)))
            :in-theory (disable fn2-run-page-headers-p fn2-format-page-header-decode fn2-run-page-header-decode
                                fn2-fields-value fn2-fields-rows nth)))))

(local
 (defthm fn2-run-decoded-header-value
   (let* ((b (fn2-format-page-header-decode rb slot gen 0 *fn2-run-header-area* pk ps pg f pool))
          (base (+ *fn2-run-c-header-fields* rb))
          (c (fn2-run-page-header-decode base slot gen *fn2-run-header-area* *fn2-run-entries-base* pk ps pg (mv-nth 2 b) pool)))
     (implies (and (fn2-run-page-headers-p bvals cvals dir count nr slot gen pk ps pg pool)
                   (natp rb) (natp watch) (< watch (+ rb *fn2-run-reader-restart*))
                   (<= (+ rb *fn2-run-reader-restart*) (fn2-fields-rows f)))
              (equal (fn2-fields-value watch (mv-nth 2 c))
                     (cond ((< watch rb) (fn2-fields-value watch f))
                           ((< watch base) (nth (- watch rb) bvals)) (t (nth (- watch base) cvals))))))
   :hints (("Goal" :use fn2-run-reads-two-header-fields
            :in-theory (disable fn2-run-page-headers-p fn2-format-page-header-decode fn2-run-page-header-decode
                                fn2-fields-value fn2-fields-rows nth)))))

(defthmd fn2-run-reads-stored-page-headers
  (let* ((read (fn2-run-read-header slot gen rb pk ps pg f pool)) (rf (mv-nth 1 read)))
    (implies (and (fn2-run-page-headers-p bvals cvals dir count nr slot gen pk ps pg pool)
                  (natp rb) (<= (+ rb *fn2-run-reader-restart*) (fn2-fields-rows f))
                  (natp watch) (< watch (+ rb *fn2-run-reader-restart*)))
             (and (equal (car read) :ok)
                  (equal (fn2-run-directory rb rf) dir)
                  (equal (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*) rf) count)
                  (equal (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-restarts*) rf) nr)
                  (equal (fn2-fields-value watch rf)
                         (cond ((< watch rb) (fn2-fields-value watch f))
                               ((< watch (+ rb *fn2-run-c-header-fields*)) (nth (- watch rb) bvals))
                               (t (nth (- watch (+ rb *fn2-run-c-header-fields*)) cvals)))))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-stored-header-metadata fn2-run-decoded-header-codes)
           :in-theory (e/d (fn2-run-read-header fn2-run-directory fn2-run-header-value)
                         (fn2-run-page-headers-p fn2-format-page-header-decode fn2-run-page-header-decode fn2-run-stored-header-p
                          fn2-fields-rows fn2-fields-value ceiling ceiling-to-floor nth len)))))
