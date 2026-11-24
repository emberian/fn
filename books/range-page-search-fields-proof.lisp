; The overview decoder writes at or after its field base. Page headers
; and query values below that base survive successful and yielded scans.
(in-package "ACL2")
(include-book "runs-served")
(include-book "runs-restart-fields-proof")

(local
 (defthm fn2-range-save-keeps-scalar
   (equal (fn2-fields-value i (fn2-codec-save base ph pos v hi size ref payload next f))
          (fn2-fields-value i f))
   :hints (("Goal" :in-theory (e/d (fn2-codec-save fn2-fields-value) (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-range-store-keeps-earlier-scalar
   (implies (and (natp i) (natp dest) (< i dest))
            (equal (fn2-fields-value i (fn2-layout-store dest v slot gen ref size status f))
                   (fn2-fields-value i f)))
   :hints (("Goal" :in-theory (e/d (fn2-layout-store fn2-fields-value fn2-fields-set-value
                                    update-fn2-fields-value$ai nth-update-nth)
                                   (nth update-nth unsigned-byte-p fn2-fields-rows))))))

(defmacro fn2-range-decoder-prefix-proof (name)
  (let* ((scan (fn2-codec-symbol name "-SCAN")) (index (fn2-codec-symbol name "-FIELD-INDEX"))
         (decode (fn2-codec-symbol name "-DECODE"))
         (step (fn2-codec-symbol name "-DECODE-STEP")) (start (fn2-codec-symbol name "-START"))
         (call `(,scan fuel base ph pos v hi size ref payload next slot gen end pk ps pg f pool)))
    `(progn
       (local (defthm ,(fn2-codec-symbol name "-DESTINATION-FOLLOWS-BASE")
                (implies (and (natp i) (natp base) (< i base))
                         (< i (+ base (,index ph))))
                :hints (("Goal" :in-theory (enable ,index)))))
       (local (defthm ,(fn2-codec-symbol name "-SCAN-KEEPS-EARLIER-SCALAR")
                (implies (and (natp i) (natp base) (< i base))
                         (equal (fn2-fields-value i (mv-nth 2 ,call)) (fn2-fields-value i f)))
                :hints (("Goal" :induct ,call :do-not '(preprocess) :expand ((:free (ph) ,call))
                         :in-theory (e/d ((:induction ,scan))
                             ((:definition ,scan) fn2-pool-read fn2-fields-value fn2-fields-rows fn2-layout-store
                              fn2-codec-save unsigned-byte-p fn2-fields-ref-slot fn2-fields-ref-gen
                              fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status))))))
       (local (defthm ,(fn2-codec-symbol name "-DECODE-KEEPS-EARLIER-SCALAR")
                (implies (and (natp i) (natp base) (< i base))
                         (equal (fn2-fields-value i (mv-nth 2 (,decode base slot gen off end pk ps pg f pool)))
                                (fn2-fields-value i f)))
                :hints (("Goal" :in-theory (e/d (,decode ,step ,start)
                                (,scan fn2-codec-save fn2-fields-value fn2-layout-range-code fn2-fields-decode-next
                                 fn2-fields-decode-phase fn2-fields-decode-pos fn2-fields-decode-acc
                                 fn2-fields-decode-high fn2-fields-decode-size fn2-fields-decode-ref
                                 fn2-fields-decode-payload unsigned-byte-p)))))))))

(fn2-range-decoder-prefix-proof fn2-overview-entry)
(fn2-range-decoder-prefix-proof fn2-overview-index)

(defthmd fn2-range-overview-decode-keeps-earlier-scalar
  (let ((read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)))
    (implies (and (natp i) (natp base) (< i base))
             (equal (fn2-fields-value i (mv-nth 2 read)) (fn2-fields-value i f))))
  :hints (("Goal" :in-theory (e/d (fn2-run-layout-decode)
                                  (fn2-overview-entry-decode fn2-overview-index-decode fn2-fields-value)))))

(defthmd fn2-range-page-search-keeps-earlier-scalar
  (let ((seek (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (natp rb) (natp i) (< i (+ rb *fn2-run-reader-restart*)))
             (equal (fn2-fields-value i (mv-nth 5 seek)) (fn2-fields-value i f))))
  :hints (("Goal" :induct (fn2-run-seek 3 level fuel lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
           :do-not '(preprocess)
           :in-theory (e/d (fn2-run-seek fn2-range-overview-decode-keeps-earlier-scalar)
              (fn2-run-restart-offset fn2-run-directory fn2-run-header-value fn2-run-layout-decode
               fn2-run-layout-compare fn2-fields-value floor)))))
