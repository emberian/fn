; A page decoder owns the field rows for its layout. A different source's
; head, the input to an insert, and the range bounds keep their values and
; byte references when their rows are outside that interval.
(in-package "ACL2")
(include-book "range-page-search-proof")

(defun-nx fn2-range-field-contents (j f)
  (list (fn2-fields-value j f) (fn2-fields-ref-slot j f) (fn2-fields-ref-gen j f)
        (fn2-fields-ref-off j f) (fn2-fields-ref-len j f) (fn2-fields-status j f)))

(local
 (defthm fn2-range-other-field-after-store
   (implies (and (natp j) (natp i) (not (equal i j)))
            (equal (fn2-range-field-contents j (fn2-layout-store i v slot gen off size status f))
                   (fn2-range-field-contents j f)))
   :hints (("Goal" :in-theory (e/d (fn2-range-field-contents fn2-layout-store fn2-fields-value
                         fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status
                         nth-update-nth) (fn2-fields-rows unsigned-byte-p nth update-nth))))))

(local
 (defthm fn2-range-field-after-codec-save
   (equal (fn2-range-field-contents j (fn2-codec-save base phase pos v hi size ref payload next f))
          (fn2-range-field-contents j f))
   :hints (("Goal" :in-theory (e/d (fn2-range-field-contents fn2-codec-save fn2-fields-value fn2-fields-ref-slot
                        fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status)
                       (unsigned-byte-p nth update-nth))))))

(defthmd fn2-range-scan-preserves-outside-field
  (let ((scan (fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)))
    (implies (and (natp i) (natp j) (or (< j i) (<= (+ i (len layout)) j)))
             (equal (fn2-range-field-contents j (mv-nth 9 scan)) (fn2-range-field-contents j f))))
  :hints (("Goal" :induct (fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool)
           :do-not '(preprocess)
           :expand ((fn2-layout-scan layout fuel i pos v hi size ref phase next slot gen end pk ps pg f pool))
           :in-theory (e/d ((:induction fn2-layout-scan))
                      ((:definition fn2-layout-scan) fn2-range-field-contents fn2-layout-store fn2-layout-byte
                       fn2-pool-read fn2-fields-rows fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen
                       fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status mod nfix unsigned-byte-p)))))

(defthm fn2-range-decoding-leaf-keeps-outside-field
  (let ((read (fn2-run-layout-decode 3 0 base slot gen off end pk ps pg f pool)))
    (implies (and (fn2-run-overview-row-atp 0 row base slot gen off end pk ps pg f pool)
                  (natp j) (or (< j base) (<= (+ base 5) j)))
             (equal (fn2-range-field-contents j (mv-nth 2 read)) (fn2-range-field-contents j f))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-overview-page-decode-refines-layout (level 0))
                 (:instance fn2-run-overview-admission-fits-decoder (layout *fn2-overview-entry*))
                 (:instance fn2-run-readable-page-prefix (bound (+ off (len (fn2-layout-octets *fn2-overview-entry* row)))))
                 (:instance fn2-run-page-scan-consumes-admitted-row (layout *fn2-overview-entry*)
                       (fuel *fn2-codec-decode-fuel*) (f (fn2-overview-entry-start base f))))
           :in-theory (e/d (fn2-run-overview-row-atp fn2-overview-entry-start fn2-range-scan-preserves-outside-field)
                        (fn2-range-field-contents fn2-run-layout-decode fn2-layout-scan fn2-layout-octets fn2-codec-save
                         fn2-run-read-bytes fn2-run-values-layoutp fn2-fields-rows fn2-layout-range-code
                         fn2-pool-wfp fn2-poolp fn2-pool-base unsigned-byte-p)))))
