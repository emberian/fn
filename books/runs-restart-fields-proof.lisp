; A restart lookup only changes the value in the dedicated restart field.
(in-package "ACL2")
(include-book "runs-restart-reader-proof")

(local
 (defthm fn2-run-restart-save-keeps-value
   (equal (fn2-fields-value i (fn2-codec-save base ph pos v hi size ref payload next f))
          (fn2-fields-value i f))
   :hints (("Goal" :in-theory (e/d (fn2-codec-save fn2-fields-value) (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-run-restart-store-keeps-other-value
   (implies (and (natp i) (natp base) (not (equal i base)))
            (equal (fn2-fields-value i (fn2-layout-store base v slot gen ref size status f))
                   (fn2-fields-value i f)))
   :hints (("Goal" :in-theory (e/d (fn2-layout-store fn2-fields-value fn2-fields-set-value
                                    update-fn2-fields-value$ai nth-update-nth)
                                   (nth update-nth unsigned-byte-p fn2-fields-rows))))))

(local
 (defthm fn2-run-restart-scan-done
   (equal (fn2-run-restart-scan fuel base 1 pos v hi size ref payload next slot gen end pk ps pg f pool)
          (list :ok next (fn2-codec-save base 1 0 0 0 0 0 0 next f)))
   :hints (("Goal" :expand ((fn2-run-restart-scan fuel base 1 pos v hi size ref payload next slot gen end pk ps pg f pool))
            :in-theory (disable fn2-codec-save)))))
(local
 (defthm fn2-run-restart-scan-keeps-other-value
   (let ((scan (fn2-run-restart-scan fuel base ph pos v hi size ref payload next slot gen end pk ps pg f pool)))
     (implies (and (natp i) (natp base) (not (equal i base)))
              (equal (fn2-fields-value i (mv-nth 2 scan)) (fn2-fields-value i f))))
   :hints (("Goal" :induct (fn2-run-restart-scan fuel base ph pos v hi size ref payload next slot gen end pk ps pg f pool)
            :do-not '(preprocess)
            :expand ((fn2-run-restart-scan fuel base ph pos v hi size ref payload next slot gen end pk ps pg f pool))
            :in-theory (e/d ((:induction fn2-run-restart-scan) fn2-run-restart-field-index fn2-run-restart-next-phase fn2-run-restart-empty-p)
                            ((:definition fn2-run-restart-scan) fn2-run-restart-byte fn2-pool-read
                             fn2-fields-value fn2-fields-rows fn2-layout-store fn2-codec-save
                             fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                             fn2-fields-status unsigned-byte-p))))))

(defthm fn2-run-restart-read-keeps-other-value
  (implies (and (natp i) (natp base) (not (equal i (+ base *fn2-run-reader-restart*))))
           (equal (fn2-fields-value i (mv-nth 2 (fn2-run-restart-offset j slot gen base pk ps pg f pool)))
                  (fn2-fields-value i f)))
  :hints (("Goal" :in-theory (e/d (fn2-run-restart-offset fn2-run-restart-decode
                                   fn2-run-restart-decode-step fn2-run-restart-start)
                            (fn2-run-header-value fn2-run-directory fn2-run-restart-scan fn2-codec-save
                             fn2-layout-range-code fn2-fields-value fn2-fields-rows unsigned-byte-p
                             fn2-fields-decode-phase fn2-fields-decode-pos fn2-fields-decode-next
                             fn2-fields-decode-acc fn2-fields-decode-high fn2-fields-decode-size
                             fn2-fields-decode-ref fn2-fields-decode-payload)))))

(defthmd fn2-run-restart-keeps-header-and-query
  (let ((after (mv-nth 2 (fn2-run-restart-offset j slot gen rb pk ps pg f pool))))
    (implies (and (natp rb) (natp qbase) (< (+ 1 qbase) (+ rb *fn2-run-reader-restart*)))
             (and (equal (fn2-run-directory rb after) (fn2-run-directory rb f))
                  (equal (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*) after)
                         (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-entries*) f))
                  (equal (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-restarts*) after)
                         (fn2-run-header-value rb (+ *fn2-run-c-header-fields* *fn2-run-page-header-field-restarts*) f))
                  (equal (fn2-fields-value qbase after) (fn2-fields-value qbase f))
                  (equal (fn2-fields-value (+ 1 qbase) after) (fn2-fields-value (+ 1 qbase) f)))))
  :hints (("Goal" :in-theory (e/d (fn2-run-directory fn2-run-header-value)
                                  (fn2-fields-value fn2-run-restart-offset nfix)))))
