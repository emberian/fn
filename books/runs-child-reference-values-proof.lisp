; Promotion keeps the leading overview key and fills the index row with
; the sealed child's identity, count and parent-held digest.
(in-package "ACL2")
(include-book "runs-store-child-digest-proof")
(include-book "range-window-proof")

(defun-nx fn2-run-overview-child-row (key w hrow writers ds)
  (list (car key) (cadr key) 0 (fn2-run-writers-unit w writers) (fn2-run-writers-epoch w writers)
        (fn2-run-writers-counter w writers) (fn2-run-writers-page-kind w writers) *fn2-run-page-size*
        (cons 1 (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds))) (fn2-run-writers-entries w writers)))

(defun-nx fn2-run-child-reference-room-p (w level ib hrow hslot hgen writers f pool ds)
  (and (fn2-run-writersp writers) (fn2-run-writers-wfp writers) (natp w) (< w (fn2-run-writers-rows writers))
       (natp level) (< level *fn2-run-max-levels*) (natp ib) (<= (+ ib (len *fn2-overview-index*)) (fn2-fields-rows f))
       (unsigned-byte-p 32 hslot) (unsigned-byte-p 60 hgen) (fn2-digest-rowp hrow ds)
       (natp (fn2-pool-base hslot pool))
       (equal (fn2-layout-range-code hslot hgen (* 32 level) (+ 32 (* 32 level)) t 9 0 1 pool) :ok)))

(local
 (defthm fn2-run-view-index-fields
   (let ((hv (+ ib 2 *fn2-format-ref-field-expected-hash*)))
     (implies (natp ib)
              (equal (fn2-run-unload-values *fn2-overview-index* ib f pool)
                     (list (fn2-fields-value ib f) (fn2-fields-value (+ ib 1) f) (fn2-fields-value (+ ib 2) f)
                           (fn2-fields-value (+ ib 3) f) (fn2-fields-value (+ ib 4) f) (fn2-fields-value (+ ib 5) f)
                           (fn2-fields-value (+ ib 6) f) (fn2-fields-value (+ ib 7) f)
                           (cons (fn2-fields-value hv f)
                                 (fn2-run-read-bytes (fn2-fields-ref-len hv f) (fn2-fields-ref-slot hv f)
                                       (fn2-fields-ref-gen hv f) (fn2-fields-ref-off hv f) 9 0 1 pool))
                           (fn2-fields-value (+ ib 9) f)))))
   :hints (("Goal" :in-theory (e/d (fn2-run-unload-values)
                            (fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len fn2-run-read-bytes))))))

(defthmd fn2-run-child-reference-records-sealed-writer
  (let* ((ref (fn2-run-child-ref w level (+ ib 2) (+ ib 2 *fn2-format-ref-num-fields*) hrow hslot hgen 9 0 1 writers f pool ds))
         (rf (mv-nth 1 ref)) (after (mv-nth 2 ref)) (bytes (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds))))
    (implies (fn2-run-child-reference-room-p w level ib hrow hslot hgen writers f pool ds)
             (and (equal (car ref) :ok)
                  (equal after (mv-nth 1 (fn2-run-load-bytes bytes hslot hgen (* 32 level) 9 0 1 pool)))
                  (equal (fn2-run-unload-values *fn2-overview-index* ib rf after)
                         (fn2-run-overview-child-row (fn2-overview-range-key-at ib f) w hrow writers ds)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-child-digest-occupies-slot (slot hslot) (gen hgen) (off (* 32 level))
                               (pk 9) (ps 0) (pg 1) (row hrow)))
           :in-theory (e/d (fn2-run-child-ref fn2-run-child-reference-room-p fn2-run-overview-child-row
                    fn2-overview-range-key-at fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                    fn2-fields-set-value update-fn2-fields-value$ai fn2-fields-set-ref-slot update-fn2-fields-ref-slot$ai
                    fn2-fields-set-ref-gen update-fn2-fields-ref-gen$ai fn2-fields-set-ref-off update-fn2-fields-ref-off$ai
                    fn2-fields-set-ref-len update-fn2-fields-ref-len$ai nth-update-nth)
                  (fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-run-writers-unit fn2-run-writers-epoch
                   fn2-run-writers-counter fn2-run-writers-page-kind fn2-run-writers-entries fn2-digest-store fn2-digest-rowp
                   fn2-page-parent-octets fn2-digest-list fn2-run-load-bytes fn2-run-unload-values fn2-run-read-bytes
                   fn2-pool-base fn2-layout-range-code fn2-fields-rows nth update-nth)))))
