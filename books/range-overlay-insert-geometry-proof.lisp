; An insert can change the row count, byte fill and offsets. Its storage
; owner, address, table capacities and source identity persist.
(in-package "ACL2")
(include-book "range-served")

(defun-nx fn2-ov-arena-geometry (o ov)
  (list (fn2-overlays-phase o ov) (fn2-overlays-schema o ov)
        (fn2-overlays-slot o ov) (fn2-overlays-gen o ov) (fn2-overlays-cap o ov)
        (fn2-overlays-ibase o ov) (fn2-overlays-icap o ov)
        (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov) (fn2-overlays-ogen o ov)))

(local
 (defthm fn2-ov-changing-fill-or-count-retains-geometry
   (and (equal (fn2-ov-arena-geometry j (fn2-overlays-set-fill o v ov)) (fn2-ov-arena-geometry j ov))
        (equal (fn2-ov-arena-geometry j (fn2-overlays-set-count o v ov)) (fn2-ov-arena-geometry j ov)))
   :hints (("Goal" :in-theory (e/d (fn2-ov-arena-geometry fn2-overlays-phase fn2-overlays-schema
                                     fn2-overlays-slot fn2-overlays-gen fn2-overlays-cap fn2-overlays-ibase fn2-overlays-icap
                                     fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen
                                     fn2-overlays-set-fill fn2-overlays-set-count update-fn2-overlays-count$ai
                                     update-fn2-overlays-fill$ai nth-update-nth) (nth update-nth))))))

(local
 (defthm fn2-ov-recording-offset-retains-geometry
   (and (equal (fn2-ov-arena-geometry j (mv-nth 1 (fn2-ov-place o pos off end ov ix))) (fn2-ov-arena-geometry j ov))
        (equal (fn2-ov-arena-geometry j (mv-nth 1 (fn2-ov-reput o pos off end ov ix))) (fn2-ov-arena-geometry j ov)))
   :hints (("Goal" :in-theory (e/d (fn2-ov-place fn2-ov-reput)
                         (fn2-ov-arena-geometry fn2-ov-insert-at fn2-ov-okp fn2-overlays-ibase fn2-overlays-icap
                          fn2-overlays-count fn2-overlay-index-rows fn2-overlays-set-count fn2-overlays-set-fill
                          fn2-overlay-index-set-off unsigned-byte-p))))))

(local
 (defthm fn2-ov-write-retains-geometry
   (equal (fn2-ov-arena-geometry j (mv-nth 1 (fn2-ov-write o pos base repl ov ix f p))) (fn2-ov-arena-geometry j ov))
   :hints (("Goal" :in-theory (e/d (fn2-ov-write) (fn2-ov-arena-geometry fn2-ov-okp fn2-run-layout-encode
                      fn2-run-layout-size fn2-ov-place fn2-ov-reput fn2-fields-rows fn2-overlays-schema fn2-overlays-fill
                      fn2-overlays-slot fn2-overlays-gen fn2-overlays-cap fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))))))

(defthmd fn2-ov-inserting-retains-geometry
  (equal (fn2-ov-arena-geometry j (mv-nth 1 (fn2-ov-insert o base eb ov ix f p))) (fn2-ov-arena-geometry j ov))
  :hints (("Goal" :in-theory (e/d (fn2-ov-insert)
                       (fn2-ov-arena-geometry fn2-ov-write fn2-ov-locate fn2-ov-okp fn2-overlays-phase
                        fn2-run-layout-merge fn2-overlays-schema fn2-overlays-count fn2-overlays-icap fn2-overlays-okind
                        fn2-overlays-oslot fn2-overlays-ogen)))))

(local
 (defthm fn2-ov-writing-retains-tables
   (let* ((r (fn2-ov-write o pos base repl ov ix f p)) (ov2 (mv-nth 1 r)) (ix2 (mv-nth 2 r)))
     (implies (and (fn2-overlaysp ov) (fn2-overlay-indexp ix) (fn2-overlays-wfp ov) (fn2-overlay-index-wfp ix))
              (and (fn2-overlaysp ov2) (fn2-overlay-indexp ix2) (fn2-overlays-wfp ov2) (fn2-overlay-index-wfp ix2)
                   (equal (fn2-overlays-rows ov2) (fn2-overlays-rows ov))
                   (equal (fn2-overlay-index-rows ix2) (fn2-overlay-index-rows ix)))))
   :hints (("Goal" :in-theory (e/d (fn2-ov-write)
                     (fn2-overlaysp fn2-overlay-indexp fn2-overlays-wfp fn2-overlay-index-wfp fn2-overlays-rows fn2-overlay-index-rows
                      fn2-ov-okp fn2-run-layout-encode fn2-run-layout-size fn2-ov-place fn2-ov-reput fn2-fields-rows
                      fn2-overlays-schema fn2-overlays-fill fn2-overlays-slot fn2-overlays-gen fn2-overlays-cap
                      fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))))))

(defthmd fn2-ov-inserting-retains-tables
  (let* ((r (fn2-ov-insert o base eb ov ix f p)) (ov2 (mv-nth 1 r)) (ix2 (mv-nth 2 r)) (f2 (mv-nth 3 r)))
    (implies (and (fn2-overlaysp ov) (fn2-overlay-indexp ix) (fn2-overlays-wfp ov) (fn2-overlay-index-wfp ix) (fn2-fieldsp f) (fn2-fields-wfp f))
             (and (fn2-overlaysp ov2) (fn2-overlay-indexp ix2) (fn2-overlays-wfp ov2) (fn2-overlay-index-wfp ix2) (fn2-fieldsp f2) (fn2-fields-wfp f2)
                  (equal (fn2-overlays-rows ov2) (fn2-overlays-rows ov))
                  (equal (fn2-overlay-index-rows ix2) (fn2-overlay-index-rows ix))
                  (equal (fn2-fields-rows f2) (fn2-fields-rows f)))))
  :hints (("Goal" :in-theory (e/d (fn2-ov-insert)
                       (fn2-overlaysp fn2-overlay-indexp fn2-overlays-wfp fn2-overlay-index-wfp fn2-overlays-rows fn2-overlay-index-rows
                        fn2-fields-rows fn2-fieldsp fn2-fields-wfp fn2-ov-write fn2-ov-locate fn2-ov-okp
                        fn2-overlays-phase fn2-run-layout-merge fn2-overlays-schema fn2-overlays-count
                        fn2-overlays-icap fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen)))))
