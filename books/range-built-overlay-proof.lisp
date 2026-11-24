; The active overlay retains its identity and owner throughout input loading.
(in-package "ACL2")
(include-book "range-served")

(defun-nx fn2-range-overlay-descriptor (ov)
  (list (fn2-overlays-rows ov) (fn2-overlays-phase 0 ov) (fn2-overlays-schema 0 ov)
        (fn2-overlays-seq 0 ov) (fn2-overlays-okind 0 ov) (fn2-overlays-oslot 0 ov) (fn2-overlays-ogen 0 ov)))

(local
 (defthm fn2-range-placing-row-preserves-overlay
   (and (equal (fn2-range-overlay-descriptor (mv-nth 1 (fn2-ov-place o pos off end ov ix)))
               (fn2-range-overlay-descriptor ov))
        (equal (fn2-range-overlay-descriptor (mv-nth 1 (fn2-ov-reput o pos off end ov ix)))
               (fn2-range-overlay-descriptor ov)))
   :hints (("Goal" :in-theory (e/d (fn2-range-overlay-descriptor fn2-ov-place fn2-ov-reput
                    fn2-overlays-rows fn2-overlays-phase fn2-overlays-schema fn2-overlays-seq
                    fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen)
                  (fn2-ov-okp fn2-ov-insert-at fn2-overlays-ibase fn2-overlays-icap fn2-overlays-count
                   fn2-overlay-index-rows unsigned-byte-p nth update-nth))))))

(local
 (defthm fn2-range-encoding-row-preserves-overlay
   (equal (fn2-range-overlay-descriptor (mv-nth 1 (fn2-ov-write o pos base repl ov ix f pool)))
          (fn2-range-overlay-descriptor ov))
   :hints (("Goal" :in-theory (e/d (fn2-ov-write)
                  (fn2-range-overlay-descriptor fn2-ov-okp fn2-ov-place fn2-ov-reput fn2-run-layout-size
                   fn2-run-layout-encode fn2-overlays-fill fn2-overlays-cap fn2-fields-rows))))))

(local
 (defthm fn2-range-inserting-row-preserves-overlay
   (equal (fn2-range-overlay-descriptor (mv-nth 1 (fn2-ov-insert o base eb ov ix f pool)))
          (fn2-range-overlay-descriptor ov))
   :hints (("Goal" :in-theory (e/d (fn2-ov-insert)
                (fn2-ov-okp fn2-range-overlay-descriptor fn2-ov-locate fn2-ov-write fn2-run-layout-merge
                 fn2-overlays-phase fn2-overlays-count fn2-overlays-icap))))))

(defthmd fn2-range-loading-rows-preserves-overlay
  (equal (fn2-range-overlay-descriptor (mv-nth 1 (fn2-ov-adapter-load sid layout entries src sg off ov ix f pool)))
         (fn2-range-overlay-descriptor ov))
  :hints (("Goal" :induct (fn2-ov-adapter-load sid layout entries src sg off ov ix f pool)
           :in-theory (e/d (fn2-ov-adapter-load)
                          (fn2-range-overlay-descriptor fn2-ov-insert fn2-run-load-values)))))

(local
 (defthm fn2-range-started-overlay-descriptor
   (let ((start (fn2-ov-start 0 sid slot gen 0 256 9 0 1 0 ov ix pool)))
     (implies (equal (car start) :ok)
              (equal (fn2-range-overlay-descriptor (mv-nth 1 start))
                     (list (fn2-overlays-rows ov) *fn2-overlay-phase-active* sid 0 9 0 1))))
   :hints (("Goal" :in-theory (e/d (fn2-ov-start fn2-range-overlay-descriptor fn2-overlays-rows
                  fn2-overlays-phase fn2-overlays-schema fn2-overlays-seq fn2-overlays-okind fn2-overlays-oslot
                  fn2-overlays-ogen nth-update-nth)
                 (fn2-pool-reset fn2-pool-rows fn2-pool-slot-cap fn2-overlay-index-rows nth update-nth unsigned-byte-p))))))

(defthmd fn2-range-loaded-overlay-source
  (let ((load (fn2-rga-call fn2-rga-overlay sid layout entries)))
    (implies (equal (car load) :ok)
             (and (equal (fn2-range-overlay-descriptor (mv-nth 3 load))
                         (list (fn2-overlays-rows fn2-overlays) *fn2-overlay-phase-active* sid 0 9 0 1))
                  (equal (mv-nth 5 load) fn2-run-installed))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-rga-overlay fn2-range-started-overlay-descriptor
                          fn2-range-loading-rows-preserves-overlay (:t fn2-ov-adapter-load) (:t fn2-ov-start) eq mv-nth car-cons cdr-cons
                          (:e mv-nth) (:e zp) (:e consp) (:e equal) (:e unary--) (:e binary-+))))))
