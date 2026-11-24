; Both physical headers precede the stored body. A preserved body span
; made up of successful zero reads stays valid input to the format checker.
(in-package "ACL2")
(include-book "runs-headed-page-contents-proof")
(include-book "ribbon-false-neg-finish-proof")

(local
 (defthm fn2-run-read-error-is-never-zero
   (not (equal (mv-nth 0 (fn2-pool-read slot gen off pk ps pg pool)) 0))
   :hints (("Goal" :in-theory (e/d (fn2-pool-read fn2-pool-readable-code fn2-pool-handle-code mv-nth)
                                   (fn2-pool-base fn2-pool-datai fn2-pool-fill fn2-pool-data-length
                                    fn2-pool-ownerp fn2-pool-state fn2-pool-rows fn2-pool-gen))))))

(local
 (defthm fn2-run-zero-read-includes-status
   (let ((r (fn2-pool-read slot gen off pk ps pg pool)))
     (equal (equal (if (equal (mv-nth 0 r) :ok) (mv-nth 1 r) (mv-nth 0 r)) 0)
            (and (equal (mv-nth 0 r) :ok) (equal (mv-nth 1 r) 0))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-read-error-is-never-zero))))))

(defthmd fn2-run-readable-zero-span
  (implies (natp start)
           (equal (fn2-ribbon-zero-region-p n start slot gen pool)
                  (equal (fn2-run-read-bytes n slot gen start 9 0 1 pool)
                         (fn2-layout-le n 0))))
  :hints (("Goal" :induct (fn2-ribbon-zero-region-p n start slot gen pool)
           :expand ((fn2-run-read-bytes n slot gen start 9 0 1 pool) (fn2-layout-le n 0))
           :in-theory (e/d (fn2-ribbon-zero-region-p fn2-run-read-bytes fn2-layout-le)
                           (fn2-pool-read mv-nth)))))

(defthmd fn2-run-heading-keeps-zero-padding
  (let ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
        (after (mv-nth 3 (fn2-run-head w writers restarts f pool))))
    (implies (and (fn2-run-heading-page-p w writers f pool)
                  (equal (fn2-run-writers-okind w writers) 9)
                  (equal (fn2-run-writers-oslot w writers) 0)
                  (equal (fn2-run-writers-ogen w writers) 1)
                  (natp start) (<= *fn2-run-entries-base* start) (<= start *fn2-run-page-size*)
                  (fn2-ribbon-zero-region-p (- *fn2-run-page-size* start) start slot gen pool))
             (fn2-ribbon-zero-region-p (- *fn2-run-page-size* start) start slot gen after)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-heading-keeps-page-span (at start) (n (- *fn2-run-page-size* start))))
           :in-theory (e/d (fn2-run-readable-zero-span)
                      (fn2-run-heading-page-p fn2-run-head fn2-run-read-bytes fn2-ribbon-zero-region-p
                       fn2-layout-le fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind
                       fn2-run-writers-oslot fn2-run-writers-ogen)))))
