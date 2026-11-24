; A newly opened leaf or index page leaves the builder's separate input
; workspace available, including bytes already written there.
(in-package "ACL2")
(include-book "range-builder-source-space-proof")

(defthmd fn2-range-builder-page-keeps-input-slot
  (let* ((r (fn2-run-build-page b level dst dg unit epoch counter builds writers pool))
         (p (mv-nth 3 r)))
    (implies (and (natp src) (natp dst) (not (equal src dst)) (natp (fn2-pool-base dst pool))
                  (equal (fn2-run-builds-okind b builds) 9) (equal (fn2-run-builds-oslot b builds) 0)
                  (equal (fn2-run-builds-ogen b builds) 1))
             (and (equal (fn2-pool-base j p) (fn2-pool-base j pool))
                  (equal (fn2-layout-range-code src sg at cap t 9 0 1 p)
                         (fn2-layout-range-code src sg at cap t 9 0 1 pool)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-run-build-page fn2-run-build-page-kind fn2-range-opening-page-keeps-input-slot)
                      (fn2-run-open fn2-run-builds-height fn2-run-writers-phase fn2-run-writers-ordinal
                       fn2-run-builds-okind fn2-run-builds-oslot fn2-run-builds-ogen fn2-run-builds-wbase fn2-run-builds-schema
                       fn2-run-builds-run fn2-run-builds-history fn2-run-builds-incarnation fn2-run-builds-fields fn2-run-builds-limit
                       fn2-pool-base fn2-layout-range-code unsigned-byte-p)))))

(defthmd fn2-range-can-rewrite-input-prefix
  (implies (and (natp at) (natp cap) (<= at cap)
                (equal (fn2-layout-range-code src sg at cap t 9 0 1 p) :ok))
           (equal (fn2-layout-range-code src sg 0 cap t 9 0 1 p) :ok))
  :hints (("Goal" :in-theory (e/d (fn2-layout-range-code)
                  (fn2-pool-workspace-code fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-slot-base fn2-pool-capacity-bytes)))))
