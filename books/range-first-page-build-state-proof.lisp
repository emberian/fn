; The request for the first page changes just the empty builder's height.
(in-package "ACL2")
(include-book "range-initial-writer-proof")

(defun-nx fn2-range-first-page-build-p (b)
  (and (fn2-run-buildsp b) (fn2-run-builds-wfp b) (< 0 (fn2-run-builds-rows b))
       (equal (fn2-run-builds-phase 0 b) *fn2-run-build-phase-adding*) (equal (fn2-run-builds-height 0 b) 1)
       (equal (fn2-run-builds-wbase 0 b) 0) (equal (fn2-run-builds-crow 0 b) 0) (equal (fn2-run-builds-hbase 0 b) 136)
       (equal (fn2-run-builds-entries 0 b) 0) (equal (fn2-run-builds-schema 0 b) 3)
       (equal (fn2-run-builds-fields 0 b) 0) (equal (fn2-run-builds-limit 0 b) 2048)
       (equal (fn2-run-builds-okind 0 b) 9) (equal (fn2-run-builds-oslot 0 b) 0) (equal (fn2-run-builds-ogen 0 b) 1)))

(defthmd fn2-range-first-page-has-requested-height
  (implies (and (fn2-range-empty-build-state-p run b) (fn2-run-buildsp b) (fn2-run-builds-wfp b)
                (< 0 (fn2-run-builds-rows b)))
           (fn2-range-first-page-build-p (fn2-run-builds-set-height 0 1 b)))
  :hints (("Goal" :in-theory (e/d (fn2-range-first-page-build-p fn2-range-empty-build-state-p fn2-run-builds-height
                      fn2-run-builds-wbase fn2-run-builds-schema fn2-run-builds-fields fn2-run-builds-limit fn2-run-builds-okind
                      fn2-run-builds-oslot fn2-run-builds-ogen fn2-run-builds-rows fn2-run-builds-phase fn2-run-builds-entries
                      fn2-run-builds-crow fn2-run-builds-hbase nth-update-nth)
                    (fn2-run-builds-set-height fn2-run-buildsp fn2-run-builds-wfp fn2-run-builds-run fn2-run-builds-pages
                      nth update-nth)))))
