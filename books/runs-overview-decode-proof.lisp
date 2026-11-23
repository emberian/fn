; The overview page decoder agrees with the layout scanner.
(in-package "ACL2")
(include-book "runs-overview-index-decode-proof")

(fn2-run-prove-page-reader fn2-overview-entry)

(defthm fn2-run-overview-page-decode-refines-layout
  (let* ((indexp (and (integerp level) (< 0 level)))
         (layout (if indexp *fn2-overview-index* *fn2-overview-entry*))
         (initial (if indexp (fn2-overview-index-start base f) (fn2-overview-entry-start base f)))
         (model (fn2-layout-scan layout *fn2-codec-decode-fuel* base
                                 0 0 0 0 0 0 off slot gen end pk ps pg initial pool))
         (read (fn2-run-layout-decode 3 level base slot gen off end pk ps pg f pool)))
    (implies (and (fn2-poolp pool) (fn2-pool-wfp pool) (natp base) (< base (fn2-fields-rows f))
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= off end)
                  (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
                  (eq (car model) :ok))
             (fn2-run-scan-agreement read model base
                                     (if indexp *fn2-overview-index-phase-done* *fn2-overview-entry-phase-done*))))
  :rule-classes nil
  :hints (("Goal" :cases ((and (integerp level) (< 0 level)))
           :use (fn2-overview-index-decode-refines-layout fn2-overview-entry-decode-refines-layout)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn2-run-layout-decode eq eql not (:e equal) (:e eql))))))
