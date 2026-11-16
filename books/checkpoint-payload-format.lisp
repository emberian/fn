; Shared typed source-manifest observations. Callers authenticate a physical
; unit against its retained location commitment BEFORE these decoders. This
; book supplies neither that admission nor allocator/source authority.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "source-manifest-codec")
(include-book "pool-ranges")
(fn2-book-layer :b)
(defun fn2-checkpoint-payload-read-header (base source-slot source-gen source-off total slot gen kind owner generation fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
 :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((mv code next fn2-fields) (fn2-am-get-header base total slot gen 0 *fn2-commit-unit-bytes* kind owner generation fn2-fields fn2-pool))
      ((unless (and (eq code :ok) (natp next) (< 0 next) (<= next *fn2-commit-unit-bytes*))) (mv :manifest-header next fn2-fields))
      (h (+ base *fn2-format-source-manifest-header-field-source-identity*))
      ((unless (and (< h (fn2-fields-rows fn2-fields)) (equal (fn2-fields-ref-len h fn2-fields) 32))) (mv :manifest-identity next fn2-fields))
      ((mv code order &) (fn2-pool-compare
       (fn2-fields-ref-slot h fn2-fields) (fn2-fields-ref-gen h fn2-fields) (fn2-fields-ref-off h fn2-fields) kind owner generation
       source-slot source-gen source-off kind owner generation 32 fn2-pool)))
  (mv (if (and (eq code :ok) (eq order :equal)) :ok :identity-mismatch) next fn2-fields)))

(defun fn2-checkpoint-payload-read-entry (base position total slot gen off kind owner generation fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
 :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((mv code next logical len unit epoch allocation fn2-fields)
       (fn2-am-get-entry base slot gen off *fn2-commit-unit-bytes* kind owner generation fn2-fields fn2-pool))
      ((unless (and (eq code :ok) (< off next) (<= next *fn2-commit-unit-bytes*) (equal logical position)
                    (equal len (min *fn2-am-block-bytes* (- total position)))
                    (equal (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-storage-domain*) fn2-fields) 0)
                    (equal (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-page-kind*) fn2-fields) *page-kind-raw-source*)
                    (equal (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-encoded-length*) fn2-fields) len)))
       (mv :manifest-entry next logical len unit epoch allocation fn2-fields))
      (h (+ base *fn2-format-source-manifest-entry-field-block-expected-hash*))
      (cv (+ base *fn2-format-source-manifest-entry-field-subtree-cv*))
      (code (if (and (equal (fn2-fields-ref-slot h fn2-fields) slot) (equal (fn2-fields-ref-gen h fn2-fields) gen)
                    (equal (fn2-fields-ref-slot cv fn2-fields) slot) (equal (fn2-fields-ref-gen cv fn2-fields) gen)
                    (equal (fn2-fields-ref-len h fn2-fields) 32) (equal (fn2-fields-ref-len cv fn2-fields) 32)) :ok :manifest-proof)))
  (mv code next logical len unit epoch allocation fn2-fields)))
(fn2-fc-shape fn2-checkpoint-payload-read-header-shape
 (fn2-checkpoint-payload-read-header base source-slot source-gen source-off total slot gen kind owner generation fn2-fields fn2-pool)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)) ((fn2-fields 2)))
(fn2-fc-shape fn2-checkpoint-payload-read-entry-shape
 (fn2-checkpoint-payload-read-entry base position total slot gen off kind owner generation fn2-fields fn2-pool)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)) ((fn2-fields 7)))

(defthm fn2-checkpoint-payload-read-header-fields-refinement
 (equal (mv-nth 2 (fn2-checkpoint-payload-read-header base source-slot source-gen source-off total slot gen kind owner generation fn2-fields fn2-pool))
        (mv-nth 2 (fn2-am-get-header base total slot gen 0 *fn2-commit-unit-bytes* kind owner generation fn2-fields fn2-pool)))
 :hints (("Goal" :in-theory (enable fn2-checkpoint-payload-read-header))))
(defthm fn2-checkpoint-payload-read-entry-fields-refinement
 (equal (mv-nth 7 (fn2-checkpoint-payload-read-entry base position total slot gen off kind owner generation fn2-fields fn2-pool))
        (mv-nth 7 (fn2-am-get-entry base slot gen off *fn2-commit-unit-bytes* kind owner generation fn2-fields fn2-pool)))
 :hints (("Goal" :in-theory (enable fn2-checkpoint-payload-read-entry))))
