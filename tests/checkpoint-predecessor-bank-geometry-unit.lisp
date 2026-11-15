; UNEXECUTED geometry-only control using canonical bank/inventory initializers.
; This is not a whole served profile or publication witness; no authority or
; physical Ref is seeded. Requires canonical bank provider5153c32b7+prerequisites.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/checkpoint-metadata-resources")
(defun fn2-cpb-body (o r e fn2-overlays fn2-run-installed fn2-checkpoint-predecessors)
 (declare (xargs :stobjs (fn2-overlays fn2-run-installed fn2-checkpoint-predecessors) :verify-guards nil))
 (b* ((profile (list (cons :identity-overlays o) (cons :identity-runs r) (cons :extent-slots e)))
      (admitted (fn2-checkpoint-predecessor-profilep profile))
      ((unless admitted) (mv nil fn2-overlays fn2-run-installed fn2-checkpoint-predecessors))
      (fn2-overlays (fn2-overlays-init o fn2-overlays))
      (fn2-run-installed (fn2-run-installed-init-configured r e fn2-run-installed))
      (fn2-checkpoint-predecessors (fn2-checkpoint-predecessors-init-for profile fn2-checkpoint-predecessors)))
  (mv (and (fn2-run-installed-bank-geometry-p fn2-run-installed)
           (= (fn2-run-installed-resident-limit fn2-run-installed) r)
           (= (fn2-run-installed-bank-capacity fn2-run-installed) e)
           (= (fn2-checkpoint-predecessors-rows fn2-checkpoint-predecessors)
              (+ (fn2-overlays-rows fn2-overlays) (fn2-run-installed-rows fn2-run-installed))))
      fn2-overlays fn2-run-installed fn2-checkpoint-predecessors)))
(defun fn2-cpb-test (o r e)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-overlays (with-local-stobj fn2-run-installed
  (with-local-stobj fn2-checkpoint-predecessors
   (mv-let (ok fn2-overlays fn2-run-installed fn2-checkpoint-predecessors)
    (fn2-cpb-body o r e fn2-overlays fn2-run-installed fn2-checkpoint-predecessors) ok)))))
(assert-event (fn2-cpb-test 3 4 2))
(assert-event (fn2-cpb-test 0 0 2))
; Former O+R+E would admit this overflow; no huge table allocation is attempted.
(assert-event (not (fn2-checkpoint-predecessor-profilep
 '((:identity-overlays . 0) (:identity-runs . 4294967294) (:extent-slots . 1)))))
