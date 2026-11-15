; The actual identity provider: preview is private; materialization uses B's
; same owner-scoped reservation transition and the actual construction ledger.
(in-package "ACL2")
(include-book "checkpoint-planning")
(include-book "checkpoint-construction-owner")
(fn2-book-layer :c)

(defun fn2-checkpoint-planning-construction-reserve (token okind oslot ogen role ordinal intended page-kind level
 fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control)
 (declare (xargs :stobjs (fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control)
  :guard (and (fn2-checkpoint-planning-wfp fn2-checkpoint-planning) (fn2-checkpoint-recipe-wfp fn2-checkpoint-recipe)
              (fn2-checkpoint-recipe-order-wfp fn2-checkpoint-recipe-order) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-control-wfp fn2-control))))
 (b* (((when (equal (fn2-alloc-freeze-phase fn2-extents) 0))
       (b* (((mv code extent epoch counter fn2-checkpoint-construction fn2-extents fn2-control)
             (fn2-checkpoint-construction-reserve token okind oslot ogen role ordinal intended
              fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control)))
        (mv code extent epoch counter fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-checkpoint-construction fn2-extents fn2-control)))
      ((unless (and (< 0 (fn2-checkpoint-planning-rows fn2-checkpoint-planning)) (equal (fn2-control-stop fn2-control) 0)))
       (mv :planning 0 0 0 fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-checkpoint-construction fn2-extents fn2-control))
      (c (fn2-checkpoint-planning-candidate 0 fn2-checkpoint-planning))
      ((when (equal (fn2-checkpoint-planning-phase 0 fn2-checkpoint-planning) *fn2-checkpoint-planning-phase-preview*))
       (b* (((mv code extent epoch counter fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order)
             (fn2-checkpoint-planning-preview c token okind oslot ogen role ordinal intended page-kind level
              fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-csnapshot fn2-extents)))
        (mv code extent epoch counter fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-checkpoint-construction fn2-extents fn2-control)))
      ((mv code expected epoch counter)
       (fn2-checkpoint-planning-next c token okind oslot ogen role ordinal intended page-kind level
        fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-csnapshot fn2-extents))
      ((unless (and (eq code :ok) (< expected (fn2-checkpoint-construction-rows fn2-checkpoint-construction))
                    (equal (fn2-checkpoint-construction-live expected fn2-checkpoint-construction) 0)))
       (mv (if (eq code :ok) :ledger code) 0 0 0 fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-checkpoint-construction fn2-extents fn2-control))
      ((mv code & extent epoch counter fn2-extents)
       (fn2-alloc-planning-reserve token okind oslot ogen expected epoch counter fn2-extents))
      (fn2-control (if (eq code :links) (fn2-control-record-stop *fn2-stop-reason-alloc-links* fn2-control) fn2-control))
      ((unless (eq code :ok))
       (mv code extent epoch counter fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-checkpoint-construction fn2-extents fn2-control))
      (fn2-checkpoint-construction (fn2-checkpoint-construction-retain-reserved))
      ((mv code fn2-checkpoint-planning)
       (fn2-checkpoint-planning-note-reserved c token okind oslot ogen extent epoch counter
        fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-checkpoint-construction fn2-csnapshot fn2-extents)))
  (mv code extent epoch counter fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-checkpoint-construction fn2-extents fn2-control)))

(fn2-checkpoint-planning-preserves fn2-checkpoint-planning-construction-reserve
 (token okind oslot ogen role ordinal intended page-kind level fn2-checkpoint-planning fn2-checkpoint-recipe fn2-checkpoint-recipe-order fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control)
 :carriers ((fn2-checkpoint-planning 4 :prefix "-PLANNING") (fn2-checkpoint-recipe 5 :prefix "-RECIPE")
            (fn2-checkpoint-recipe-order 6 :prefix "-ORDER") (fn2-checkpoint-construction 7 :prefix "-CONSTRUCTION")
            (fn2-extents 8 :prefix "-EXTENTS") (fn2-control 9 :prefix "-CONTROL")))
