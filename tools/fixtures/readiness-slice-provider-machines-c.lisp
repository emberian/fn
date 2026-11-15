(fn2-idc-child fn2-core-run-cursors fn2-run-cursors
 (fn2-run-cursors-init (fn2-b-run-cursor-rows profile) fn2-run-cursors)
 "A decision's resumable run cursor (cursor row = decision row), then each read row's lookup cursor and its range sources' (C-S4).")
(fn2-idc-child fn2-core-checkpoint-summary-leases fn2-checkpoint-summary-leases
 (fn2-checkpoint-summary-leases-init (fn2-b-run-cursor-rows profile) fn2-checkpoint-summary-leases)
 "Every actual C cursor can retain one exact selected physical source across yields.")
(fn2-idc-child fn2-core-run-paths fn2-run-paths
 (fn2-run-paths-init (* *fn2-run-max-levels* (fn2-b-run-cursor-rows profile)) fn2-run-paths)
 "Each cursor's descent, one row per level.")
(fn2-idc-child fn2-core-run-loads fn2-run-loads
 (fn2-run-load-profile-init profile fn2-run-loads)
 "A private authenticated 64KiB page and sector workspace per active physical cursor.")
(defcorechild fn2-core-run-load-ops fn2-run-load-ops
 :init (fn2-run-load-ops-init (fn2-profile-o profile) fn2-run-load-ops)
 :profilep (unsigned-byte-p 32 (fn2-profile-o profile))
 :harvest (fn2-run-load-harvest ((fn2-core-run-loads fn2-run-loads) (fn2-core-run-load-ops fn2-run-load-ops)))
 :why "Route exact physical read completions before operation finish, without scanning active cursors.")
(defcorechild fn2-core-run-load-geometry fn2-run-load-geometry
 :init (fn2-run-load-geometry-profile-init profile fn2-run-load-geometry)
 :profilep (fn2-run-load-geometry-profilep profile)
 :why "Readonly profile-derived cursor/checker geometry binds the cold loader capability scan.")
(defcorechild fn2-core-run-load-readiness fn2-run-load-readiness
 :init (fn2-run-load-readiness-init 1 fn2-run-load-readiness) :profilep t
 :why "The cold capability scan retains selected identity, exact EOF and admissions serial across turns.")
