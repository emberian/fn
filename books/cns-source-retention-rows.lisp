; Retaining one exact source identity changes counts and edges, not their table dimensions.
(in-package "ACL2")
(include-book "cns-source-retention")
(include-book "commit-alloc")
(fn2-book-layer :d)

(local
 (fn2-extents-preserves fn2-alloc-edge-add
  (edge holder i epoch counter kind fn2-extents fn2-alloc-edges)
  :specs (("-EXTENTS-ROWS" fn2-extents-rows 1 :frame fn2-extents)
          ("-EDGES-ROWS" fn2-alloc-edges-rows 2 :frame fn2-alloc-edges))
  :disable nil
  :hints ((fn2-columns-call-guard-hint 'fn2-alloc-edge-add
    '(fn2-alloc-account fn2-alloc-set-edge fn2-alloc-edge-count
      fn2-alloc-reason fn2-alloc-retirement-intentp fn2-alloc-durable-edgep)
    '(fn2-alloc-edge-add) world))))

(fn2-extents-preserves fn2-cns-source-claim-identity
 (s cns cnsgen ctl ctlgen request unit epoch allocation
    fn2-cns-sources fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops)
 :specs (("-EXTENTS-ROWS" fn2-extents-rows 1 :frame fn2-extents)
         ("-EDGES-ROWS" fn2-alloc-edges-rows 2 :frame fn2-alloc-edges))
 :disable nil
 :hints ((fn2-columns-call-guard-hint 'fn2-cns-source-claim-identity
   '(fn2-cns-source-retain-ownerp fn2-alloc-handle-code fn2-alloc-edge-add)
   '(fn2-cns-source-claim-identity) world)))

(fn2-cns-sources-preserves fn2-cns-source-root-hold-children
 (s cns cnsgen ctl ctlgen request fn2-cns-sources fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops)
 :specs (("-SOURCES-ROWS" fn2-cns-sources-rows 1 :frame fn2-cns-sources)
         ("-EXTENTS-ROWS" fn2-extents-rows 2 :frame fn2-extents)
         ("-EDGES-ROWS" fn2-alloc-edges-rows 3 :frame fn2-alloc-edges))
 :disable nil
 :hints ((fn2-columns-call-guard-hint 'fn2-cns-source-root-hold-children
   '(fn2-cns-source-retain-ownerp fn2-cns-source-claim-identity)
   '(fn2-cns-source-root-hold-children) world)))
