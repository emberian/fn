; Declared output shapes from checkpoint-metadata-driver.lisp at267894d02.
; These literal projections bind the output-count control to that exact table.
; They do NOT execute or prove the actual parametric project helper, validate
; its write set, or establish ACL2 admission. Unknown macro expansions remain
; unresolved by the generic preflight.
(defconst *fn2-checkpoint-root1-children*
 '(fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-retained-entry fn2-checkpoint-payload fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-page fn2-checkpoint-page-verified fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-run-cache fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))

(defconst *fn2-checkpoint-root1-outputs*
 '((fn2-checkpoint-root1-begin fn2-checkpoint-root1 fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-run-builds fn2-run-writers fn2-pool)
   (fn2-checkpoint-root1-select fn2-checkpoint-root1 fn2-checkpoint-source fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-cursors fn2-pool)
   (fn2-checkpoint-root1-bind fn2-checkpoint-page)
   (fn2-checkpoint-root1-consume fn2-checkpoint-root1 fn2-digests)
   (fn2-checkpoint-root1-work fn2-checkpoint-root1 fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-construction fn2-extents fn2-control fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
   (fn2-checkpoint-root1-payload-start fn2-checkpoint-root1 fn2-checkpoint-retained-entry fn2-checkpoint-semantic fn2-checkpoint-payload fn2-digests fn2-b3 fn2-extents fn2-alloc-edges)
   (fn2-checkpoint-root1-retention fn2-checkpoint-root1 fn2-checkpoint-metadata fn2-extents fn2-alloc-edges fn2-checkpoint-semantic)
   (fn2-checkpoint-root1-closure fn2-checkpoint-root1 fn2-checkpoint-metadata-manifest fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-metadata fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests fn2-checkpoint-payload fn2-checkpoint-retained-entry fn2-checkpoint-refs fn2-checkpoint-bytes fn2-csnapshot)
   (fn2-checkpoint-root1-read fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-metadata fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests fn2-checkpoint-payload)
   (fn2-checkpoint-root1-step fn2-checkpoint-root1 fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-retained-entry fn2-checkpoint-payload fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-checkpoint-refs fn2-checkpoint-bytes fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))

(defmacro fn2-checkpoint-root1-begin-count-control (code)
 `(mv ,code fn2-checkpoint-root1 fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-run-builds fn2-run-writers fn2-pool))
(defmacro fn2-checkpoint-root1-select-count-control (code)
 `(mv ,code fn2-checkpoint-root1 fn2-checkpoint-source fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-cursors fn2-pool))
(defmacro fn2-checkpoint-root1-bind-count-control (code)
 `(mv ,code fn2-checkpoint-page))
(defmacro fn2-checkpoint-root1-consume-count-control (code)
 `(mv ,code fn2-checkpoint-root1 fn2-digests))
(defmacro fn2-checkpoint-root1-work-count-control (code)
 `(mv ,code fn2-checkpoint-root1 fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-construction fn2-extents fn2-control fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
(defmacro fn2-checkpoint-root1-payload-start-count-control (code)
 `(mv ,code fn2-checkpoint-root1 fn2-checkpoint-retained-entry fn2-checkpoint-semantic fn2-checkpoint-payload fn2-digests fn2-b3 fn2-extents fn2-alloc-edges))
(defmacro fn2-checkpoint-root1-retention-count-control (code)
 `(mv ,code fn2-checkpoint-root1 fn2-checkpoint-metadata fn2-extents fn2-alloc-edges fn2-checkpoint-semantic))
(defmacro fn2-checkpoint-root1-closure-count-control (code)
 `(mv ,code fn2-checkpoint-root1 fn2-checkpoint-metadata-manifest fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-metadata fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests fn2-checkpoint-payload fn2-checkpoint-retained-entry fn2-checkpoint-refs fn2-checkpoint-bytes fn2-csnapshot))
(defmacro fn2-checkpoint-root1-read-count-control (code op-slot op-gen)
 `(mv ,code ,op-slot ,op-gen fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-metadata fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests fn2-checkpoint-payload))
(defmacro fn2-checkpoint-root1-step-count-control (code)
 `(mv ,code fn2-checkpoint-root1 fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-retained-entry fn2-checkpoint-payload fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-checkpoint-refs fn2-checkpoint-bytes fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
