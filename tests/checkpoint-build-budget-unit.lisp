; Real BEGIN/pack/bind budget controls with synthetic eligible root carriers.
; This isolates source binding, not a real C cut/root or generated IO witness.
; Configured physical37/41 deliberately differs from semantic101/103/107.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/checkpoint-build")
(defun fn2-checkpoint-budget-roots (role fn2-checkpoint-refs)
 (declare (xargs :stobjs fn2-checkpoint-refs :verify-guards nil :measure (nfix (- 6 (nfix role)))))
 (if (>= (nfix role) 6) fn2-checkpoint-refs
  (let ((fn2-checkpoint-refs (fn2-checkpoint-refs-put role (encoded-length 4096)
          (root-build-token 9) (root-source-complete 1) (root-intended-bytes 4096) (root-completed-bytes 4096))))
   (fn2-checkpoint-budget-roots (+ 1 role) fn2-checkpoint-refs))))

(defun fn2-checkpoint-budget-test-body (fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc fn2-checkpoint-page fn2-checkpoint-page-verified)
 (declare (xargs :stobjs (fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc fn2-checkpoint-page fn2-checkpoint-page-verified) :verify-guards nil))
 (b* ((fn2-checkpoint-build (fn2-checkpoint-build-init 1 fn2-checkpoint-build))
      (fn2-csnapshot (fn2-csnapshot-init 1 fn2-csnapshot))
      (fn2-checkpoints (fn2-checkpoints-init 1 fn2-checkpoints))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-init 6 fn2-checkpoint-refs))
      (fn2-checkpoint-bytes (fn2-checkpoint-bytes-init 192 fn2-checkpoint-bytes))
      (fn2-checkpoint-construction (fn2-checkpoint-construction-init 1 fn2-checkpoint-construction))
      (fn2-extents (fn2-alloc-init 1 fn2-extents))
      (fn2-pool (fn2-pool-init '((2 . 4096)) 1 100 fn2-pool))
      (fn2-control (fn2-control-columns-init 0 fn2-control))
      (fn2-fields (fn2-fields-init 1024 fn2-fields)) (fn2-fc (fn2-fc-init 4 fn2-fc))
      (fn2-checkpoint-page (fn2-checkpoint-page-init 1 fn2-checkpoint-page))
      (fn2-checkpoint-page-verified (fn2-checkpoint-page-verified-init 1 fn2-checkpoint-page-verified))
      ((mv epoch-code fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents))
      ((mv window slot gen fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
      ((mv scratch-code scratch sgen fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
      (fn2-csnapshot (fn2-csnapshot-put 0 (phase *fn2-csnapshot-phase-held*) (token 9)
        (owner-kind 1) (owner-slot 0) (owner-gen 1) (cut-commit 0) (cut-event 0) (complete 1)))
      ((mv begun fn2-checkpoint-build fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-control)
       (with-local-stobj fn2-origin
        (let ((fn2-origin (fn2-origin-prepare '((:origin-lineage . 101) (:origin-domain . 103) (:origin-incarnation . 107) (:history-id . 37) (:history-incarnation . 41)) fn2-origin)))
         (fn2-checkpoint-build-begin 1 0 9 slot gen scratch sgen 1 0 1
        fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-fc
        fn2-checkpoint-construction fn2-extents fn2-pool fn2-origin fn2-control))))
      (fn2-checkpoint-refs (fn2-checkpoint-budget-roots 1 fn2-checkpoint-refs))
      ((mv roots fn2-checkpoint-build) (fn2-checkpoint-build-roots-ready fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs))
      ((mv packed fn2-checkpoint-build fn2-fields fn2-pool)
       (fn2-checkpoint-build-pack fn2-checkpoint-build fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool))
      ((mv physical-header & fn2-fields)
       (fn2-format-page-header-decode 0 slot gen 0 4096 1 0 1 fn2-fields fn2-pool))
      (e (fn2-checkpoint-build-extent 0 fn2-checkpoint-build))
      (antecedent (and (eq epoch-code :ok) (eq window :ok) (eq scratch-code :ok) (eq begun :ok) (eq roots :ok) (eq packed :ok) (eq physical-header :ok)
                       (= (fn2-checkpoint-build-history 0 fn2-checkpoint-build) 37)
                       (= (fn2-checkpoint-build-history-incarnation 0 fn2-checkpoint-build) 41)
                       (= (fn2-checkpoints-history 0 fn2-checkpoints) 37)
                       (= (fn2-checkpoints-incarnation 0 fn2-checkpoints) 41)
                       (= (fn2-fields-value *fn2-format-page-header-field-history* fn2-fields) 37)
                       (= (fn2-fields-value *fn2-format-page-header-field-incarnation* fn2-fields) 41)
                       (not (= (fn2-fields-value *fn2-format-page-header-field-history* fn2-fields) 101))
                       (not (= (fn2-fields-value *fn2-format-page-header-field-incarnation* fn2-fields) 107))
                       (fn2-checkpoint-builder-ownerp 0 9 1 0 1 fn2-checkpoints)
                       (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-page*)
                       (equal (fn2-checkpoint-page-phase 0 fn2-checkpoint-page) *fn2-checkpoint-page-phase-idle*)
                       (equal (fn2-checkpoint-construction-completed-bytes e fn2-checkpoint-construction) 0)))
      ((mv zero fn2-checkpoint-build fn2-checkpoint-page)
       (fn2-checkpoint-build-bind-page 0 fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs
        fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-checkpoint-page-verified fn2-pool fn2-fc fn2-fields))
      (unchanged (and (eq zero :yield)
                      (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-page*)
                      (equal (fn2-checkpoint-page-phase 0 fn2-checkpoint-page) *fn2-checkpoint-page-phase-idle*)
                      (equal (fn2-pool-out-count slot fn2-pool) 0)))
      ((mv positive fn2-checkpoint-build fn2-checkpoint-page)
       (fn2-checkpoint-build-bind-page 1 fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs
        fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-checkpoint-page-verified fn2-pool fn2-fc fn2-fields)))
  (mv (and antecedent unchanged (eq positive :ok)
           (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-bound*)
           (equal (fn2-checkpoint-page-phase 0 fn2-checkpoint-page) *fn2-checkpoint-page-phase-context*)
           (equal (fn2-checkpoint-page-extent 0 fn2-checkpoint-page) e)
           (= (fn2-checkpoint-page-history 0 fn2-checkpoint-page) 37)
           (= (fn2-checkpoint-page-incarnation 0 fn2-checkpoint-page) 41)
           (equal (fn2-checkpoint-page-transferred 0 fn2-checkpoint-page) 0)
           (equal (fn2-pool-out-count slot fn2-pool) 0)
           (equal (fn2-checkpoint-construction-completed-bytes e fn2-checkpoint-construction) 0))
      fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc fn2-checkpoint-page fn2-checkpoint-page-verified)))

(defun fn2-checkpoint-budget-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoint-build
 (mv-let (answer fn2-checkpoint-build)
  (with-local-stobj fn2-csnapshot
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot)
  (with-local-stobj fn2-checkpoints
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints)
  (with-local-stobj fn2-checkpoint-refs
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs)
  (with-local-stobj fn2-checkpoint-bytes
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
  (with-local-stobj fn2-checkpoint-construction
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction)
  (with-local-stobj fn2-extents
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents)
  (with-local-stobj fn2-pool
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool)
  (with-local-stobj fn2-control
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control)
  (with-local-stobj fn2-fields
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields)
  (with-local-stobj fn2-fc
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc)
  (with-local-stobj fn2-checkpoint-page
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc fn2-checkpoint-page)
  (with-local-stobj fn2-checkpoint-page-verified
 (mv-let (answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc fn2-checkpoint-page fn2-checkpoint-page-verified)
  (fn2-checkpoint-budget-test-body fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc fn2-checkpoint-page fn2-checkpoint-page-verified)
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc fn2-checkpoint-page)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields fn2-fc)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control fn2-fields)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool fn2-control)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents fn2-pool)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction fn2-extents)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-construction)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs)))
  (mv answer fn2-checkpoint-build fn2-csnapshot fn2-checkpoints)))
  (mv answer fn2-checkpoint-build fn2-csnapshot)))
  (mv answer fn2-checkpoint-build)))
  answer)))
(assert-event (fn2-checkpoint-budget-test))
