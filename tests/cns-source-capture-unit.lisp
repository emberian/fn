; UNEXECUTED actual capture/allocator control. The semantic live READ row
; is an explicitly SYNTHETIC environment premise, not publication authority.
; Pool writes/copies, typed READ access and promised-read claim are actual.
(in-package "ACL2")
(include-book "../books/cns-source-capture")
(defun fn2-cns-source-capture-unit-body (fn2-cns-sources fn2-reads fn2-run-installed fn2-fields fn2-pool fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops)
 (declare (xargs :stobjs (fn2-cns-sources fn2-reads fn2-run-installed fn2-fields fn2-pool fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops) :verify-guards nil))
 (b* ((fn2-cns-sources (fn2-cns-sources-init 1 fn2-cns-sources))
      (fn2-reads (fn2-reads-init 1 fn2-reads))
      (fn2-run-installed (fn2-run-installed-init 1 fn2-run-installed))
      (fn2-fields (fn2-fields-init 128 fn2-fields))
      (fn2-pool (fn2-pool-init (list (cons 1 256) (cons 1 *fn2-cns-item-workspace-bytes*)) 1 100 fn2-pool))
      (fn2-checkpoints (fn2-checkpoints-init 1 fn2-checkpoints))
      (fn2-extents (fn2-alloc-init 2 fn2-extents))
      (fn2-alloc-edges (fn2-alloc-edges-init 512 fn2-alloc-edges))
      (fn2-ops (fn2-ops-init *fn2-profile-tiny* fn2-ops))
      ((mv begun fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents))
      ((mv reserved & extent epoch allocation fn2-extents) (fn2-alloc-reserve fn2-extents))
      ((mv committed fn2-extents) (fn2-alloc-commit-allocation extent epoch allocation 1 1 fn2-extents))
      ((mv a src sgen fn2-pool) (fn2-pool-reserve 0 7 11 13 fn2-pool))
      ((mv b lease lgen fn2-pool) (fn2-pool-reserve 1 9 17 19 fn2-pool))
      ((mv zero fn2-pool) (fn2-run-zero 128 src sgen 0 7 11 13 fn2-pool))
      ((mv w0 fn2-pool) (fn2-pool-write src sgen 0 17 7 11 13 fn2-pool))
      ((mv w1 fn2-pool) (fn2-pool-write src sgen 64 29 7 11 13 fn2-pool))
      ((mv w2 fn2-pool) (fn2-pool-write src sgen 96 43 7 11 13 fn2-pool))
      (fn2-reads (fn2-reads-put 0 (sid *fn2-article-sid*) (entry 1) (erow 0) (ek 7) (es 11) (eg 13) (ever (fn2-run-version *fn2-article-sid* 1 fn2-run-installed))))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-article* (value 7) (ref-len 0)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-state* (value *fn2-article-state-live*) (ref-len 0)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-version* (value 1) (ref-len 0)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-bytes* (value 6144) (ref-len 0)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-location-kind* (value *fn2-txn-location-raw-source*) (ref-len 0)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-location-unit* (value (* extent *fn2-storage-extent-units*)) (ref-len 0)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-location-epoch* (value epoch) (ref-len 0)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-location-allocation* (value allocation) (ref-len 0)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-location-hashes* (ref-slot src) (ref-gen sgen) (ref-off 0) (ref-len 64)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-source* (ref-slot src) (ref-gen sgen) (ref-off 64) (ref-len 32)))
      (fn2-fields (fn2-fields-put *fn2-article-entry-field-stored-source* (ref-slot src) (ref-gen sgen) (ref-off 96) (ref-len 32)))
      ; The old reset/vector/source recipe cannot jump over bytes64..95.
      ((mv old0 oc ol fn2-pool) (fn2-read-octets-children 0 *fn2-article-entry-field-location-hashes* 0 64 lease lgen 0 9 17 19 fn2-reads fn2-run-installed fn2-fields fn2-pool))
      ((mv old1 & & fn2-pool) (fn2-read-octets-children 0 *fn2-article-entry-field-source* 0 32 lease lgen *fn2-cns-source-original-offset* 9 17 19 fn2-reads fn2-run-installed fn2-fields fn2-pool))
      ((mv code total fn2-cns-sources fn2-pool fn2-extents fn2-alloc-edges)
       (fn2-cns-source-capture-children 0 17 19 23 29 31 0 lease lgen 9 fn2-cns-sources fn2-reads fn2-run-installed fn2-fields fn2-pool fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops))
      ((mv p0 v0) (fn2-pool-read lease lgen 0 9 17 19 fn2-pool))
      ((mv p1 v1) (fn2-pool-read lease lgen 64 9 17 19 fn2-pool))
      ((mv p2 v2) (fn2-pool-read lease lgen *fn2-cns-source-original-offset* 9 17 19 fn2-pool))
      ((mv p3 v3) (fn2-pool-read lease lgen *fn2-cns-source-stored-offset* 9 17 19 fn2-pool)))
  (mv (and (eq begun :ok) (eq reserved :ok) (eq committed :ok) (eq a :ok) (eq b :ok) (eq zero :ok)
           (eq w0 :ok) (eq w1 :ok) (eq w2 :ok) (eq old0 :ok) (equal oc 64) (equal ol 0) (eq old1 :bounds)
           (eq code :ok) (equal total 6144) (equal (fn2-pool-fill lease fn2-pool) *fn2-cns-source-prefix*)
           (eq p0 :ok) (equal v0 17) (eq p1 :ok) (equal v1 0) (eq p2 :ok) (equal v2 29) (eq p3 :ok) (equal v3 43)
           (equal (fn2-cns-sources-phase 0 fn2-cns-sources) *fn2-cns-source-phase-raw-read*)
           (fn2-cns-source-heldp 0 17 19 23 29 31 (* extent *fn2-storage-extent-units*) epoch allocation fn2-cns-sources fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops))
   fn2-cns-sources fn2-reads fn2-run-installed fn2-fields fn2-pool fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops)))
(defun fn2-cns-source-capture-unit ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-cns-sources
 (with-local-stobj fn2-reads
 (with-local-stobj fn2-run-installed
 (with-local-stobj fn2-fields
 (with-local-stobj fn2-pool
 (with-local-stobj fn2-checkpoints
 (with-local-stobj fn2-extents
 (with-local-stobj fn2-alloc-edges
 (with-local-stobj fn2-ops
 (mv-let (good fn2-cns-sources fn2-reads fn2-run-installed fn2-fields fn2-pool fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops) (fn2-cns-source-capture-unit-body fn2-cns-sources fn2-reads fn2-run-installed fn2-fields fn2-pool fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops) good)))))))))))
(assert-event (fn2-cns-source-capture-unit))
