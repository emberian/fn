; Actual factory -> encoded pending page -> real page seal/check -> linked
; decoder controls. The reused producer fixture explicitly supplies SYNTHETIC
; held-C and historical E authentication premises. This is not autonomous
; checkpoint entry, a persisted checkpoint, or selected-recovery acceptance.
; No inventory/event COMPLETE or physical-completion field is written here.
;
; The missing full private path is concrete: fn2-rrc-producer obtains a real
; Fenced PERSISTED RELEASE; produce a SECOND checkpoint while that target is
; pending, crash with fn2-ccp-restart, then run actual boot/root3 journal-step
; through root4 and inventory. The current shared fn2-ccp-maintenance-entry
; explicitly seeds CATALOG because activation is NIL. That entry is not an
; admission witness. Original R/J tuple facts must come from their real image
; reads; they are not fabricated to make inventory ENTRY accept in this unit.
(in-package "ACL2")
(include-book "release-inventory-producer-unit")
(include-book "../books/checkpoint-restore-read")

(defun fn2-rier-format (sealp length slot gen fn2-release-inventory-build fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (ignore fn2-release-inventory-build)
  (xargs :stobjs (fn2-release-inventory-build fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) :verify-guards nil))
 (fn2-format-drive (fn2-format-fuel length) 0 :page sealp slot gen 0 length 0 1 2 3 4096
  fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))

(defun fn2-rier-body (mode fn2-release-inventory-build fn2-release-evidence fn2-release-evidence-candidates fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified fn2-fc fn2-fields fn2-pool fn2-control fn2-allocation-release fn2-checkpoint-page fn2-fc-context fn2-b3 fn2-digests)
 (declare (xargs :stobjs (fn2-release-inventory-build fn2-release-evidence fn2-release-evidence-candidates fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified fn2-fc fn2-fields fn2-pool fn2-control fn2-allocation-release fn2-checkpoint-page fn2-fc-context fn2-b3 fn2-digests) :verify-guards nil))
 (b* (((mv produced fn2-release-inventory-build fn2-release-evidence fn2-release-evidence-candidates fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified fn2-fc fn2-fields fn2-pool fn2-control fn2-allocation-release fn2-checkpoint-page)
       (fn2-ripu-body nil fn2-release-inventory-build fn2-release-evidence fn2-release-evidence-candidates fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified fn2-fc fn2-fields fn2-pool fn2-control fn2-allocation-release fn2-checkpoint-page))
      (slot (fn2-release-inventory-build-slot 0 fn2-release-inventory-build))
      (gen (fn2-release-inventory-build-gen 0 fn2-release-inventory-build))
      (extent (fn2-release-inventory-build-extent 0 fn2-release-inventory-build))
      (history (fn2-release-inventory-build-history 0 fn2-release-inventory-build))
      (incarnation (fn2-release-inventory-build-incarnation 0 fn2-release-inventory-build))
      (rows (fn2-fc-rows fn2-fc))
      (fn2-fc-context (fn2-fc-context-init rows fn2-fc-context))
      (fn2-b3 (fn2-b3-table-init rows fn2-b3))
      (fn2-digests (fn2-digests-init (* *fn2-digest-stride* rows) fn2-digests))
      (fn2-fc-context (fn2-fc-context-put 0
       (location (* extent *fn2-storage-extent-units*))
       (writer-epoch (fn2-release-inventory-build-epoch 0 fn2-release-inventory-build))
       (allocation (fn2-release-inventory-build-allocation 0 fn2-release-inventory-build))
       (history history) (incarnation incarnation) (page-kind *page-kind-merkle-node*)
       (encoded-length *fn2-format-page-size*)
       (hash (fn2-digest-slot 0 *fn2-fc-hash*)) (geometry (fn2-digest-slot 0 *fn2-fc-geometry*))
       (previous-seal (fn2-digest-slot 0 *fn2-fc-previous-seal*))))
      (row 0) (base 0) (off 0) (len *fn2-format-page-size*)
      (whole-antecedent (and produced (fn2-fc-guard)
       (fn2-fcp fn2-fc) (fn2-fc-contextp fn2-fc-context) (fn2-b3p fn2-b3) (fn2-digestsp fn2-digests)
       (fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool)
       (= (fn2-release-inventory-build-phase 0 fn2-release-inventory-build) *fn2-release-inventory-build-phase-bound*)
       (= (fn2-release-inventory-build-count 0 fn2-release-inventory-build) 1)
       (= (fn2-checkpoint-page-phase 0 fn2-checkpoint-page) *fn2-checkpoint-page-phase-context*)
       (= (fn2-checkpoint-page-pending 0 fn2-checkpoint-page) 0)
       (not (fn2-release-inventory-complete-p fn2-release-inventory-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified))))
      ((unless whole-antecedent) (mv nil fn2-release-inventory-build fn2-release-evidence fn2-release-evidence-candidates fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified fn2-fc fn2-fields fn2-pool fn2-control fn2-allocation-release fn2-checkpoint-page fn2-fc-context fn2-b3 fn2-digests))
      ((mv sealed fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-rier-format t len slot gen fn2-release-inventory-build fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv verified fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-rier-format nil len slot gen fn2-release-inventory-build fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv header fn2-fields) (fn2-checkpoint-restore-header 6 4 9 1 0 0 slot gen 1 2 3 fn2-fields fn2-pool))
      ((mv decoded actual-end fn2-fields) (fn2-release-inventory-entry-decode 0 slot gen *fn2-checkpoint-map-entries-start*
       (+ *fn2-checkpoint-map-entries-start* *fn2-release-inventory-entry-width*) 1 2 3 fn2-fields fn2-pool))
      ((mv entry fn2-fields) (fn2-checkpoint-restore-entry 6 0 0 slot gen 1 2 3 fn2-fields fn2-pool))
      (tuple (and (eq decoded :ok) (eq entry :entry)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-journal-extent* fn2-fields) 2)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-commit* fn2-fields) 4)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-event* fn2-fields) 9)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-extent* fn2-fields) 3)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-journal-history* fn2-fields) 101)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-journal-incarnation* fn2-fields) 103)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-installation-history* fn2-fields) 29)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-installation-incarnation* fn2-fields) 31)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-history* fn2-fields) 37)
       (= (fn2-fields-value *fn2-release-inventory-entry-field-incarnation* fn2-fields) 41)))
      (original-page (fn2-pool-logical-octets len (fn2-pool-base slot fn2-pool) fn2-pool))
      ; Change only expected physical namespace: actual FORMAT verifies it
      ; against producer bytes, independent of the pending entry namespaces.
      (fn2-fc-context (fn2-fc-context-set-history 0 (+ history 1) fn2-fc-context))
      ((mv wrong-history fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-rier-format nil len slot gen fn2-release-inventory-build fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      (fn2-fc-context (fn2-fc-context-set-history 0 history fn2-fc-context))
      (fn2-fc-context (fn2-fc-context-set-incarnation 0 (+ incarnation 1) fn2-fc-context))
      ((mv wrong-incarnation fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-rier-format nil len slot gen fn2-release-inventory-build fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      (fn2-fc-context (fn2-fc-context-set-incarnation 0 incarnation fn2-fc-context))
      ((mv short-page fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-rier-format nil (- len 1) slot gen fn2-release-inventory-build fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv truncated & fn2-fields) (fn2-release-inventory-entry-decode 0 slot gen *fn2-checkpoint-map-entries-start*
       (- actual-end 1) 1 2 3 fn2-fields fn2-pool))
      (refusal-frame (equal original-page (fn2-pool-logical-octets len (fn2-pool-base slot fn2-pool) fn2-pool)))
      ((mv fault fn2-fields fn2-pool)
       (case mode
        (:count
         (b* (((mv parsed & fn2-fields) (fn2-checkpoint-map-header-decode 0 slot gen *fn2-checkpoint-map-body-start* *fn2-checkpoint-map-entries-start* 1 2 3 fn2-fields fn2-pool))
              (fn2-fields (fn2-fields-set-value *fn2-checkpoint-map-header-field-entry-count* 2 fn2-fields))
              ((mv encoded & fn2-pool) (fn2-checkpoint-map-header-encode 0 slot gen *fn2-checkpoint-map-body-start* 1 2 3 fn2-fields fn2-pool))
              ((mv rejected fn2-fields) (fn2-checkpoint-restore-header 6 4 9 1 0 0 slot gen 1 2 3 fn2-fields fn2-pool)))
          (mv (and (eq parsed :ok) (eq encoded :ok) (eq rejected :coverage)) fn2-fields fn2-pool)))
        (:namespace
         (b* (((mv parsed & fn2-fields) (fn2-release-inventory-entry-decode 0 slot gen *fn2-checkpoint-map-entries-start*
                (+ *fn2-checkpoint-map-entries-start* *fn2-release-inventory-entry-width*) 1 2 3 fn2-fields fn2-pool))
              ; Substitute the covering descriptor's namespace for original R.
              ; Both are one-byte varints: this is a same-length substitution.
              (fn2-fields (fn2-fields-set-value *fn2-release-inventory-entry-field-journal-history*
                (fn2-fields-value *fn2-release-inventory-entry-field-history* fn2-fields) fn2-fields))
              ((mv encoded next fn2-pool) (fn2-release-inventory-entry-encode 0 slot gen *fn2-checkpoint-map-entries-start* 1 2 3 fn2-fields fn2-pool))
              ((mv reread & fn2-fields) (fn2-release-inventory-entry-decode 0 slot gen *fn2-checkpoint-map-entries-start*
                (+ *fn2-checkpoint-map-entries-start* *fn2-release-inventory-entry-width*) 1 2 3 fn2-fields fn2-pool)))
          (mv (and (eq parsed :ok) (eq encoded :ok) (= next actual-end) (eq reread :ok)
               (= (fn2-fields-value *fn2-release-inventory-entry-field-journal-history* fn2-fields) 37)
               (not (= (fn2-fields-value *fn2-release-inventory-entry-field-journal-history* fn2-fields)
                       (fn2-release-evidence-journal-history 2 fn2-release-evidence)))) fn2-fields fn2-pool)))
        (otherwise (mv (eq mode :clean) fn2-fields fn2-pool))))
      ((mv final-check fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-rier-format nil len slot gen fn2-release-inventory-build fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (mv (and whole-antecedent (eq sealed :ok) (eq verified :ok) (eq header :ok) tuple
       (eq wrong-history :wrong-history) (eq wrong-incarnation :wrong-incarnation)
       (eq short-page :wrong-length) (eq truncated :truncated) refusal-frame fault
       (if (eq mode :clean)
           (equal original-page (fn2-pool-logical-octets len (fn2-pool-base slot fn2-pool) fn2-pool))
         (not (equal original-page (fn2-pool-logical-octets len (fn2-pool-base slot fn2-pool) fn2-pool))))
       (if (eq mode :clean) (eq final-check :ok) (eq final-check :bad-hash))
       (= (fn2-release-inventory-build-phase 0 fn2-release-inventory-build) *fn2-release-inventory-build-phase-bound*)
       (= (fn2-checkpoint-page-phase 0 fn2-checkpoint-page) *fn2-checkpoint-page-phase-context*)
       (not (fn2-release-inventory-complete-p fn2-release-inventory-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified)))
   fn2-release-inventory-build fn2-release-evidence fn2-release-evidence-candidates fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified fn2-fc fn2-fields fn2-pool fn2-control fn2-allocation-release fn2-checkpoint-page fn2-fc-context fn2-b3 fn2-digests)))
(defun fn2-rier-test (mode)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-release-inventory-build fn2-release-evidence fn2-release-evidence-candidates fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified fn2-fc fn2-fields fn2-pool fn2-control fn2-allocation-release fn2-checkpoint-page fn2-fc-context fn2-b3 fn2-digests)
  (fn2-rier-body mode fn2-release-inventory-build fn2-release-evidence fn2-release-evidence-candidates fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified fn2-fc fn2-fields fn2-pool fn2-control fn2-allocation-release fn2-checkpoint-page fn2-fc-context fn2-b3 fn2-digests)))
(assert-event (fn2-rier-test :clean))
(assert-event (fn2-rier-test :count))
(assert-event (fn2-rier-test :namespace))
