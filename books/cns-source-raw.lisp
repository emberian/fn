; Real source I/O is an actor transition. NEXT below only copies already
; verified and hashed bytes; it never issues or verifies a storage unit.
(in-package "ACL2")
(include-book "pool-copy")
(include-book "cns-source-workspace")
(include-book "cns-source-state")
(include-book "cns-source-hash")
(include-book "cns-source-retention")
(include-book "storage-block-io")
(include-book "machines-b")
(include-book "columns-call-guards")
(include-book "columns-observation-frames")
(fn2-book-layer :d)
(defcolumns fn2-cns-source-operations ((live :bool) (generation :u60) (source-row :u32)))

(defun fn2-cns-source-issue-children (s cns cnsgen ctl ctlgen request kind principal
 fn2-cns-sources fn2-cns-source-operations fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control fn2-checkpoints)
 (declare (xargs :stobjs (fn2-cns-sources fn2-cns-source-operations fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control fn2-checkpoints)
 :guard (and (fn2-cns-sources-wfp fn2-cns-sources) (fn2-cns-source-operations-wfp fn2-cns-source-operations)
 (fn2-checkpoints-wfp fn2-checkpoints) (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control))
 :guard-hints ((fn2-columns-call-guard-hint 'fn2-cns-source-issue-children
                '(fn2-pool-truncate fn2-block-read-children
                  fn2-cns-source-heldp fn2-pool-ownerp
                  fn2-cns-source-data-position-p) nil world))))
 (b* (((unless (and (fn2-cns-source-ownerp s cns cnsgen ctl ctlgen request fn2-cns-sources)
                    (equal kind (fn2-cns-sources-owner-kind s fn2-cns-sources))
                    (equal (fn2-cns-sources-pending s fn2-cns-sources) 0) (equal (fn2-cns-sources-borrow-count s fn2-cns-sources) 0)
                    (equal (fn2-cns-source-operations-rows fn2-cns-source-operations) (fn2-ops-rows fn2-ops))))
       (mv :bad 0 0 fn2-cns-sources fn2-cns-source-operations fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      (phase (fn2-cns-sources-phase s fn2-cns-sources))
      (stage (fn2-cns-sources-manifest-stage s fn2-cns-sources))
      (raw (equal phase *fn2-cns-source-phase-raw-read*))
      (manifest (and (equal phase *fn2-cns-source-phase-manifest*) (equal stage *fn2-cns-source-manifest-stage-read*)))
      (data (and (equal phase *fn2-cns-source-phase-manifest*) (equal stage *fn2-cns-source-manifest-stage-data-read*)))
      (at (if data *fn2-cns-source-data-offset* *fn2-cns-source-prefix*))
      (slot (fn2-cns-sources-lslot s fn2-cns-sources)) (gen (fn2-cns-sources-lgen s fn2-cns-sources))
      (len (if manifest *fn2-commit-unit-bytes*
             (if raw (min *fn2-commit-unit-bytes* (nfix (- (fn2-cns-sources-total s fn2-cns-sources) (fn2-cns-sources-offset s fn2-cns-sources))))
               (fn2-cns-sources-unit-length s fn2-cns-sources))))
      (unit (if manifest (+ (fn2-cns-sources-root-unit s fn2-cns-sources) (fn2-cns-sources-manifest-index s fn2-cns-sources))
             (if raw (+ (fn2-cns-sources-root-unit s fn2-cns-sources) (fn2-cns-sources-unit-index s fn2-cns-sources)) (fn2-cns-sources-unit s fn2-cns-sources))))
      (epoch (if data (fn2-cns-sources-epoch s fn2-cns-sources) (fn2-cns-sources-root-epoch s fn2-cns-sources)))
      (allocation (if data (fn2-cns-sources-allocation s fn2-cns-sources) (fn2-cns-sources-root-allocation s fn2-cns-sources)))
      (o (fn2-ops-free-head fn2-ops))
      ((unless (and (or raw manifest data)
                    (equal (fn2-cns-sources-uncertain s fn2-cns-sources) 0)
                    (fn2-cns-source-heldp s cns cnsgen ctl ctlgen request unit epoch allocation fn2-cns-sources fn2-checkpoints fn2-extents fn2-alloc-edges fn2-ops)
                    (if manifest t (equal (fn2-cns-sources-retention-phase s fn2-cns-sources) *fn2-cns-source-retention-ready*))
                    (posp len) (<= len *fn2-commit-unit-bytes*)
                    (if data (fn2-cns-source-data-position-p s fn2-cns-sources) t)
                    (if raw (and (equal (fn2-cns-sources-location-kind s fn2-cns-sources) 0)
                                 (equal (fn2-cns-sources-offset s fn2-cns-sources) (* *fn2-commit-unit-bytes* (fn2-cns-sources-unit-index s fn2-cns-sources)))
                                 (equal (fn2-cns-sources-offset s fn2-cns-sources) (fn2-cns-sources-hash-offset s fn2-cns-sources))) t)
                    (eq (fn2-pool-workspace-code slot gen kind cns cnsgen fn2-pool) :ok)
                    (<= at (fn2-pool-fill slot fn2-pool))
                    (fn2-op-slotp o fn2-ops) (< o (fn2-cns-source-operations-rows fn2-cns-source-operations))
                    (equal (fn2-cns-source-operations-live o fn2-cns-source-operations) 0)))
       (mv :wait 0 0 fn2-cns-sources fn2-cns-source-operations fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      ((mv trim fn2-pool) (fn2-pool-truncate slot gen at kind cns cnsgen fn2-pool))
      ((mv code op opgen fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)
       (if (eq trim :ok) (fn2-block-read-children unit epoch allocation 0 len slot gen kind cns cnsgen principal fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
        (mv :bounds 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)))
      ((unless (eq code :ok))
       (let ((fn2-cns-sources (if (equal (fn2-control-stop fn2-control) 1)
              (fn2-cns-sources-put s (phase *fn2-cns-source-phase-bad*) (uncertain 1)) fn2-cns-sources)))
        (mv (if (and (eq code :exhausted) (equal (fn2-control-stop fn2-control) 0)) :wait :bad) op opgen fn2-cns-sources fn2-cns-source-operations fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)))
      (fn2-cns-source-operations (fn2-cns-source-operations-put op (live 1) (generation opgen) (source-row s)))
      (fn2-cns-sources (let* ((fn2-cns-sources (fn2-cns-sources-put s (pending 1) (op-slot op) (op-gen opgen) (unit-length len) (unit-copied 0) (unit-hashed 0) (phase (if raw *fn2-cns-source-phase-raw-wait* phase))))
        (fn2-cns-sources (cond (manifest (fn2-cns-sources-put s (manifest-stage *fn2-cns-source-manifest-stage-wait*))) (data (fn2-cns-sources-put s (manifest-stage *fn2-cns-source-manifest-stage-data-wait*))) (t fn2-cns-sources))))
   fn2-cns-sources)))
  (mv :ok op opgen fn2-cns-sources fn2-cns-source-operations fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)))

(defun fn2-cns-source-harvest (op opgen cell event outcome reason count aux0 aux1 fn2-cns-sources fn2-cns-source-operations)
 (declare (xargs :stobjs (fn2-cns-sources fn2-cns-source-operations)
 :guard (and (fn2-cns-sources-wfp fn2-cns-sources) (fn2-cns-source-operations-wfp fn2-cns-source-operations))) (ignore aux0 aux1))
 (b* (((unless (and (natp op) (< op (fn2-cns-source-operations-rows fn2-cns-source-operations))
                    (equal (fn2-cns-source-operations-live op fn2-cns-source-operations) 1)
                    (equal opgen (fn2-cns-source-operations-generation op fn2-cns-source-operations))
                    (equal cell 0) (equal event *fn2-event-read-result*)))
       (mv :ok fn2-cns-sources fn2-cns-source-operations))
      (s (fn2-cns-source-operations-source-row op fn2-cns-source-operations))
      ((unless (and (< s (fn2-cns-sources-rows fn2-cns-sources)) (equal (fn2-cns-sources-pending s fn2-cns-sources) 1)
                    (equal op (fn2-cns-sources-op-slot s fn2-cns-sources)) (equal opgen (fn2-cns-sources-op-gen s fn2-cns-sources))
                    (unsigned-byte-p 8 event) (unsigned-byte-p 8 outcome) (unsigned-byte-p 8 reason) (unsigned-byte-p 32 count)))
       (mv :ok fn2-cns-sources fn2-cns-source-operations))
      (stage (fn2-cns-sources-manifest-stage s fn2-cns-sources))
      (fn2-cns-sources (let* ((fn2-cns-sources (fn2-cns-sources-put s (pending 0) (result-kind event) (result-outcome outcome) (result-reason reason) (result-count count)))
        (fn2-cns-sources (if (equal (fn2-cns-sources-phase s fn2-cns-sources) *fn2-cns-source-phase-raw-wait*) (fn2-cns-sources-put s (phase *fn2-cns-source-phase-raw-check*)) fn2-cns-sources))
        (fn2-cns-sources (cond ((equal stage *fn2-cns-source-manifest-stage-wait*) (fn2-cns-sources-put s (manifest-stage *fn2-cns-source-manifest-stage-check*))) ((equal stage *fn2-cns-source-manifest-stage-data-wait*) (fn2-cns-sources-put s (manifest-stage *fn2-cns-source-manifest-stage-data-check*))) (t fn2-cns-sources))))
   fn2-cns-sources))
      (fn2-cns-source-operations (fn2-cns-source-operations-set-live op 0 fn2-cns-source-operations)))
  (mv :ok fn2-cns-sources fn2-cns-source-operations)))

; Actor-only verification/hashing/finalization. This function never queues IO.
(defcolumns-observation-frame fn2-cns-sources-hash-offset-after-unit-hashed
 fn2-cns-sources hash-offset unit-hashed)

(defun fn2-cns-source-raw-step-children (s cns cnsgen ctl ctlgen request kind connections budget fn2-cns-sources fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-cns-sources fn2-b3 fn2-digests fn2-pool)
 :guard (and (fn2-cns-sources-wfp fn2-cns-sources) (fn2-b3-wfp fn2-b3) (fn2-digests-wfp fn2-digests) (fn2-pool-wfp fn2-pool))
 :guard-hints ((fn2-columns-call-guard-hint 'fn2-cns-source-raw-step-children
                '(fn2-pool-workspace-code fn2-block-read-commitment-children
                  fn2-cns-source-hash-begin fn2-cns-source-hash-update
                  fn2-cns-source-hash-finish)
                nil world))))
 (b* (((unless (and (fn2-cns-source-ownerp s cns cnsgen ctl ctlgen request fn2-cns-sources)
                    (equal kind (fn2-cns-sources-owner-kind s fn2-cns-sources))
                    (equal (fn2-cns-sources-pending s fn2-cns-sources) 0) (equal (fn2-cns-sources-borrow-count s fn2-cns-sources) 0)
                    (fn2-b-cns-source-geometry-p (fn2-cns-sources-rows fn2-cns-sources) connections (fn2-b3-rows fn2-b3))))
       (mv :bad fn2-cns-sources fn2-b3 fn2-digests))
      ((unless (posp budget)) (mv :wait fn2-cns-sources fn2-b3 fn2-digests))
      (slot (fn2-cns-sources-lslot s fn2-cns-sources)) (gen (fn2-cns-sources-lgen s fn2-cns-sources))
      ((unless (eq (fn2-pool-workspace-code slot gen kind cns cnsgen fn2-pool) :ok))
       (mv :wait fn2-cns-sources fn2-b3 fn2-digests))
      (phase (fn2-cns-sources-phase s fn2-cns-sources))
      (row (fn2-b-cns-source-row s (fn2-cns-sources-rows fn2-cns-sources) (fn2-b3-rows fn2-b3)))
      ((when (equal phase *fn2-cns-source-phase-raw-check*))
       (b* (((unless (<= *fn2-commit-unit-bytes* budget)) (mv :wait fn2-cns-sources fn2-b3 fn2-digests))
            (len (fn2-cns-sources-unit-length s fn2-cns-sources))
            (good-result (and (equal (fn2-cns-sources-result-kind s fn2-cns-sources) *fn2-event-read-result*)
                              (equal (fn2-cns-sources-result-outcome s fn2-cns-sources) *fn2-outcome-done*)
                              (equal (fn2-cns-sources-result-reason s fn2-cns-sources) *fn2-reason-none*)))
            ((mv code fn2-b3 fn2-digests)
             (if (and good-result (<= *fn2-commit-unit-bytes* budget)
                      (equal (fn2-cns-sources-location-kind s fn2-cns-sources) 0)
                      (< (* 32 (fn2-cns-sources-unit-index s fn2-cns-sources)) (fn2-cns-sources-hashes s fn2-cns-sources)))
              (fn2-block-read-commitment-children (fn2-cns-sources-result-count s fn2-cns-sources) len slot gen *fn2-cns-source-prefix*
               slot gen (* 32 (fn2-cns-sources-unit-index s fn2-cns-sources)) kind cns cnsgen fn2-b3 fn2-digests fn2-pool)
              (mv  :bad fn2-b3 fn2-digests)))
            (fn2-cns-sources (if (eq code :wait) fn2-cns-sources
             (fn2-cns-sources-set-phase s (if (eq code :ok) *fn2-cns-source-phase-raw-hash* *fn2-cns-source-phase-bad*) fn2-cns-sources))))
        (mv (cond ((eq code :ok) :more) ((eq code :wait) :wait) (t :bad)) fn2-cns-sources fn2-b3 fn2-digests)))
      ((when (equal phase *fn2-cns-source-phase-raw-hash*))
       (b* (((when (equal (fn2-cns-sources-hash-phase s fn2-cns-sources) 0))
             (b* (((mv code fn2-b3 fn2-digests) (fn2-cns-source-hash-begin row fn2-b3 fn2-digests))
                  (fn2-cns-sources (if (eq code :ok) (fn2-cns-sources-set-hash-phase s 1 fn2-cns-sources)
                                    (fn2-cns-sources-set-phase s *fn2-cns-source-phase-bad* fn2-cns-sources))))
              (mv (if (eq code :ok) :more :bad) fn2-cns-sources fn2-b3 fn2-digests)))
            (hashed (fn2-cns-sources-unit-hashed s fn2-cns-sources)) (len (fn2-cns-sources-unit-length s fn2-cns-sources))
            (base (if (equal (fn2-cns-sources-location-kind s fn2-cns-sources) 0) *fn2-cns-source-prefix* *fn2-cns-source-data-offset*))
            ((unless (and (<= hashed len) (< 0 len)
                           (<= (+ (fn2-cns-sources-hash-offset s fn2-cns-sources) (- len hashed)) (fn2-cns-sources-total s fn2-cns-sources))))
             (mv :bad fn2-cns-sources fn2-b3 fn2-digests))
            ((when (equal hashed len))
             (let ((fn2-cns-sources (fn2-cns-sources-set-phase s *fn2-cns-source-phase-raw-copy* fn2-cns-sources)))
              (mv :ready fn2-cns-sources fn2-b3 fn2-digests)))
            (n (min (min 1024 budget) (- len hashed)))
            ((mv code used fn2-b3 fn2-digests) (fn2-cns-source-hash-update row slot gen (+ base hashed) n kind cns cnsgen fn2-b3 fn2-digests fn2-pool))
            ((unless (and (member-eq code '(:ok :more)) (posp used) (<= used n)))
             (let ((fn2-cns-sources (fn2-cns-sources-set-phase s *fn2-cns-source-phase-bad* fn2-cns-sources)))
              (mv :bad fn2-cns-sources fn2-b3 fn2-digests)))
            (fn2-cns-sources (fn2-cns-sources-put s (unit-hashed (+ hashed used)) (hash-offset (+ (fn2-cns-sources-hash-offset s fn2-cns-sources) used)))))
        (mv :more fn2-cns-sources fn2-b3 fn2-digests)))
      ((when (equal phase *fn2-cns-source-phase-final*))
       (b* (((unless (and (equal (fn2-cns-sources-offset s fn2-cns-sources) (fn2-cns-sources-total s fn2-cns-sources))
                           (equal (fn2-cns-sources-hash-offset s fn2-cns-sources) (fn2-cns-sources-total s fn2-cns-sources))
                           (equal (fn2-cns-sources-hash-phase s fn2-cns-sources) 1)))
             (mv :bad fn2-cns-sources fn2-b3 fn2-digests))
            ((mv code fn2-b3 fn2-digests) (fn2-cns-source-hash-finish row slot gen *fn2-cns-source-stored-offset* kind cns cnsgen fn2-b3 fn2-digests fn2-pool))
            (fn2-cns-sources (fn2-cns-sources-set-phase s (if (eq code :ok) *fn2-cns-source-phase-complete* *fn2-cns-source-phase-bad*) fn2-cns-sources)))
        (mv (if (eq code :ok) :complete :bad) fn2-cns-sources fn2-b3 fn2-digests))))
  (mv (cond ((equal phase *fn2-cns-source-phase-raw-read*) :need-read)
            ((equal phase *fn2-cns-source-phase-raw-copy*) :ready)
            ((equal phase *fn2-cns-source-phase-complete*) :complete)
            ((equal phase *fn2-cns-source-phase-bad*) :bad) (t :wait)) fn2-cns-sources fn2-b3 fn2-digests)))


(defcolumns-observation-frame fn2-cns-sources-manifest-index-after-offset fn2-cns-sources manifest-index offset)
(defcolumns-observation-frame fn2-cns-sources-manifest-index-after-unit-copied fn2-cns-sources manifest-index unit-copied)
(defcolumns-observation-frame fn2-cns-sources-manifest-index-after-unit-index fn2-cns-sources manifest-index unit-index)
(defcolumns-observation-frame fn2-cns-sources-manifest-loaded-index-after-manifest-index fn2-cns-sources manifest-loaded-index manifest-index)
(defcolumns-observation-frame fn2-cns-sources-manifest-loaded-index-after-offset fn2-cns-sources manifest-loaded-index offset)
(defcolumns-observation-frame fn2-cns-sources-manifest-loaded-index-after-unit-copied fn2-cns-sources manifest-loaded-index unit-copied)
(defcolumns-observation-frame fn2-cns-sources-manifest-loaded-index-after-unit-index fn2-cns-sources manifest-loaded-index unit-index)
(defcolumns-observation-frame fn2-cns-sources-total-after-manifest-index fn2-cns-sources total manifest-index)
(defcolumns-observation-frame fn2-cns-sources-total-after-manifest-stage fn2-cns-sources total manifest-stage)
(defcolumns-observation-frame fn2-cns-sources-total-after-offset fn2-cns-sources total offset)
(defcolumns-observation-frame fn2-cns-sources-total-after-unit-copied fn2-cns-sources total unit-copied)
(defcolumns-observation-frame fn2-cns-sources-total-after-unit-index fn2-cns-sources total unit-index)
(defcolumns-observation-frame fn2-cns-sources-unit-index-after-offset fn2-cns-sources unit-index offset)
(defcolumns-observation-frame fn2-cns-sources-unit-index-after-unit-copied fn2-cns-sources unit-index unit-copied)

(defun fn2-cns-source-next-children (s cns cnsgen ctl ctlgen request slot gen off maximum ctlkind fn2-cns-sources fn2-pool)
 (declare (xargs :stobjs (fn2-cns-sources fn2-pool) :guard (and (fn2-cns-sources-wfp fn2-cns-sources) (fn2-pool-wfp fn2-pool))
 :guard-hints ((fn2-columns-call-guard-hint 'fn2-cns-source-next-children
   '(fn2-rd-copy fn2-pool-ownerp) nil world))))
 (b* (((unless (and (fn2-cns-source-ownerp s cns cnsgen ctl ctlgen request fn2-cns-sources)
                    (natp maximum) (<= maximum 1024) (natp off)))
       (mv :bad 0 nil fn2-cns-sources fn2-pool))
      ((when (equal (fn2-cns-sources-phase s fn2-cns-sources) *fn2-cns-source-phase-complete*))
       (if (and (equal (fn2-cns-sources-offset s fn2-cns-sources) (fn2-cns-sources-total s fn2-cns-sources))
                (equal (fn2-cns-sources-hash-offset s fn2-cns-sources) (fn2-cns-sources-total s fn2-cns-sources))
                (equal (fn2-cns-sources-uncertain s fn2-cns-sources) 0)
                (equal (fn2-cns-sources-pending s fn2-cns-sources) 0)
                (eq (fn2-pool-workspace-code (fn2-cns-sources-lslot s fn2-cns-sources) (fn2-cns-sources-lgen s fn2-cns-sources)
                     (fn2-cns-sources-owner-kind s fn2-cns-sources) cns cnsgen fn2-pool) :ok))
        (mv :ok 0 t fn2-cns-sources fn2-pool) (mv :bad 0 nil fn2-cns-sources fn2-pool)))
      ((unless (and (equal (fn2-cns-sources-phase s fn2-cns-sources) *fn2-cns-source-phase-raw-copy*) (posp maximum)
                    (equal (fn2-cns-sources-pending s fn2-cns-sources) 0) (equal (fn2-cns-sources-borrow-count s fn2-cns-sources) 0)
                    (equal (fn2-cns-sources-unit-hashed s fn2-cns-sources) (fn2-cns-sources-unit-length s fn2-cns-sources))))
       (mv (if (equal (fn2-cns-sources-phase s fn2-cns-sources) *fn2-cns-source-phase-bad*) :bad :wait) 0 nil fn2-cns-sources fn2-pool))
      (kind (fn2-cns-sources-owner-kind s fn2-cns-sources))
      (source (fn2-cns-sources-lslot s fn2-cns-sources)) (sgen (fn2-cns-sources-lgen s fn2-cns-sources))
      (copied (fn2-cns-sources-unit-copied s fn2-cns-sources)) (len (fn2-cns-sources-unit-length s fn2-cns-sources))
      ((unless (and (< copied len) (not (equal source slot))
                    (equal (fn2-cns-sources-hash-offset s fn2-cns-sources) (+ (fn2-cns-sources-offset s fn2-cns-sources) (- len copied)))
                    (<= (+ (fn2-cns-sources-offset s fn2-cns-sources) (min maximum (- len copied))) (fn2-cns-sources-total s fn2-cns-sources))
                    (eq (fn2-pool-workspace-code source sgen kind cns cnsgen fn2-pool) :ok)
                    (eq (fn2-pool-workspace-code slot gen ctlkind ctl ctlgen fn2-pool) :ok)
                    (equal off (fn2-pool-fill slot fn2-pool))
                    (<= (+ off (min maximum (- len copied))) (fn2-pool-cap slot fn2-pool))
                    (<= (+ (if (equal (fn2-cns-sources-location-kind s fn2-cns-sources) 0) *fn2-cns-source-prefix* *fn2-cns-source-data-offset*)
                           copied (min maximum (- len copied))) (fn2-pool-fill source fn2-pool))))
       (mv :bad 0 nil fn2-cns-sources fn2-pool))
      (n (min maximum (- len copied)))
      ((unless (unsigned-byte-p 32 (+ 1 (fn2-cns-sources-unit-index s fn2-cns-sources))))
       (mv :bad 0 nil fn2-cns-sources fn2-pool))
      (base (if (equal (fn2-cns-sources-location-kind s fn2-cns-sources) 0) *fn2-cns-source-prefix* *fn2-cns-source-data-offset*))
      ((mv code fn2-pool) (fn2-rd-copy n source sgen (+ base copied) kind cns cnsgen slot gen off ctlkind ctl ctlgen fn2-pool))
      ((unless (eq code :ok))
       (let ((fn2-cns-sources (fn2-cns-sources-set-phase s *fn2-cns-source-phase-bad* fn2-cns-sources)))
        (mv :bad 0 nil fn2-cns-sources fn2-pool)))
      (offset (+ (fn2-cns-sources-offset s fn2-cns-sources) n))
      (done (equal (+ copied n) len))
      (raw (equal (fn2-cns-sources-location-kind s fn2-cns-sources) 0))
      (next-index (floor (fn2-cns-sources-manifest-position s fn2-cns-sources) *fn2-commit-unit-bytes*))
      (fn2-cns-sources (let* ((fn2-cns-sources (fn2-cns-sources-put s (offset offset) (unit-copied (+ copied n)) (unit-index (if done (+ 1 (fn2-cns-sources-unit-index s fn2-cns-sources)) (fn2-cns-sources-unit-index s fn2-cns-sources))) (manifest-index (if (and done (not raw)) next-index (fn2-cns-sources-manifest-index s fn2-cns-sources)))))
        (fn2-cns-sources (if (and done (not raw)) (fn2-cns-sources-put s (manifest-stage (if (equal next-index (fn2-cns-sources-manifest-loaded-index s fn2-cns-sources)) *fn2-cns-source-manifest-stage-entry* *fn2-cns-source-manifest-stage-read*))) fn2-cns-sources))
        (fn2-cns-sources (fn2-cns-sources-put s (phase (cond ((equal offset (fn2-cns-sources-total s fn2-cns-sources)) *fn2-cns-source-phase-final*)
                    (done (if raw *fn2-cns-source-phase-raw-read* *fn2-cns-source-phase-manifest*)) (t *fn2-cns-source-phase-raw-copy*))))))
   fn2-cns-sources)))
  (mv :ok n nil fn2-cns-sources fn2-pool)))

; Pinned reads may record a stop and add or drop a pin. Their public
; row frames compose the fixed-size updates on these paths.
(local
 (fn2-control-preserves fn2-control-record-stop (reason fn2-control)
  :specs (("-ROWS" fn2-control-rows nil :frame fn2-control))
  :disable nil
  :hints (("Goal" :in-theory (e/d (fn2-control-record-stop fn2-control-rows
                                   update-fn2-control-stop update-fn2-control-stop-reason)
                                  (fn2-control-stop))))))

(local
 (fn2-control-preserves fn2-issue-children
  (kind cap-index cap-nonce offset fua slot gen off len may-release target-slot
   target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)
  :specs (("-CONTROL-ROWS" fn2-control-rows 5 :frame fn2-control))
  :disable nil
  :hints ((fn2-columns-call-guard-hint 'fn2-issue-children
           '(fn2-control-record-stop fn2-op-reserve fn2-op-unreserve fn2-core-lease
             fn2-op-set-range fn2-op-set-capability fn2-op-set-storage
             fn2-op-set-cancel-target fn2-op-enqueue)
           '(fn2-issue-children) world))))

(local
 (fn2-extents-preserves fn2-b-read-pin-drop (opslot opgen fn2-extents fn2-alloc-edges)
  :specs (("-EXTENTS-ROWS" fn2-extents-rows 1 :frame fn2-extents)
          ("-EDGES-ROWS" fn2-alloc-edges-rows 2 :frame fn2-alloc-edges))
  :disable nil
  :hints ((fn2-columns-call-guard-hint 'fn2-b-read-pin-drop
           '(fn2-b-read-pin-edge fn2-alloc-edge-slotp fn2-alloc-edge-drop)
           '(fn2-b-read-pin-drop) world))))

(local
 (fn2-control-preserves fn2-block-read-children
  (pu epoch alloc off len lslot lgen okind oslot ogen principal
   fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
  :specs (("-CONTROL-ROWS" fn2-control-rows 5 :frame fn2-control)
          ("-EXTENTS-ROWS" fn2-extents-rows 6 :frame fn2-extents)
          ("-EDGES-ROWS" fn2-alloc-edges-rows 7 :frame fn2-alloc-edges))
  :disable nil
  :hints ((fn2-columns-call-guard-hint 'fn2-block-read-children
           '(fn2-control-record-stop fn2-issue-children fn2-alloc-handle-code
             fn2-alloc-edge-add fn2-b-read-pin-drop fn2-b-read-pin-edge
             fn2-op-slotp fn2-ops-free-head fn2-ops-gen)
           '(fn2-block-read-children fn2-pinned-block-io-children
             fn2-issue-read-children) world))))

(local
 (defthm fn2-cns-source-ownerp-row-bound
  (implies (fn2-cns-source-ownerp s cns cnsgen ctl ctlgen request fn2-cns-sources)
   (and (natp s) (< s (fn2-cns-sources-rows fn2-cns-sources))))
  :hints (("Goal" :in-theory (enable fn2-cns-source-ownerp)))
  :rule-classes :forward-chaining))

(local
 (defthm fn2-op-slotp-row-bound
  (implies (fn2-op-slotp op fn2-ops)
   (and (natp op) (< op (fn2-ops-rows fn2-ops))))
  :hints (("Goal" :in-theory (enable fn2-op-slotp)))
  :rule-classes :forward-chaining))

(fn2-cns-source-frames fn2-cns-source-issue-children
 (s cns cnsgen ctl ctlgen request kind principal fn2-cns-sources fn2-cns-source-operations fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control fn2-checkpoints)
 (fn2-cns-sources fn2-cns-source-operations fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control fn2-checkpoints)
 ((fn2-cns-sources 3) (fn2-cns-source-operations 4) (fn2-pool 5) (fn2-ops 6) (fn2-control 7) (fn2-extents 8) (fn2-alloc-edges 9))
 ((fn2-columns-call-guard-hint 'fn2-cns-source-issue-children
   '(fn2-block-read-children fn2-pool-truncate fn2-rd-copy
     fn2-cns-source-ownerp fn2-op-slotp min
     fn2-cns-source-heldp fn2-cns-source-retain-ownerp
     fn2-cns-source-data-position-p fn2-pool-workspace-code
     fn2-pool-ownerp fn2-alloc-edge-matchesp fn2-alloc-handle-code)
   '(fn2-cns-source-issue-children) world)))
(fn2-cns-source-frames fn2-cns-source-harvest
 (op opgen cell event outcome reason count aux0 aux1 fn2-cns-sources fn2-cns-source-operations)
 (fn2-cns-sources fn2-cns-source-operations)
 ((fn2-cns-sources 1) (fn2-cns-source-operations 2))
 ((fn2-columns-call-guard-hint 'fn2-cns-source-harvest
   '(fn2-block-read-children fn2-pool-truncate fn2-rd-copy
     fn2-cns-source-heldp fn2-cns-source-retain-ownerp
     fn2-cns-source-data-position-p fn2-pool-workspace-code
     fn2-pool-ownerp fn2-alloc-edge-matchesp fn2-alloc-handle-code)
   '(fn2-cns-source-harvest) world)))
(local (fn2-hash-row-frames fn2-block-read-commitment-children fn2-b3 fn2-digests))

(fn2-cns-source-frames fn2-cns-source-raw-step-children
 (s cns cnsgen ctl ctlgen request kind connections budget fn2-cns-sources fn2-b3 fn2-digests fn2-pool)
 (fn2-cns-sources fn2-b3 fn2-digests fn2-pool)
 ((fn2-cns-sources 1) (fn2-b3 2) (fn2-digests 3))
 ((fn2-columns-call-guard-hint 'fn2-cns-source-raw-step-children
   '(fn2-cns-source-hash-begin fn2-cns-source-hash-update
     fn2-cns-source-hash-finish fn2-block-read-commitment-children
     fn2-block-read-children fn2-pool-truncate fn2-rd-copy
     fn2-cns-source-heldp fn2-cns-source-retain-ownerp
     fn2-cns-source-data-position-p fn2-pool-workspace-code
     fn2-pool-ownerp fn2-alloc-edge-matchesp fn2-alloc-handle-code)
   '(fn2-cns-source-raw-step-children) world)))
(fn2-cns-source-frames fn2-cns-source-next-children
 (s cns cnsgen ctl ctlgen request slot gen off maximum ctlkind fn2-cns-sources fn2-pool)
 (fn2-cns-sources fn2-pool)
 ((fn2-cns-sources 3) (fn2-pool 4))
 ((fn2-columns-call-guard-hint 'fn2-cns-source-next-children
   '(fn2-block-read-children fn2-pool-truncate fn2-rd-copy
     fn2-cns-source-heldp fn2-cns-source-retain-ownerp
     fn2-cns-source-data-position-p fn2-pool-workspace-code
     fn2-pool-ownerp fn2-alloc-edge-matchesp fn2-alloc-handle-code)
   '(fn2-cns-source-next-children) world)))
