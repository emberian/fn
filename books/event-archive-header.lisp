; Actual archive-header reservation, bounded packing and shared physical worker.
; Physical source completion remains distinct from B allocation/publication.
(in-package "ACL2")
(include-book "event-archive-manifest")
(include-book "checkpoint-page-header")
(include-book "checkpoint-map-build")
(fn2-book-layer :c)

(fn2-event-archive-operation fn2-event-archive-header-reserve
 (fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
  fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers
  fn2-checkpoint-construction fn2-extents fn2-control fn2-pool)
 (fn2-event-archive fn2-checkpoint-metadata fn2-checkpoint-construction fn2-extents fn2-control fn2-pool)
 (b* (((unless (and (fn2-event-archive-ownerp 1 fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build
                     fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers)
                    (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-header*)
                    (fn2-checkpoint-metadata-ownerp fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers)
                    (equal (fn2-checkpoint-metadata-phase 0 fn2-checkpoint-metadata) *fn2-checkpoint-metadata-phase-source-drained*)
                    (equal (fn2-checkpoint-metadata-held 0 fn2-checkpoint-metadata) 0)
                    (equal (fn2-event-archive-manifest-entries 1 fn2-event-archive) (fn2-event-archive-member-runs 1 fn2-event-archive))))
       (mv :source fn2-event-archive fn2-checkpoint-metadata fn2-checkpoint-construction fn2-extents fn2-control fn2-pool))
      (kind (fn2-event-archive-owner-kind 1 fn2-event-archive)) (owner (fn2-event-archive-owner-slot 1 fn2-event-archive))
      (gen (fn2-event-archive-owner-gen 1 fn2-event-archive))
      (ordinal (fn2-checkpoint-metadata-ordinal 0 fn2-checkpoint-metadata))
      (pages (+ (fn2-event-archive-member-pages 1 fn2-event-archive) (fn2-event-archive-manifest-pages 1 fn2-event-archive) 1))
      ((unless (and (equal (+ ordinal 1) pages) (unsigned-byte-p 60 pages) (unsigned-byte-p 60 (* pages *fn2-format-page-size*))))
       (mv :coverage fn2-event-archive fn2-checkpoint-metadata fn2-checkpoint-construction fn2-extents fn2-control fn2-pool))
      ((mv code page pgen & & & &) (fn2-checkpoint-root1-workspaces kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-event-archive fn2-checkpoint-metadata fn2-checkpoint-construction fn2-extents fn2-control fn2-pool))
      ((mv code e epoch allocation fn2-checkpoint-construction fn2-extents fn2-control)
       (fn2-checkpoint-construction-reserve (fn2-event-archive-token 1 fn2-event-archive) kind owner gen 3 ordinal *fn2-format-page-size*
        fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control))
      ((unless (eq code :ok))
       (let ((fn2-event-archive (if (eq code :uncertain) (fn2-event-archive-set-phase 1 *fn2-event-archive-phase-uncertain* fn2-event-archive) fn2-event-archive)))
        (mv code fn2-event-archive fn2-checkpoint-metadata fn2-checkpoint-construction fn2-extents fn2-control fn2-pool)))
      (fn2-event-archive (fn2-event-archive-put 1 (phase *fn2-event-archive-phase-uncertain*)
       (header-unit (* e *fn2-storage-extent-units*)) (header-epoch epoch) (header-allocation allocation)
       (header-ordinal ordinal) (header-slot page) (header-gen pgen) (header-zero 0) (header-payload 0) (source-pages pages)))
      (fn2-checkpoint-metadata (fn2-checkpoint-metadata-set-ordinal 0 (+ ordinal 1) fn2-checkpoint-metadata))
      ((mv code fn2-pool) (fn2-pool-reset page pgen kind owner gen fn2-pool))
      (fn2-event-archive (if (eq code :ok) (fn2-event-archive-set-phase 1 *fn2-event-archive-phase-header-zero* fn2-event-archive) fn2-event-archive)))
  (mv code fn2-event-archive fn2-checkpoint-metadata fn2-checkpoint-construction fn2-extents fn2-control fn2-pool)))

(fn2-event-archive-operation fn2-event-archive-header-zero-step
 (fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
  fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers fn2-pool)
 (fn2-event-archive fn2-pool)
 (b* (((unless (and (fn2-event-archive-ownerp 1 fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build
                     fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers)
                    (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-header-zero*)))
       (mv :source fn2-event-archive fn2-pool))
      (at (fn2-event-archive-header-zero 1 fn2-event-archive))
      ((unless (< at *fn2-format-page-size*)) (mv :bounds fn2-event-archive fn2-pool))
      (n (min 4096 (- *fn2-format-page-size* at)))
      ((mv code fn2-pool) (fn2-run-zero n (fn2-event-archive-header-slot 1 fn2-event-archive) (fn2-event-archive-header-gen 1 fn2-event-archive) at
        (fn2-event-archive-owner-kind 1 fn2-event-archive) (fn2-event-archive-owner-slot 1 fn2-event-archive)
        (fn2-event-archive-owner-gen 1 fn2-event-archive) fn2-pool))
      (next (+ at n))
      (fn2-event-archive (if (eq code :ok) (fn2-event-archive-put 1 (header-zero next)
        (phase (if (equal next *fn2-format-page-size*) *fn2-event-archive-phase-header-pack* *fn2-event-archive-phase-header-zero*))) fn2-event-archive)))
  (mv (if (eq code :ok) :more code) fn2-event-archive fn2-pool)))

(fn2-event-archive-operation fn2-event-archive-header-pack
 (fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
  fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers fn2-fc fn2-fields fn2-pool fn2-digests)
 (fn2-event-archive fn2-fields fn2-pool fn2-digests)
 (b* (((unless (and (fn2-event-archive-ownerp 1 fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build
                     fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers)
                    (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-header-pack*)
                    (equal (fn2-event-archive-header-zero 1 fn2-event-archive) *fn2-format-page-size*)
                    (posp (fn2-event-archive-manifest-height 1 fn2-event-archive))
                    (<= (fn2-event-archive-manifest-height 1 fn2-event-archive) *fn2-run-max-levels*)))
       (mv :source fn2-event-archive fn2-fields fn2-pool fn2-digests))
      (kind (fn2-event-archive-owner-kind 1 fn2-event-archive)) (owner (fn2-event-archive-owner-slot 1 fn2-event-archive)) (gen (fn2-event-archive-owner-gen 1 fn2-event-archive))
      ((mv code page pgen scratch sgen & &) (fn2-checkpoint-root1-workspaces kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool))
      ((unless (and (eq code :ok) (equal page (fn2-event-archive-header-slot 1 fn2-event-archive)) (equal pgen (fn2-event-archive-header-gen 1 fn2-event-archive))))
       (mv :window fn2-event-archive fn2-fields fn2-pool fn2-digests))
      (base (fn2-checkpoint-source-ebase (fn2-fc-rows fn2-fc)))
      (hash (fn2-run-builds-hbase *fn2-checkpoint-source-build* fn2-run-builds))
      ((unless (and (<= (+ base *fn2-event-archive-header-num-fields*) (fn2-fields-rows fn2-fields)) (fn2-digest-rowp hash fn2-digests)))
       (mv :bounds fn2-event-archive fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-pool) (fn2-pool-reset scratch sgen kind owner gen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-event-archive fn2-fields fn2-pool fn2-digests))
      (fn2-digests (fn2-event-archive-load-digest 1 :cut-seal 0 hash fn2-event-archive fn2-digests))
      ((mv code fn2-pool) (fn2-digest-store 32 hash scratch sgen 0 kind owner gen fn2-digests fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-event-archive fn2-fields fn2-pool fn2-digests))
      (fn2-digests (fn2-event-archive-load-digest 1 :manifest 0 hash fn2-event-archive fn2-digests))
      ((mv code fn2-pool) (fn2-digest-store 32 hash scratch sgen 32 kind owner gen fn2-digests fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-event-archive fn2-fields fn2-pool fn2-digests))
      (fn2-fields (fn2-event-archive-header-bind base *checkpoint-event-archive-kind-canonical-member-archive* 1
       (fn2-event-archive-checkpoint 1 fn2-event-archive) (fn2-event-archive-history 1 fn2-event-archive) (fn2-event-archive-incarnation 1 fn2-event-archive)
       (fn2-event-archive-cut-commit 1 fn2-event-archive) (fn2-event-archive-cut-event 1 fn2-event-archive) scratch sgen 0
       (fn2-event-archive-first-event 1 fn2-event-archive) (fn2-event-archive-last-event 1 fn2-event-archive) (fn2-event-archive-member-runs 1 fn2-event-archive)
       (fn2-event-archive-checkpoint 1 fn2-event-archive) (fn2-event-archive-manifest-height 1 fn2-event-archive) (fn2-event-archive-manifest-entries 1 fn2-event-archive)
       *fn2-checkpoint-served-storage-domain* (fn2-event-archive-manifest-unit 1 fn2-event-archive) (fn2-event-archive-manifest-epoch 1 fn2-event-archive)
       (fn2-event-archive-manifest-allocation 1 fn2-event-archive) *page-kind-manifest* *fn2-format-page-size* scratch sgen 32 fn2-fields))
      ((mv code next fn2-pool) (fn2-event-archive-header-encode base page pgen *fn2-event-archive-header-start* kind owner gen fn2-fields fn2-pool))
      (good (and (eq code :ok) (natp next) (<= *fn2-event-archive-header-start* next) (<= next *fn2-event-archive-header-limit*)))
      (fn2-event-archive (fn2-event-archive-put 1
       (phase (if good *fn2-event-archive-phase-header-seal* *fn2-event-archive-phase-uncertain*))
       (header-payload (if good (- next *fn2-checkpoint-page-header-area*) 0)))))
  (mv (if good :more (if (eq code :ok) :format code)) fn2-event-archive fn2-fields fn2-pool fn2-digests)))

(fn2-event-archive-operation fn2-event-archive-header-seal
 (fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
  fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers fn2-checkpoint-construction fn2-extents fn2-fc fn2-fields fn2-pool)
 (fn2-event-archive fn2-fields fn2-pool)
 (b* (((unless (and (fn2-event-archive-ownerp 1 fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build
                     fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers)
                    (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-header-seal*)))
       (mv :source fn2-event-archive fn2-fields fn2-pool))
      (base (fn2-checkpoint-source-ebase (fn2-fc-rows fn2-fc)))
      ((mv code fn2-fields fn2-pool) (fn2-checkpoint-page-pack-header (fn2-event-archive-token 1 fn2-event-archive)
        (fn2-event-archive-owner-kind 1 fn2-event-archive) (fn2-event-archive-owner-slot 1 fn2-event-archive)
        (fn2-event-archive-owner-gen 1 fn2-event-archive) 3 (fn2-event-archive-header-ordinal 1 fn2-event-archive)
        (floor (fn2-event-archive-header-unit 1 fn2-event-archive) *fn2-storage-extent-units*)
        (fn2-event-archive-header-epoch 1 fn2-event-archive) (fn2-event-archive-header-allocation 1 fn2-event-archive)
        *page-kind-manifest* (fn2-event-archive-history 1 fn2-event-archive) (fn2-event-archive-incarnation 1 fn2-event-archive)
        *fn2-format-page-size* (fn2-event-archive-header-payload 1 fn2-event-archive) base
        (fn2-event-archive-header-slot 1 fn2-event-archive) (fn2-event-archive-header-gen 1 fn2-event-archive)
        fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool))
      (fn2-event-archive (fn2-event-archive-set-phase 1 (if (eq code :ok) *fn2-event-archive-phase-page* *fn2-event-archive-phase-uncertain*) fn2-event-archive)))
  (mv (if (eq code :ok) :page code) fn2-event-archive fn2-fields fn2-pool)))

(fn2-event-archive-operation fn2-event-archive-header-bind-page
 (fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
  fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers fn2-checkpoint-page fn2-checkpoint-page-verified
  fn2-checkpoint-construction fn2-extents fn2-pool fn2-fc fn2-fields)
 (fn2-event-archive fn2-checkpoint-page)
 (b* (((unless (and (fn2-event-archive-ownerp 1 fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build
                     fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers)
                    (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-page*)))
       (mv :source fn2-event-archive fn2-checkpoint-page))
      ((mv code fn2-checkpoint-page) (fn2-checkpoint-page-begin (fn2-event-archive-token 1 fn2-event-archive)
        (fn2-event-archive-owner-kind 1 fn2-event-archive) (fn2-event-archive-owner-slot 1 fn2-event-archive)
        (fn2-event-archive-owner-gen 1 fn2-event-archive) 3 (fn2-event-archive-header-ordinal 1 fn2-event-archive)
        (floor (fn2-event-archive-header-unit 1 fn2-event-archive) *fn2-storage-extent-units*)
        (fn2-event-archive-header-epoch 1 fn2-event-archive) (fn2-event-archive-header-allocation 1 fn2-event-archive)
        (fn2-event-archive-header-slot 1 fn2-event-archive) (fn2-event-archive-header-gen 1 fn2-event-archive) *page-kind-manifest*
        (fn2-event-archive-history 1 fn2-event-archive) (fn2-event-archive-incarnation 1 fn2-event-archive) *fn2-format-page-size*
        fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-csnapshot fn2-extents fn2-pool fn2-fc fn2-fields))
      (fn2-event-archive (if (eq code :ok) (fn2-event-archive-set-phase 1 *fn2-event-archive-phase-bound* fn2-event-archive) fn2-event-archive)))
  (mv code fn2-event-archive fn2-checkpoint-page)))

; This terminal establishes only this concrete root3 source. Durability,
; selectable banks and historical/query/peer obligation transfer are separate.
(fn2-event-archive-operation fn2-event-archive-header-complete
 (fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
  fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-checkpoint-page
  fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-refs fn2-checkpoint-bytes fn2-pool)
 (fn2-event-archive fn2-checkpoint-refs fn2-checkpoint-bytes)
 (b* (((unless (and (fn2-event-archive-ownerp 1 fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build
                     fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers)
                    (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-bound*)))
       (mv :source fn2-event-archive fn2-checkpoint-refs fn2-checkpoint-bytes))
      (c (fn2-event-archive-candidate 1 fn2-event-archive)) (r (+ (* 6 c) 3))
      (token (fn2-event-archive-token 1 fn2-event-archive)) (kind (fn2-event-archive-owner-kind 1 fn2-event-archive))
      (owner (fn2-event-archive-owner-slot 1 fn2-event-archive)) (gen (fn2-event-archive-owner-gen 1 fn2-event-archive))
      (unit (fn2-event-archive-header-unit 1 fn2-event-archive)) (e (floor unit *fn2-storage-extent-units*))
      (pages (+ (fn2-event-archive-member-pages 1 fn2-event-archive) (fn2-event-archive-manifest-pages 1 fn2-event-archive) 1))
      (intended (* pages *fn2-format-page-size*))
      ((unless (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                    (equal (fn2-checkpoint-refs-root-source-complete r fn2-checkpoint-refs) 0)
                    (equal (fn2-checkpoint-refs-root-build-token r fn2-checkpoint-refs) 0)
                    (equal pages (fn2-event-archive-source-pages 1 fn2-event-archive))
                    (equal pages (fn2-checkpoint-metadata-ordinal 0 fn2-checkpoint-metadata))
                    (unsigned-byte-p 60 intended) (posp intended)
                    (equal (mod unit *fn2-storage-extent-units*) 0)
                    (fn2-checkpoint-page-completed-extent-p token kind owner gen 3 (fn2-event-archive-header-ordinal 1 fn2-event-archive) e
                     fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents)
                    (equal (fn2-checkpoint-page-verified-epoch e fn2-checkpoint-page-verified) (fn2-event-archive-header-epoch 1 fn2-event-archive))
                    (equal (fn2-checkpoint-page-verified-allocation e fn2-checkpoint-page-verified) (fn2-event-archive-header-allocation 1 fn2-event-archive))
                    (equal (fn2-checkpoint-page-verified-page-kind e fn2-checkpoint-page-verified) *page-kind-manifest*)
                    (equal (fn2-checkpoint-page-verified-history e fn2-checkpoint-page-verified) (fn2-event-archive-history 1 fn2-event-archive))
                    (equal (fn2-checkpoint-page-verified-incarnation e fn2-checkpoint-page-verified) (fn2-event-archive-incarnation 1 fn2-event-archive))
                    (equal (fn2-checkpoint-page-verified-encoded-length e fn2-checkpoint-page-verified) *fn2-format-page-size*)
                    (eq (fn2-pool-workspace-code (fn2-event-archive-header-slot 1 fn2-event-archive) (fn2-event-archive-header-gen 1 fn2-event-archive) kind owner gen fn2-pool) :ok)
                    (< 0 (fn2-checkpoint-page-rows fn2-checkpoint-page))
                    (or (not (equal (fn2-checkpoint-page-extent 0 fn2-checkpoint-page) e)) (equal (fn2-checkpoint-page-transferred 0 fn2-checkpoint-page) 0))))
       (mv :pending fn2-event-archive fn2-checkpoint-refs fn2-checkpoint-bytes))
      (fn2-checkpoint-bytes (fn2-checkpoint-map-root-hash-copy 32 0 e (* 32 r) fn2-checkpoint-page-verified fn2-checkpoint-bytes))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-put r (storage-domain *fn2-checkpoint-served-storage-domain*) (physical-unit unit)
       (writer-epoch (fn2-event-archive-header-epoch 1 fn2-event-archive)) (allocation (fn2-event-archive-header-allocation 1 fn2-event-archive))
       (page-kind *page-kind-manifest*) (encoded-length *fn2-format-page-size*) (edge 0) (retained 0)
       (root-build-token token) (root-source-complete 1) (root-intended-bytes intended) (root-completed-bytes intended)))
      (fn2-event-archive (fn2-event-archive-set-phase 1 *fn2-event-archive-phase-complete* fn2-event-archive)))
  (mv :complete fn2-event-archive fn2-checkpoint-refs fn2-checkpoint-bytes)))
