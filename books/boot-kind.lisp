; Image startup's declaration. Configuration is a trusted startup input;
; external image octets stay in bounded pool windows and are never read as Lisp.
(in-package "ACL2")
(include-book "machines-b")
(include-book "machine-arms")
(include-book "checkpoint-geometry")
(include-book "checkpoint-restore-reader")
(include-book "checkpoint-restore-map")
(include-book "checkpoint-recovery-evidence-state")
(include-book "checkpoint-recovery-census-state")
(include-book "checkpoint-selected-source-state")
(include-book "checkpoint-projection-state")
(include-book "checkpoint-suffix-allocation")
(include-book "checkpoint-restore-arena")
(include-book "checkpoint-restore-semantic-state")
(include-book "checkpoint-restore-events-state")
(include-book "checkpoint-summary-state")
(include-book "checkpoint-payload-harvest")
(include-book "checkpoint-restore-events-state")
(include-book "boot-format")
(fn2-book-layer :b)

; Only startup configuration has a list cursor. It advances one group per
; visit, is cleared before ready, and never contains parsed device data.
; Its resident measure (T10) is declared at the boot record's widths: each of
; the COUNT genesis groups as a name at the identity field's 250 octets (the
; most fn2-boot-pack-pool writes) and a u60 value in 8 bytes; the path at
; *fn2-profile-path-identity-max* octets. COUNT is fixed at init, so the
; measure is too while the cursor advances.
(defconst *fn2-boot-group-entry-bytes* (+ 250 8))
(defcolumns fn2-boot-config nil :init-name fn2-boot-config-empty
 :extra-fields
 ((fn2-boot-config-checkpoint-layout-ready :type (unsigned-byte 1) :initially 0 :why "Set only after checked bootstrap/empty anchor scan and the final startup fence.")
  (fn2-boot-config-image-size :type (unsigned-byte 60) :initially 0 :why "Actual image size checked by ACL2 startup geometry.")
  (fn2-boot-config-geometry :type (array (unsigned-byte 8) (32)) :initially 0 :why "Owned bootstrap geometry hash; not checker scratch.")
  (fn2-boot-config-anchor-checked-mask :type (unsigned-byte 8) :initially 0 :why "Actual per-slot anchor authentication results; retained separately from empty and malformed sectors.")
  (fn2-boot-config-anchor-empty-mask :type (unsigned-byte 8) :initially 0 :why "Actual canonical-zero anchor sectors observed during this cold scan.")
  (fn2-boot-config-anchor-invalid-mask :type (unsigned-byte 8) :initially 0 :why "Observed nonempty anchor failures remain explicit census evidence; never silently relabelled empty.")
  (fn2-boot-config-arena-mask :type (unsigned-byte 8) :initially 0 :why "Per-anchor authenticated arena tuple/uniqueness evidence only; never selected-base authority.")
  (fn2-boot-config-map-fifo-mask :type (unsigned-byte 8) :initially 0 :why "Per-anchor allocation-map/FIFO investigation evidence only; never a selected-base or serving bit.")
  (fn2-boot-config-anchor-evidence :type (array (unsigned-byte 8) (384)) :initially 0 :why "Three checked digests per physical anchor slot: batch, predecessor, anchor hash; retained across rx window reuse.")
  (fn2-boot-config-groups :type t :initially nil :why "Unconsumed trusted startup group configuration; one group per boot visit."
   :resident (* *fn2-boot-group-entry-bytes* (fn2-boot-config-count fn2-boot-config)))
  (fn2-boot-config-path :type t :initially nil :why "Trusted startup path identity, checked against the immutable image record."
   :resident *fn2-profile-path-identity-max*)
  (fn2-boot-config-count :type (unsigned-byte 32) :initially 0 :why "Number of immutable genesis group records.")
  (fn2-boot-config-extents :type (unsigned-byte 32) :initially 0 :why "The image's arena geometry, checked before recovery.")
  (fn2-boot-config-owner :type (unsigned-byte 32) :initially 0 :why "Persisted initial owner account binding.")
  (fn2-boot-config-recovery-assumptions :type (unsigned-byte 8) :initially 2 :why "Declared startup storage fault contract; never inferred from image bytes.")
  (fn2-boot-config-authority :type (unsigned-byte 1) :initially 0 :why "Whether genesis includes the principal directory.")))

(defun fn2-boot-config-prepare (profile fn2-boot-config)
 (declare (xargs :stobjs fn2-boot-config :guard t))
 (let* ((fn2-boot-config (fn2-boot-config-empty 0 fn2-boot-config))
        (groups (fn2-profile-get :groups profile))
        (extents (fn2-b-capacity :extent-slots 16 profile))
        (owner (fn2-profile-get :owner-account profile)))
  (if (not (fn2-profile-get :image-boot profile)) fn2-boot-config
   (let* ((fn2-boot-config (update-fn2-boot-config-groups groups fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-recovery-assumptions (fn2-profile-recovery-assumptions profile) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-path (fn2-profile-path-identity profile) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-count (if (unsigned-byte-p 32 (len groups)) (len groups) 0) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-extents (if (unsigned-byte-p 32 extents) extents 0) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-owner (if (and (posp owner) (unsigned-byte-p 32 owner)) owner 1) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-authority (if (posp (nfix (fn2-profile-get :authority profile))) 1 0) fn2-boot-config)))
     fn2-boot-config))))
(defthm fn2-boot-config-prepare-type
 (implies (fn2-boot-configp fn2-boot-config)
          (fn2-boot-configp (fn2-boot-config-prepare profile fn2-boot-config)))
 :hints (("Goal" :in-theory (disable fn2-profile-recovery-assumptions fn2-profile-get
                                    fn2-profile-path-identity unsigned-byte-p posp nfix))))
(defthm fn2-boot-config-prepare-wfp (fn2-boot-config-wfp (fn2-boot-config-prepare profile fn2-boot-config))
 :hints (("Goal" :in-theory (disable fn2-profile-recovery-assumptions fn2-profile-get
                                    fn2-profile-path-identity unsigned-byte-p posp nfix))))
(defthm fn2-boot-config-prepare-recovery-assumptions
 (implies (fn2-profile-get :image-boot profile)
  (equal (fn2-boot-config-recovery-assumptions (fn2-boot-config-prepare profile fn2-boot-config))
         (fn2-profile-recovery-assumptions profile)))
 :hints (("Goal" :in-theory (disable fn2-profile-recovery-assumptions fn2-profile-get
                                    fn2-profile-path-identity unsigned-byte-p posp nfix))))
(in-theory (disable fn2-boot-config-prepare))
(defcorechild fn2-core-boot-config fn2-boot-config
 :init (fn2-boot-config-prepare profile fn2-boot-config)
 :profilep (unsigned-byte-p 32 (len (fn2-profile-get :groups profile)))
 :why "Immutable genesis verification advances a trusted configuration cursor before serving.")

(defcorechild fn2-core-checkpoint-restore-reader fn2-checkpoint-restore-reader
 :init (fn2-checkpoint-restore-reader-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-restore-reader)
 :profilep t
 :why "Boot holds one authenticated checkpoint page and exact entry cursor while rebuilding candidate roots; this child grants no serving authority.")

(defcorechild fn2-core-checkpoint-restore-map fn2-checkpoint-restore-map
 :init (fn2-checkpoint-restore-map-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-map)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "One exact wire allocation-map row per actual arena extent; candidate investigation cannot mutate the live allocator.")
(defcorechild fn2-core-checkpoint-restore-map-control fn2-checkpoint-restore-map-control
 :init (fn2-checkpoint-restore-map-control-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-restore-map-control)
 :profilep t
 :why "Exact intake cursor and bounded FIFO investigation remain bound to their actual anchor candidate.")

(defcorechild fn2-core-checkpoint-restore-reach fn2-checkpoint-restore-reach
 :init (fn2-checkpoint-restore-reach-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-reach)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "One tagged identity and typed protection union per extent, shared by every cold root and payload alias.")
(defcorechild fn2-core-checkpoint-restore-reach-control fn2-checkpoint-restore-reach-control
 :init (fn2-checkpoint-restore-reach-control-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-restore-reach-control)
 :profilep t
 :why "A nonwrapping investigation generation binds every cold reach to the same authenticated descriptor and map intake.")

(defcorechild fn2-core-checkpoint-restore-events fn2-checkpoint-restore-events
 :init (fn2-checkpoint-restore-events-init 2 fn2-checkpoint-restore-events)
 :profilep t
 :why "Scratch row0 and retained row1 give cold investigation and live canonical archive distinct lifetimes, including nonimage startup.")
(defcorechild fn2-core-checkpoint-restore-events-work fn2-checkpoint-restore-events-work
 :init (fn2-checkpoint-restore-events-work-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-events-work)
 :profilep (and (unsigned-byte-p 32 (* 2 (fn2-b-capacity :extent-slots 16 profile)))
                (unsigned-byte-p 32 (* 64 (fn2-b-capacity :extent-slots 16 profile))))
 :why "Two charged stripes of the same journal-source layout: cold scratch and retained selected catalog; each follows actual extent capacity.")

(defcorechild fn2-core-checkpoint-restore-arena fn2-checkpoint-restore-arena
 :init (fn2-checkpoint-restore-arena-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-arena)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "Exact ordered journal scan targets are distinct extents in the authenticated candidate map.")
(defcorechild fn2-core-checkpoint-restore-arena-marks fn2-checkpoint-restore-arena-marks
 :init (fn2-checkpoint-restore-arena-marks-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-arena-marks)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "Generation-tagged extent uniqueness rejects repeated arena tickets without whole-ledger clearing.")
(defcorechild fn2-core-checkpoint-restore-arena-control fn2-checkpoint-restore-arena-control
 :init (fn2-checkpoint-restore-arena-control-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-restore-arena-control)
 :profilep t
 :why "One candidate-bound ordered arena intake cursor; no live allocator authority.")

(defcorechild fn2-core-checkpoint-restore-semantic fn2-checkpoint-restore-semantic
 :init (fn2-checkpoint-restore-semantic-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-restore-semantic)
 :profilep t
 :why "One exact descriptor-bound cold semantic page reader; no selected-base or live allocator authority.")

(defcorechild fn2-core-checkpoint-summary fn2-checkpoint-summary
 :init (fn2-checkpoint-summary-init (if (fn2-profile-get :image-boot profile) 2 0) fn2-checkpoint-summary)
 :profilep t :why "Exact selected-source catalog intake and bounded C adoption; capture alone is not sufficient-summary authority.")
(defcorechild fn2-core-checkpoint-selected-source fn2-checkpoint-selected-source
 :init (fn2-checkpoint-selected-source-init 1 fn2-checkpoint-selected-source)
 :profilep t :why "Owner-bound chosen cold source; re-investigation precedes allocator projection and serving authority.")
(defcorechild fn2-core-checkpoint-projection fn2-checkpoint-projection
 :init (fn2-checkpoint-projection-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-projection)
 :profilep t :why "One owner-bound cold map/FIFO/protection cursor; phase4 remains closed through suffix reconstruction.")
(defcorechild fn2-core-checkpoint-suffix-allocation fn2-checkpoint-suffix-allocation
 :init (fn2-checkpoint-suffix-allocation-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-suffix-allocation)
 :profilep t :why "One actual authenticated cold replay allocation holds a bounded FREE predecessor cursor while phase4 remains closed.")
(defcorechild fn2-core-checkpoint-summary-sources fn2-checkpoint-summary-sources
 :init (fn2-checkpoint-summary-sources-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-summary-sources)
 :profilep t :why "One authenticated C source root per actual physical extent, tagged by exact descriptor investigation.")
(defcorechild fn2-core-checkpoint-restore-semantic-work fn2-checkpoint-restore-semantic-work
 :init (fn2-checkpoint-restore-semantic-work-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-semantic-work)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "Tagged exact authenticated semantic page targets, one row per physical extent; no live edge or serving authority.")

(defcorechild fn2-core-checkpoint-payload fn2-checkpoint-payload
 :init (fn2-checkpoint-payload-init 1 fn2-checkpoint-payload)
 :profilep t
 :why "One canonical payload continuation: concrete binders choose live/cold ownership only after prior physical work settles."
 :harvest (fn2-checkpoint-payload-harvest-children
  ((fn2-core-checkpoint-payload fn2-checkpoint-payload) (fn2-core-ops fn2-ops))))

(defcorechild fn2-core-checkpoint-recovery-evidence fn2-checkpoint-recovery-evidence
 :init (fn2-checkpoint-recovery-evidence-init 5 fn2-checkpoint-recovery-evidence) :profilep t
 :why "One bounded cold journal investigation and evidence for each of the four physical anchors; no base selection.")

(defcorechild fn2-core-checkpoint-recovery-census fn2-checkpoint-recovery-census
 :init (fn2-checkpoint-recovery-census-init (if (fn2-profile-get :image-boot profile) 1 0) fn2-checkpoint-recovery-census)
 :profilep t
 :why "One bounded census rebinds retained installation evidence and observed anchor ancestry; semantic roots remain owed and no base is selected.")

(defmachine fn2-boot
 :states (:free :prepare :write :write-result :read :read-result :verify :advance
          :anchor :bootstrap :bootstrap-verify :checkpoint-anchor :checkpoint-check :checkpoint-descriptor :checkpoint-verify :checkpoint-root-candidate :checkpoint-root-reserve :checkpoint-root-begin :checkpoint-root-load :checkpoint-root-copy :checkpoint-root-verify :checkpoint-root-dispatch :checkpoint-root-padding :checkpoint-root-next :checkpoint-root-finish :checkpoint-root-fifo :checkpoint-evidence-begin :checkpoint-evidence-target :checkpoint-evidence-load :checkpoint-evidence-copy :checkpoint-evidence-check :checkpoint-evidence-record :checkpoint-evidence-next :checkpoint-semantic-begin :checkpoint-semantic-load :checkpoint-semantic-copy :checkpoint-semantic-check :checkpoint-summary-capture :checkpoint-semantic-entries :checkpoint-semantic-find :checkpoint-summary-close :checkpoint-payload-begin :checkpoint-payload-load :checkpoint-payload-copy :checkpoint-payload-step :checkpoint-census :recover :recover-wait :epoch :epoch-fence :epoch-result :release :ready :failed
         :checkpoint-events-begin :checkpoint-events-journal-bind :checkpoint-events-journal-load :checkpoint-events-journal-received :checkpoint-events-journal-check :checkpoint-events-frontier-begin :checkpoint-events-frontier-check :checkpoint-events-frontier-peaks :checkpoint-events-frontier-padding :checkpoint-events-frontier-finish :checkpoint-events-finish :checkpoint-events-seed :checkpoint-project-begin :checkpoint-project-step :checkpoint-project-protect :checkpoint-cbase-acquire :checkpoint-adopt-begin :checkpoint-adopt-preflight :checkpoint-adopt-copy :checkpoint-authority-begin :checkpoint-authority-copy :checkpoint-directory-install :checkpoint-catalog-begin :checkpoint-catalog-copy :genesis-begin :genesis-step)
 :fields ((pending :u32) (stopped :bool) (pool-slot :u32) (pool-gen :u60)
          (rx-slot :u32) (rx-gen :u60) (create :bool) (image-size :u60)
          (base :u60) (total :u32) (index :u32) (stage :u8) (offset :u60)
          (checkpoint-index :u8) (checkpoint-length :u32) (checkpoint-seen :bool) (root-role :u8) (root-slot :u32) (root-gen :u60) (root-cursor :u32) (epoch0 :u60) (epoch1 :u60) (next-epoch :u60) (anchor-slot :bool)
          (event-ready :bool) (outcome :u8) (count :u32) (release-index :u32) (read-length :u32))
 :holds ((:prepare :storage-window) (:write :storage-window) (:write-result :storage-window)
         (:read :storage-window) (:read-result :storage-window) (:verify :storage-window)
         (:advance :storage-window) (:anchor :storage-window)
         (:bootstrap :storage-window) (:bootstrap-verify :storage-window)
         (:checkpoint-anchor :storage-window) (:checkpoint-check :storage-window) (:checkpoint-descriptor :storage-window) (:checkpoint-verify :storage-window)
         (:checkpoint-root-candidate :storage-window) (:checkpoint-root-reserve :storage-window) (:checkpoint-root-begin :storage-window) (:checkpoint-root-load :storage-window) (:checkpoint-root-copy :storage-window) (:checkpoint-root-verify :storage-window) (:checkpoint-root-dispatch :storage-window) (:checkpoint-root-padding :storage-window) (:checkpoint-root-next :storage-window) (:checkpoint-root-finish :storage-window) (:checkpoint-root-fifo :storage-window)
         (:checkpoint-evidence-begin :storage-window)
         (:checkpoint-evidence-target :storage-window)
         (:checkpoint-evidence-load :storage-window)
         (:checkpoint-evidence-copy :storage-window)
         (:checkpoint-evidence-check :storage-window)
         (:checkpoint-evidence-record :storage-window)
         (:checkpoint-evidence-next :storage-window)
         (:checkpoint-semantic-begin :storage-window)
         (:checkpoint-semantic-load :storage-window)
         (:checkpoint-semantic-copy :storage-window)
         (:checkpoint-semantic-check :storage-window)
         (:checkpoint-summary-capture :storage-window)
         (:checkpoint-summary-close :storage-window)
         (:checkpoint-semantic-entries :storage-window)
         (:checkpoint-semantic-find :storage-window)
         (:checkpoint-payload-begin :storage-window)
         (:checkpoint-payload-load :storage-window)
         (:checkpoint-payload-copy :storage-window)
         (:checkpoint-payload-step :storage-window)
         (:checkpoint-census :storage-window) (:recover :storage-window)
         (:recover-wait :storage-window) (:epoch :storage-window) (:epoch-fence :storage-window)
         (:epoch-result :storage-window)
         (:checkpoint-events-begin :storage-window)
         (:checkpoint-events-journal-bind :storage-window)
         (:checkpoint-events-journal-load :storage-window)
         (:checkpoint-events-journal-received :storage-window)
         (:checkpoint-events-journal-check :storage-window)
         (:checkpoint-events-frontier-begin :storage-window)
         (:checkpoint-events-frontier-check :storage-window)
         (:checkpoint-events-frontier-peaks :storage-window)
         (:checkpoint-events-frontier-padding :storage-window)
         (:checkpoint-events-frontier-finish :storage-window)
         (:checkpoint-events-finish :storage-window)
         (:checkpoint-events-seed :storage-window)
         (:checkpoint-project-begin :storage-window)
         (:checkpoint-project-step :storage-window)
         (:checkpoint-project-protect :storage-window)
         (:checkpoint-cbase-acquire :storage-window)
         (:checkpoint-adopt-begin :storage-window)
         (:checkpoint-adopt-preflight :storage-window)
         (:checkpoint-adopt-copy :storage-window)
         (:checkpoint-authority-begin :storage-window)
         (:checkpoint-authority-copy :storage-window)
         (:checkpoint-directory-install :storage-window)
         (:checkpoint-catalog-begin :storage-window)
         (:checkpoint-catalog-copy :storage-window)
         (:genesis-begin :storage-window)
         (:genesis-step :storage-window))
 :budget (:bytes 32768 :steps 32 :descriptors 4)
 :stops (:geometry :configuration :io :anchor :checkpoint :recovery :epoch :bounds)
 :capacity (if (fn2-profile-get :image-boot profile) 1 0)
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free) (:prepare) (:write) (:write-result) (:read) (:read-result) (:verify) (:advance)
        (:anchor) (:bootstrap) (:bootstrap-verify) (:checkpoint-anchor) (:checkpoint-check) (:checkpoint-descriptor) (:checkpoint-verify) (:checkpoint-root-candidate) (:checkpoint-root-reserve) (:checkpoint-root-begin) (:checkpoint-root-load) (:checkpoint-root-copy) (:checkpoint-root-verify) (:checkpoint-root-dispatch) (:checkpoint-root-padding) (:checkpoint-root-next) (:checkpoint-root-finish) (:checkpoint-root-fifo)
        (:checkpoint-evidence-begin)
        (:checkpoint-evidence-target)
        (:checkpoint-evidence-load)
        (:checkpoint-evidence-copy)
        (:checkpoint-evidence-check)
        (:checkpoint-evidence-record)
        (:checkpoint-evidence-next)
        (:checkpoint-semantic-begin)
        (:checkpoint-semantic-load)
        (:checkpoint-semantic-copy)
        (:checkpoint-semantic-check)
        (:checkpoint-summary-capture)
        (:checkpoint-semantic-entries)
        (:checkpoint-semantic-find)
        (:checkpoint-summary-close)
        (:checkpoint-payload-begin)
        (:checkpoint-payload-load)
        (:checkpoint-payload-copy)
        (:checkpoint-payload-step)
        (:checkpoint-census) (:recover) (:recover-wait) (:epoch) (:epoch-fence) (:epoch-result) (:release) (:ready) (:failed)
         (:checkpoint-events-begin)
         (:checkpoint-events-journal-bind)
         (:checkpoint-events-journal-load)
         (:checkpoint-events-journal-received)
         (:checkpoint-events-journal-check)
         (:checkpoint-events-frontier-begin)
         (:checkpoint-events-frontier-check)
         (:checkpoint-events-frontier-peaks)
         (:checkpoint-events-frontier-padding)
         (:checkpoint-events-frontier-finish)
         (:checkpoint-events-finish)
         (:checkpoint-events-seed)
         (:checkpoint-project-begin)
         (:checkpoint-project-step)
         (:checkpoint-project-protect)
         (:checkpoint-cbase-acquire)
         (:checkpoint-adopt-begin)
         (:checkpoint-adopt-preflight)
         (:checkpoint-adopt-copy)
         (:checkpoint-authority-begin)
         (:checkpoint-authority-copy)
         (:checkpoint-directory-install)
         (:checkpoint-catalog-begin)
         (:checkpoint-catalog-copy)
         (:genesis-begin)
         (:genesis-step))
 :observes ((:read-result) (:write-result) (:fence-result)))

(include-book "checkpoint-restore-boot")
