; Image startup's declaration. Configuration is a trusted startup input;
; external image octets stay in bounded pool windows and are never read as Lisp.
(in-package "ACL2")
(include-book "machines-b")
(include-book "machine-arms")
(include-book "boot-config-state")
(include-book "boot-format")
(fn2-book-layer :b)

; Only startup configuration has a list cursor. It advances one group per
; visit, is cleared before ready, and never contains parsed device data.
; Its resident measure (T10) is declared at the boot record's widths: each of
; the COUNT genesis groups as a name at the identity field's 250 octets (the
; most fn2-boot-pack-pool writes) and a u60 value in 8 bytes; the path at
; *fn2-profile-path-identity-max* octets. COUNT is fixed at init, so the
; measure is too while the cursor advances.



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

(defmachine fn2-boot
 :states (:free :prepare :write :write-result :read :read-result :verify :advance
          :anchor :recover :recover-wait :epoch :epoch-fence :epoch-result :release :ready :failed)
 :fields ((pending :u32) (stopped :bool) (pool-slot :u32) (pool-gen :u60)
          (rx-slot :u32) (rx-gen :u60) (create :bool) (image-size :u60)
          (base :u60) (total :u32) (index :u32) (stage :u8) (offset :u60)
          (epoch0 :u60) (epoch1 :u60) (next-epoch :u60) (anchor-slot :bool)
          (event-ready :bool) (outcome :u8) (count :u32) (release-index :u32))
 :holds ((:prepare :storage-window) (:write :storage-window) (:write-result :storage-window)
         (:read :storage-window) (:read-result :storage-window) (:verify :storage-window)
         (:advance :storage-window) (:anchor :storage-window) (:recover :storage-window)
         (:recover-wait :storage-window) (:epoch :storage-window) (:epoch-fence :storage-window)
         (:epoch-result :storage-window))
 :budget (:bytes 32768 :steps 32 :descriptors 4)
 :stops (:geometry :configuration :io :anchor :recovery :epoch :bounds)
 :capacity (if (fn2-profile-get :image-boot profile) 1 0)
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free) (:prepare) (:write) (:write-result) (:read) (:read-result) (:verify) (:advance)
        (:anchor) (:recover) (:recover-wait) (:epoch) (:epoch-fence) (:epoch-result) (:release) (:ready) (:failed))
 :observes ((:read-result) (:write-result) (:fence-result)))
