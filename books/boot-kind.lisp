; Image startup's declaration. Configuration is a trusted startup input;
; external image octets stay in bounded pool windows and are never read as Lisp.
(in-package "ACL2")
(include-book "machines-b")
(include-book "machine-arms")
(fn2-book-layer :b)

(deflayout fn2-boot-record
 '((magic :u32) (version :u8) (kind :u8) (index :varint)
   (image-size :varint) (extents :varint) (groups :varint)
   (owner :u32) (authority :u8) (identity (:octets 250))
   (value :varint) (epoch :varint) (previous :varint)))
(defconst *fn2-boot-magic* #x54423246)
(defconst *fn2-boot-unit* 4096)
(defconst *fn2-boot-hash-offset* 4064)

; Only startup configuration has a list cursor. It advances one group per
; visit, is cleared before ready, and never contains parsed device data.
(defcolumns fn2-boot-config nil :init-name fn2-boot-config-empty
 :extra-fields
 ((fn2-boot-config-groups :type t :initially nil :why "Unconsumed trusted startup group configuration; one group per boot visit.")
  (fn2-boot-config-path :type t :initially nil :why "Trusted startup path identity, checked against the immutable image record.")
  (fn2-boot-config-count :type (unsigned-byte 32) :initially 0 :why "Number of immutable genesis group records.")
  (fn2-boot-config-extents :type (unsigned-byte 32) :initially 0 :why "The image's arena geometry, checked before recovery.")
  (fn2-boot-config-owner :type (unsigned-byte 32) :initially 0 :why "Persisted initial owner account binding.")
  (fn2-boot-config-authority :type (unsigned-byte 1) :initially 0 :why "Whether genesis includes the principal directory.")))

(defun fn2-boot-config-prepare (profile fn2-boot-config)
 (declare (xargs :stobjs fn2-boot-config :guard t))
 (let* ((fn2-boot-config (fn2-boot-config-empty 0 fn2-boot-config))
        (groups (fn2-profile-get :groups profile))
        (extents (fn2-b-capacity :extent-slots 16 profile))
        (owner (fn2-profile-get :owner-account profile)))
  (if (not (fn2-profile-get :image-boot profile)) fn2-boot-config
   (let* ((fn2-boot-config (update-fn2-boot-config-groups groups fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-path (fn2-profile-path-identity profile) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-count (if (unsigned-byte-p 32 (len groups)) (len groups) 0) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-extents (if (unsigned-byte-p 32 extents) extents 0) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-owner (if (and (posp owner) (unsigned-byte-p 32 owner)) owner 1) fn2-boot-config))
          (fn2-boot-config (update-fn2-boot-config-authority (if (posp (nfix (fn2-profile-get :authority profile))) 1 0) fn2-boot-config)))
     fn2-boot-config))))
(defthm fn2-boot-config-prepare-type (fn2-boot-configp (fn2-boot-config-prepare profile fn2-boot-config)))
(defthm fn2-boot-config-prepare-wfp (fn2-boot-config-wfp (fn2-boot-config-prepare profile fn2-boot-config)))
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
         (:epoch-result :storage-window) (:release :storage-window))
 :budget (:bytes 32768 :steps 32 :descriptors 4)
 :stops (:geometry :configuration :io :anchor :recovery :epoch :bounds)
 :capacity (if (fn2-profile-get :image-boot profile) 1 0)
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free) (:prepare) (:write) (:write-result) (:read) (:read-result) (:verify) (:advance)
        (:anchor) (:recover) (:recover-wait) (:epoch) (:epoch-fence) (:epoch-result) (:release) (:ready) (:failed))
 :observes ((:read-result) (:write-result) (:fence-result)))
