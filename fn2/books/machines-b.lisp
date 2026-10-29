; Layer B declarations; the assembly owns the single core instance.
(in-package "ACL2")
(include-book "machines")
(include-book "core-children")
(include-book "profile")
(include-book "commit-alloc")
(include-book "format-check")
(fn2-book-layer :b)
(defun fn2-b-capacity (key default profile)
 (declare (xargs :guard t))
 (if (and (alistp profile) (assoc-equal key profile)) (fn2-profile-get key profile) default))
; Keep generated child/column guard proofs from expanding the full type database.
(in-theory (disable fn2-b-capacity))
(local (in-theory (disable tau-system)))
(defun fn2-b-barrier-mode (profile)
 (declare (xargs :guard t))
 (fn2-b-capacity :commit-barrier-mode 0 profile))
(defcorechild fn2-core-extents fn2-extents
 :init (fn2-alloc-init (fn2-b-capacity :extent-slots 16 profile) fn2-extents)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-alloc-edges fn2-alloc-edges
 :init (fn2-alloc-edges-init (fn2-b-capacity :alloc-edge-slots (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)))) profile) fn2-alloc-edges)
 :profilep (and
  (unsigned-byte-p 32 (fn2-b-capacity :alloc-edge-slots (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)))) profile))
  (<= (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile))))
      (fn2-b-capacity :alloc-edge-slots (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)))) profile)))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-fc fn2-fc
 :init (fn2-fc-init (fn2-b-capacity :format-slots 2 profile) fn2-fc)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-slots 2 profile))
                (<= 2 (fn2-b-capacity :format-slots 2 profile)))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-fc-context fn2-fc-context
 :init (fn2-fc-context-init (fn2-b-capacity :format-slots 2 profile) fn2-fc-context)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-slots 2 profile))
                (<= 2 (fn2-b-capacity :format-slots 2 profile)))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-b3 fn2-b3
 :init (fn2-b3-table-init (fn2-b-capacity :format-slots 2 profile) fn2-b3)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-slots 2 profile))
                (<= 2 (fn2-b-capacity :format-slots 2 profile)))
 :why "Commit work survives scheduler yields.")
(defun fn2-b-digest-minimum (profile)
 (declare (xargs :guard t))
 (+ (* *fn2-digest-stride* (nfix (fn2-b-capacity :format-slots 2 profile)))
    1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
(defthm fn2-b-digest-minimum-natural
 (natp (fn2-b-digest-minimum profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-b-digest-minimum))
(defcorechild fn2-core-digests fn2-digests
 :init (fn2-digests-init (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile) fn2-digests)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile))
  (<= (fn2-b-digest-minimum profile) (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile)))
 :why "Hasher stripes and immutable predecessor seals survive commit yields and row reuse.")
(defcorechild fn2-core-fields fn2-fields
 :init (fn2-fields-init (fn2-b-capacity :format-field-slots 256 profile) fn2-fields)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-field-slots 256 profile))
                (<= 256 (fn2-b-capacity :format-field-slots 256 profile)))
 :why "Commit work survives scheduler yields.")
; Each resource row retains its exact issuing op generation as edge holder.
(defcolumns fn2-commit-io
 ((extent :u32) (epoch :u60) (counter :u60) (pool-slot :u32) (pool-gen :u60)
  (op-slot :u32) (op-gen :u60) (ready :bool) (lent :bool)))
(defcorechild fn2-core-commit-io fn2-commit-io
 :init (fn2-commit-io-init 6 fn2-commit-io) :profilep t
 :why "Three reserved resources per batch, including operation-owned edges.")
(defcolumns fn2-commit-root
 ((installed :u60) (published :u60) (proposed :u60)
  (parent :u60) (extent :u32) (first-key :u60) (members :u32) (seal-ready :bool) (barrier-mode :bool)
 ))
(local (in-theory (disable fn2-commit-rootp fn2-commit-root-wfp fn2-commit-root-rows)))
(defun fn2-commit-root-init-for (profile fn2-commit-root)
 (declare (xargs :stobjs fn2-commit-root
  :guard (and (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
              (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))))
 (let ((fn2-commit-root (fn2-commit-root-init (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))) fn2-commit-root)))
  (fn2-commit-root-set-barrier-mode 0 (fn2-b-barrier-mode profile) fn2-commit-root)))
(defthm fn2-commit-root-init-for-type
 (implies (and (fn2-commit-rootp root)
               (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
               (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))
          (fn2-commit-rootp (fn2-commit-root-init-for profile root))))
(defthm fn2-commit-root-init-for-wfp
 (implies (and (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
               (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))
          (fn2-commit-root-wfp (fn2-commit-root-init-for profile root))))
(in-theory (disable fn2-commit-root-init-for))
(defcorechild fn2-core-commit-root fn2-commit-root
 :init (fn2-commit-root-init-for profile fn2-commit-root)
 :profilep (and (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
                (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))
 :why "Root handles are swapped only after durability; profile mode is authoritative.")
(defconst *fn2-commit-reason-stray* 255)
(defun fn2-commit-initial-generation (slot base n gen)
 (declare (xargs :guard t) (ignore slot base n)) gen)
(defmachine fn2-commit
 :states (:free :collect :seal :dependencies :log-write :fence :durable
          :install :publish :notify :draining :uncertain)
 :fields ((pending :u32) (stopped :bool) (pool-slot :u32) (pool-gen :u60)
          (batch-no :u60) (member-count :u32) (first-key :u60) (partner :u32)
          (cb-mode :bool) (cb-stage :u32) (cb-cursor :u32)
          (cb-issued :u32) (cb-done :u32) (cb-bytes :u60)
          (cb-failed :bool) (outcome :u8) (cb-reason :u8)
          (cb-fence-live :bool) (cb-fence-ok :bool) (cb-deps-ok :bool)
          (cb-log-ok :bool) (cb-published :bool) (cb-acks :u32)
          (cb-seal-len :u32))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 2
 :initial ((generation fn2-commit-initial-generation) (ready-prev 4294967295) (ready-next 4294967295))
 :observes ((:write-result fn2-commit-observe)
            (:fence-result fn2-commit-observe))
 :continuations
 ((:free fn2-commit-idle)
  (:collect fn2-commit-collect)
  (:seal fn2-commit-seal)
  (:dependencies fn2-commit-writes)
  (:log-write fn2-commit-writes)
  (:fence fn2-commit-fence)
  (:durable fn2-commit-durable)
  (:install fn2-commit-install)
  (:publish fn2-commit-publish)
  (:notify fn2-commit-notify)
  (:draining fn2-commit-drain)
  (:uncertain fn2-commit-drain)))
(include-book "commit")

; Export child boundaries: downstream A proofs need shapes, not B array bodies.
(in-theory (disable fn2-extentsp fn2-extents-wfp fn2-extents-rows
 fn2-alloc-edgesp fn2-alloc-edges-wfp fn2-alloc-edges-rows
 fn2-fcp fn2-fc-wfp fn2-fc-rows fn2-fc-contextp fn2-fc-context-wfp fn2-fc-context-rows
 fn2-b3p fn2-b3-wfp fn2-b3-rows fn2-fieldsp fn2-fields-wfp fn2-fields-rows
 fn2-commit-iop fn2-commit-io-wfp fn2-commit-io-rows
 fn2-commit-io-extent fn2-commit-io-epoch fn2-commit-io-counter fn2-commit-io-pool-slot fn2-commit-io-pool-gen fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-ready fn2-commit-io-lent
 fn2-commit-rootp fn2-commit-root-wfp fn2-commit-root-rows
 fn2-commit-root-installed fn2-commit-root-published
 fn2-commit-root-proposed fn2-commit-root-parent fn2-commit-root-extent fn2-commit-root-first-key fn2-commit-root-members fn2-commit-root-seal-ready fn2-commit-root-barrier-mode
 fn2-digestsp fn2-digests-wfp fn2-digests-rows
 fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal))
