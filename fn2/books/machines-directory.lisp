(in-package "ACL2")
(include-book "machines")
(include-book "profile")
(defcolumns fn2-machines ((kind :u8) (slot :u32))
 :init-name fn2-machines-columns-init
 :extra-fields
  ((fn2-machines-accept-count :type (unsigned-byte 32) :initially 0 :why "Directory-wide listener capacity fixes the admission partition.")
   (fn2-machines-connection-count :type (unsigned-byte 32) :initially 0 :why "Directory-wide connection capacity fixes the reusable partition.")
   (fn2-machines-free-head :type (unsigned-byte 32) :initially *fn2-none* :why "Single head of the connection free chain.")
   (fn2-machines-gen-limit :type (unsigned-byte 60) :initially 0 :why "Generation retirement policy applies to every machine kind.")
   (fn2-machines-kind-bases :type (array (unsigned-byte 32) (256)) :initially *fn2-none* :why "Kind-indexed directory offsets have different cardinality from machine rows.")
   (fn2-machines-wake-id :type (unsigned-byte 32) :initially *fn2-none* :why "Single pending wake handoff from the current callback.")
   (fn2-machines-pool-wait-id :type (unsigned-byte 32) :initially *fn2-none* :why "The singleton storage probe owns the pool waiter.")
   (fn2-machines-wait-head :type (unsigned-byte 32) :initially *fn2-none* :why "Head of the global operation-credit FIFO.")
   (fn2-machines-wait-tail :type (unsigned-byte 32) :initially *fn2-none* :why "Tail of the global operation-credit FIFO.")
   (fn2-machines-refusals :type (unsigned-byte 60) :initially 0 :why "Aggregate admission refusals outlive individual rows.")
   (fn2-machines-admission-head :type (unsigned-byte 32) :initially *fn2-none* :why "Head of the admission-credit FIFO across listeners.")
   (fn2-machines-admission-tail :type (unsigned-byte 32) :initially *fn2-none* :why "Tail of the admission-credit FIFO across listeners.")
   (fn2-machines-admission-credits :type (unsigned-byte 32) :initially 0 :why "Unassigned connection credits are directory-wide.")
   (fn2-machines-active-count :type (unsigned-byte 32) :initially 0 :why "Aggregate active connections must be compared with admission credits.")))

(defmacro fn2-machine-directory-events ()
 '(progn
(defun fn2-machines-init-bases (left profile fn2-machines)
  (declare (xargs :stobjs fn2-machines :measure (nfix left)
                  :guard (and (natp left) (<= left 256) (fn2-profilep profile))))
  (if (or (zp left) (> left 256)) fn2-machines
    (let* ((kind (- left 1)) (id (fn2-machine-global-id kind 0 profile))
           (fn2-machines (update-fn2-machines-kind-basesi kind
                          (if (unsigned-byte-p 32 id) id *fn2-none*) fn2-machines)))
      (fn2-machines-init-bases kind profile fn2-machines))))
(fn2-machines-preserves fn2-machines-init-bases (left profile fn2-machines) :prefix "" :wfp-type nil :raw-rows t)

(defun fn2-machines-init-rows (left profile fn2-machines)
  (declare (xargs :stobjs fn2-machines :measure (nfix left)
                  :guard (and (natp left) (<= left (fn2-machines-rows fn2-machines))
                              (fn2-profilep profile) (fn2-machines-wfp fn2-machines))))
  (if (or (zp left) (> left (fn2-machines-rows fn2-machines))) fn2-machines
    (mv-let (kind slot) (fn2-machine-local-id (- left 1) profile)
      (let* ((fn2-machines (fn2-machines-set-kind (- left 1) (if (unsigned-byte-p 8 kind) kind 255) fn2-machines))
             (fn2-machines (fn2-machines-set-slot (- left 1) (if (unsigned-byte-p 32 slot) slot 0) fn2-machines)))
        (fn2-machines-init-rows (- left 1) profile fn2-machines)))))
(fn2-machines-preserves fn2-machines-init-rows (left profile fn2-machines) :prefix "" :wfp-type nil :raw-rows t)

(defun fn2-machines-profilep (profile)
  (declare (xargs :guard t))
  (and (fn2-profilep profile)
       (unsigned-byte-p 32 (fn2-profile-accept-credits profile))
       (unsigned-byte-p 32 (fn2-profile-c profile))
       (< (fn2-machine-index-count profile)
          4294967296)))

(defun fn2-machines-init (profile fn2-machines)
  (declare (xargs :stobjs fn2-machines :guard (fn2-machines-profilep profile)))
  (let* ((a (fn2-profile-accept-credits profile)) (c (fn2-profile-c profile))
         (n (fn2-machine-index-count profile))
         (fn2-machines (fn2-machines-columns-init n fn2-machines))
         (fn2-machines (fn2-machines-init-bases 256 profile fn2-machines))
         (fn2-machines (update-fn2-machines-accept-count a fn2-machines))
         (fn2-machines (update-fn2-machines-connection-count c fn2-machines))
         (fn2-machines (update-fn2-machines-free-head (fn2-machine-global-id *fn2-echo-kind* 0 profile) fn2-machines))
         (fn2-machines (update-fn2-machines-refusals 0 fn2-machines))
         (fn2-machines (update-fn2-machines-active-count 0 fn2-machines))
         (fn2-machines (update-fn2-machines-admission-credits c fn2-machines))
         (fn2-machines (update-fn2-machines-admission-head *fn2-none* fn2-machines))
         (fn2-machines (update-fn2-machines-admission-tail *fn2-none* fn2-machines))
         (fn2-machines (update-fn2-machines-gen-limit
                        (fn2-profile-generation-limit profile) fn2-machines))
         (fn2-machines (update-fn2-machines-wake-id *fn2-none* fn2-machines))
         (fn2-machines (update-fn2-machines-pool-wait-id *fn2-none* fn2-machines))
         (fn2-machines (update-fn2-machines-wait-head *fn2-none* fn2-machines))
         (fn2-machines (update-fn2-machines-wait-tail *fn2-none* fn2-machines)))
    (fn2-machines-init-rows n profile fn2-machines)))
(defthm fn2-machines-init-type
  (implies (and (fn2-machinesp fn2-machines) (fn2-machines-profilep profile))
           (fn2-machinesp (fn2-machines-init profile fn2-machines))))
(defthm fn2-machines-init-wfp
  (implies (fn2-machines-profilep profile)
           (fn2-machines-wfp (fn2-machines-init profile fn2-machines))))
(in-theory (disable fn2-machines-init fn2-machines-profilep))
(assert-event
 (fn2-assert-compliant-p
  '(fn2-machines-init-rows
    fn2-machines-profilep fn2-machines-init) (w state)))

))
