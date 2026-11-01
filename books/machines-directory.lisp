(in-package "ACL2")
(include-book "machines")
(include-book "profile")
;; The directory row of a machine id: its kind and slot, and (MACHINE-FORM
;; 6.5 P1) the row fields generic code writes across rows,
;; *fn2-machine-directory-fields*: the resource FIFOs' links and the wait reason.
(make-event
 `(defcolumns fn2-machines ((kind :u8) (slot :u32) ,@*fn2-machine-directory-fields*)
 :init-name fn2-machines-columns-init
 :extra-fields
  ((fn2-machines-accept-count :type (unsigned-byte 32) :initially 0 :why "Directory-wide listener capacity fixes the admission partition.")
   (fn2-machines-connection-count :type (array (unsigned-byte 32) (16)) :initially 0 :why "Each admitted kind's connection capacity fixes its reusable partition (indexed by admitted-kind ordinal).")
   (fn2-machines-free-head :type (array (unsigned-byte 32) (16)) :initially *fn2-none* :why "One connection free-chain head per admitted kind.")
   (fn2-machines-gen-limit :type (unsigned-byte 60) :initially 0 :why "Generation retirement policy applies to every machine kind.")
   (fn2-machines-kind-bases :type (array (unsigned-byte 32) (256)) :initially *fn2-none* :why "Kind-indexed directory offsets have different cardinality from machine rows.")
   (fn2-machines-wake-id :type (unsigned-byte 32) :initially *fn2-none* :why "Single pending wake handoff from the current callback.")
   (fn2-machines-pool-wait-id :type (unsigned-byte 32) :initially *fn2-none* :why "The singleton storage probe owns the pool waiter.")
   (fn2-machines-wait-head :type (unsigned-byte 32) :initially *fn2-none* :why "Head of the global operation-credit FIFO.")
   (fn2-machines-wait-tail :type (unsigned-byte 32) :initially *fn2-none* :why "Tail of the global operation-credit FIFO.")
   (fn2-machines-refusals :type (unsigned-byte 60) :initially 0 :why "Aggregate admission refusals outlive individual rows.")
   (fn2-machines-admission-head :type (array (unsigned-byte 32) (16)) :initially *fn2-none* :why "Head of each admitted kind's admission-credit FIFO across listeners.")
   (fn2-machines-admission-tail :type (array (unsigned-byte 32) (16)) :initially *fn2-none* :why "Tail of each admitted kind's admission-credit FIFO across listeners.")
   (fn2-machines-admission-credits :type (array (unsigned-byte 32) (16)) :initially 0 :why "Unassigned connection credits per admitted kind.")
   (fn2-machines-active-count :type (array (unsigned-byte 32) (16)) :initially 0 :why "Active connections per admitted kind, compared with its credits."))))

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
             (fn2-machines (fn2-machines-set-slot (- left 1) (if (unsigned-byte-p 32 slot) slot 0) fn2-machines))
             (fn2-machines (fn2-machines-set-ready-prev (- left 1) *fn2-none* fn2-machines))
             (fn2-machines (fn2-machines-set-ready-next (- left 1) *fn2-none* fn2-machines))
             (fn2-machines (fn2-machines-set-wait-reason (- left 1) *fn2-wait-none* fn2-machines)))
        (fn2-machines-init-rows (- left 1) profile fn2-machines)))))
(fn2-machines-preserves fn2-machines-init-rows (left profile fn2-machines) :prefix "" :wfp-type nil :raw-rows t)

; Each admitted kind's partition: capacity, free head at its first row,
; credits equal to its capacity, no active rows, empty admission FIFO.
(defun fn2-machines-init-partitions (left profile fn2-machines)
  (declare (xargs :stobjs fn2-machines :measure (nfix left)
                  :guard (and (natp left) (<= left 16) (fn2-machines-wfp fn2-machines))))
  (if (or (zp left) (> left 16)) fn2-machines
    (let* ((o (- left 1)) (cap (fn2-machine-admitted-capacity o profile))
           (base (fn2-machine-admitted-base o profile))
           (cap (if (unsigned-byte-p 32 cap) cap 0))
           (base (if (unsigned-byte-p 32 base) base *fn2-none*))
           (fn2-machines (update-fn2-machines-connection-counti o cap fn2-machines))
           (fn2-machines (update-fn2-machines-free-headi o base fn2-machines))
           (fn2-machines (update-fn2-machines-admission-creditsi o cap fn2-machines))
           (fn2-machines (update-fn2-machines-active-counti o 0 fn2-machines))
           (fn2-machines (update-fn2-machines-admission-headi o *fn2-none* fn2-machines))
           (fn2-machines (update-fn2-machines-admission-taili o *fn2-none* fn2-machines)))
      (fn2-machines-init-partitions o profile fn2-machines))))
; The partition capacities and bases are opaque here: the stores check their widths.
(in-theory (disable fn2-machine-admitted-capacity fn2-machine-admitted-base))
(fn2-machines-preserves fn2-machines-init-partitions (left profile fn2-machines) :prefix "" :wfp-type nil :raw-rows t)
(in-theory (enable fn2-machine-admitted-capacity fn2-machine-admitted-base))
(defun fn2-machines-admitted-capacities-p (left profile)
  (declare (xargs :guard (natp left) :measure (nfix left)))
  (if (zp left) t
    (and (unsigned-byte-p 32 (fn2-machine-admitted-capacity (- left 1) profile))
         (fn2-machines-admitted-capacities-p (- left 1) profile))))

(defun fn2-machines-profilep (profile)
  (declare (xargs :guard t))
  (and (fn2-profilep profile)
       (unsigned-byte-p 32 (fn2-profile-accept-credits profile))
       (unsigned-byte-p 32 (fn2-profile-c profile))
       (fn2-machines-admitted-capacities-p (len *fn2-machine-partitioned*) profile)
       (< (fn2-machine-index-count profile)
          4294967296)))

(defun fn2-machines-init (profile fn2-machines)
  (declare (xargs :stobjs fn2-machines :guard (fn2-machines-profilep profile)))
  (let* ((a (fn2-profile-accept-credits profile))
         (n (fn2-machine-index-count profile))
         (fn2-machines (fn2-machines-columns-init n fn2-machines))
         (fn2-machines (fn2-machines-init-bases 256 profile fn2-machines))
         (fn2-machines (update-fn2-machines-accept-count a fn2-machines))
         (fn2-machines (fn2-machines-init-partitions (len *fn2-machine-partitioned*) profile fn2-machines))
         (fn2-machines (update-fn2-machines-refusals 0 fn2-machines))
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
