(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-bpnp-prune-waits-loop (waits held acc)
  (declare (xargs :guard t :measure (acl2-count waits)))
  (if (atom waits) (fn-ag-rev-onto acc nil)
    (fn-bpnp-prune-waits-loop (cdr waits) held
     (if (fn-bpnf-find-held (fn-bpn-nth 1 (car waits)) held) (cons (car waits) acc) acc))))

(defun fn-bpnp-prune-waits (waits held)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count waits)))
  (mbe :logic
       (if (atom waits) nil
         (let* ((row (car waits))
                (key (fn-bpn-nth 1 row)))
           (if (fn-bpnf-find-held key held)
               (cons row (fn-bpnp-prune-waits (cdr waits) held))
             (fn-bpnp-prune-waits (cdr waits) held))))
       :exec (fn-bpnp-prune-waits-loop waits held nil)))

(defthm fn-bpnp-prune-waits-loop-is-rev-onto
  (equal (fn-bpnp-prune-waits-loop waits held acc)
         (fn-ag-rev-onto acc (fn-bpnp-prune-waits waits held)))
  :hints (("Goal" :induct (fn-bpnp-prune-waits-loop waits held acc)
                  :in-theory (union-theories
                              '(fn-bpnp-prune-waits-loop fn-bpnp-prune-waits fn-ag-rev-onto atom car-cons cdr-cons)
                              (theory 'minimal-theory)))))
