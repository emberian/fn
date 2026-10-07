(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-bpnp-attempt-replace-loop (arrival record held acc)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) (fn-ag-rev-onto acc nil)
    (if (equal arrival (fn-bpn-nth 3 (car held)))
        (if (true-listp (car held))
            (fn-ag-rev-onto acc (cons (fn-bpnp-attempted-held (car held) record) (cdr held)))
          (fn-ag-rev-onto acc nil))
      (fn-bpnp-attempt-replace-loop arrival record (cdr held) (cons (car held) acc)))))

(defun fn-bpnp-attempt-replace (arrival record held)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count held)))
  (mbe :logic
       (if (atom held) nil
         (if (equal arrival (fn-bpn-nth 3 (car held)))
             (if (true-listp (car held))
                 (cons (fn-bpnp-attempted-held (car held) record) (cdr held))
               nil)
           (cons (car held)
                 (fn-bpnp-attempt-replace arrival record (cdr held)))))
       :exec (fn-bpnp-attempt-replace-loop arrival record held nil)))

(defthm fn-bpnp-attempt-replace-loop-is-rev-onto
  (equal (fn-bpnp-attempt-replace-loop arrival record held acc)
         (fn-ag-rev-onto acc (fn-bpnp-attempt-replace arrival record held)))
  :hints (("Goal" :induct (fn-bpnp-attempt-replace-loop arrival record held acc)
                  :in-theory (union-theories
                              '(fn-bpnp-attempt-replace-loop fn-bpnp-attempt-replace fn-ag-rev-onto atom car-cons cdr-cons)
                              (theory 'minimal-theory)))))
