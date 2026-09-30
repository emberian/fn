; The actual pending catalog row is unassigned until this bounded producer.
; ROOT/ROOT-ID are supplied only by the core registered publication builder.
(in-package "ACL2")
(include-book "group-number-source-assignment")
(include-book "catalog-commit")

(defun fn-gns-pending-begin (pending root root-id)
  (declare (xargs :guard t))
  (fn-gns-assign-begin (fn-record-groups (fn-pc-held pending)) root
    (fn-pc-held pending) (fn-pc-token pending) (fn-pc-expected pending) root-id))
(defun fn-gns-pending-result (c)
  (declare (xargs :guard t))
  (if (eq (fn-gns-at 0 c) :done)
      (list :assigned (fn-gns-at 7 c) (fn-gns-at 8 c) (fn-gns-at 9 c)
            (fn-gns-at 11 c)
            (fn-held-with-numbers (fn-gns-at 7 c) (fn-gns-at 5 c))
            (fn-gns-at 5 c) (fn-gns-at 10 c))
    '(:pending)))

; Logical carried relation, not a served-time catalog revalidation. The
; publisher must establish/preserve it for the actual immutable root.
(defun fn-gns-groups-high-matchp (groups root catalog)
  (declare (xargs :guard t))
  (if (consp groups)
      (and (stringp (car groups))
           (equal (fn-gns-group-value-high (fn-gns-group-get (car groups) 0 0 root))
                  (fn-cat-group-high (car groups) catalog))
           (fn-gns-groups-high-matchp (cdr groups) root catalog))
    t))
(defthm fn-gns-assigned-memberships-are-cat-assign-numbers
  (implies (fn-gns-groups-high-matchp groups root catalog)
    (equal (fn-gns-assigned-memberships groups root)
           (fn-cat-assign-numbers groups catalog)))
  :hints (("Goal" :induct (fn-gns-groups-high-matchp groups root catalog)
           :in-theory (enable fn-gns-groups-high-matchp fn-gns-assigned-memberships
                              fn-cat-assign-numbers))))
(defthm fn-gns-pending-done-is-cat-assign
  (implies (and (eq (fn-gns-at 0 c) :done)
                (equal (fn-gns-at 7 c) (fn-pc-held pending))
                (equal (fn-gns-assign-denotation c)
                       (fn-gns-assigned-memberships (fn-record-groups (fn-pc-held pending))
                                                  (fn-gns-at 2 c)))
                (fn-gns-groups-high-matchp (fn-record-groups (fn-pc-held pending))
                                          (fn-gns-at 2 c) catalog))
    (equal (fn-gns-at 5 (fn-gns-pending-result c))
           (fn-cat-assign (fn-pc-held pending) catalog)))
  :hints (("Goal" :use ((:instance fn-gns-assign-done-result-refinement))
           :in-theory (e/d (fn-gns-pending-result fn-gns-assign-denotation fn-cat-assign)
                           (fn-gns-assigned-memberships fn-gns-groups-high-matchp)))))
