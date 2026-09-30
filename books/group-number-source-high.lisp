; Pointwise immutable high maintenance for the actual assigned-member fold.
(in-package "ACL2")
(include-book "group-number-source-key")
(include-book "group-number-source-stage")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-gns-membershipsp (members)
  (declare (xargs :guard t))
  (if (consp members)
      (and (consp (car members)) (stringp (caar members)) (posp (cdar members))
           (fn-gns-membershipsp (cdr members)))
    (not members)))
(defun fn-gns-member-high (group members)
  (declare (xargs :guard t))
  (if (consp members)
      (max (if (and (consp (car members)) (equal group (caar members)))
               (nfix (cdar members)) 0)
           (fn-gns-member-high group (cdr members)))
    0))
(defthm fn-gns-member-high-type
  (natp (fn-gns-member-high group members))
  :rule-classes (:rewrite :type-prescription))
(defthm fn-gns-group-high-after-one-set
  (implies (and (or (stringp group) (stringp target)) (natp high))
    (equal (fn-gns-group-value-high
             (fn-gns-group-get group 0 0
               (fn-gns-group-set target 0 0 (fn-gns-group-value high nr) root)))
           (if (equal group target) high
             (fn-gns-group-value-high (fn-gns-group-get group 0 0 root)))))
  :hints (("Goal" :use ((:instance fn-gns-group-get-of-set
                                   (a group) (b target) (value (fn-gns-group-value high nr))))
           :in-theory (disable fn-gns-group-get fn-gns-group-set
                               fn-gns-group-get-of-set))))
(defthm fn-gns-memberships-root-preserves-high
  (implies (fn-gns-membershipsp members)
    (equal (fn-gns-group-value-high
             (fn-gns-group-get group 0 0 (fn-gns-memberships-root members ordinal root)))
           (max (fn-gns-group-value-high (fn-gns-group-get group 0 0 root))
                (fn-gns-member-high group members))))
  :hints (("Goal" :induct (fn-gns-memberships-root members ordinal root)
           :in-theory (e/d (fn-gns-memberships-root fn-gns-member-high fn-gns-membershipsp)
                           (fn-gns-group-get fn-gns-group-set fn-gnix-set
                            fn-gns-group-value-high fn-gns-group-value-root
                            fn-gns-group-value)))))
