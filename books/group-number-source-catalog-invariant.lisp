; Initial and preserved pointwise catalog-high lineage; no served-time scan.
(in-package "ACL2")
(include-book "group-number-source-pending")
(include-book "group-number-source-high")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-gns-string-groupsp (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (and (stringp (car groups)) (fn-gns-string-groupsp (cdr groups)))
    t))
(defthm fn-gns-empty-root-lookup
  (equal (fn-gns-group-get group pos bit nil) nil)
  :hints (("Goal" :induct (fn-gns-group-get group pos bit nil)
           :in-theory (disable fn-gns-bit))))
(defthm fn-gns-empty-root-has-empty-catalog-high
  (equal (fn-gns-group-value-high (fn-gns-group-get group 0 0 nil))
         (fn-cat-group-high group nil)))
(defthm fn-gns-empty-root-matches-initial-groups
  (implies (fn-gns-string-groupsp groups)
           (fn-gns-groups-high-matchp groups nil nil)))
(defthm fn-gns-high-match-implies-string-groups
  (implies (fn-gns-groups-high-matchp groups root catalog)
           (fn-gns-string-groupsp groups))
  :hints (("Goal" :in-theory (disable fn-gns-group-get fn-cat-group-high
                                      fn-gns-group-value-high))))
(defthm fn-gns-catalog-high-type
  (natp (fn-cat-group-high group catalog))
  :rule-classes (:rewrite :type-prescription))
(defthm fn-gns-catalog-assigned-members-typed
  (implies (fn-gns-string-groupsp groups)
           (fn-gns-membershipsp (fn-cat-assign-numbers groups catalog))))
(defthm fn-gns-catalog-assigned-member-high
  (equal (fn-gns-member-high group (fn-cat-assign-numbers groups catalog))
         (if (member-equal group groups) (1+ (fn-cat-group-high group catalog)) 0))
  :hints (("Goal" :induct (fn-cat-assign-numbers groups catalog)
           :in-theory (disable fn-cat-group-high))))
(local
 (defthm fn-gns-assoc-of-actual-assigned-members
  (equal (fn-cat-assoc group (fn-cat-assign-numbers groups catalog))
         (if (member-equal group groups)
             (cons group (1+ (fn-cat-group-high group catalog))) nil))))
(local
 (defthm fn-gns-number-in-actual-assigned-row
  (equal (fn-held-number-in group (fn-cat-assign h catalog))
         (if (member-equal group (fn-record-groups h))
             (1+ (fn-cat-group-high group catalog)) nil))
  :hints (("Goal" :in-theory (enable fn-held-number-in fn-cat-assign fn-held-with-numbers)))))
(local
 (defthm fn-gns-high-of-actual-append
  (equal (fn-cat-group-high group (append catalog (list h)))
         (max (fn-cat-group-high group catalog) (nfix (fn-held-number-in group h))))))
(defthm fn-gns-prepared-insertion-preserves-catalog-high
  (implies (and (fn-gns-groups-high-matchp (fn-record-groups h) root catalog)
                (equal (fn-gns-group-value-high (fn-gns-group-get group 0 0 root))
                       (fn-cat-group-high group catalog)))
    (equal (fn-gns-group-value-high
             (fn-gns-group-get group 0 0
               (fn-gns-memberships-root
                 (fn-gns-assigned-memberships (fn-record-groups h) root) ordinal root)))
           (fn-cat-group-high group (append catalog (list (fn-cat-assign h catalog))))))
  :hints (("Goal"
    :use ((:instance fn-gns-memberships-root-preserves-high
                     (members (fn-cat-assign-numbers (fn-record-groups h) catalog))))
    :in-theory (disable fn-gns-group-get fn-gns-memberships-root
                       fn-gns-group-value-high fn-gns-assigned-memberships
                       fn-cat-group-high fn-cat-assign fn-cat-assign-numbers
                       fn-gns-groups-high-matchp fn-gns-membershipsp
                       fn-gns-memberships-root-preserves-high))))
; Actual terminal API projection, linked to the carried staged-fold
; denotation (which each bounded stage action preserves).
(defthm fn-gns-completed-stage-preserves-catalog-high
  (implies (and (eq (fn-gns-at 0 c) :done)
                (equal (fn-gns-stage-denotation c)
                  (fn-gns-memberships-root
                    (fn-gns-assigned-memberships (fn-record-groups h) root) ordinal root))
                (fn-gns-groups-high-matchp (fn-record-groups h) root catalog)
                (equal (fn-gns-group-value-high (fn-gns-group-get group 0 0 root))
                       (fn-cat-group-high group catalog)))
    (equal (fn-gns-group-value-high
             (fn-gns-group-get group 0 0 (fn-gns-at 1 (fn-gns-stage-result c))))
           (fn-cat-group-high group (append catalog (list (fn-cat-assign h catalog))))))
  :hints (("Goal" :use ((:instance fn-gns-prepared-insertion-preserves-catalog-high))
           :in-theory (e/d (fn-gns-stage-result fn-gns-stage-denotation)
             (fn-gns-group-get fn-gns-memberships-root fn-gns-assigned-memberships
              fn-gns-group-value-high fn-cat-group-high fn-cat-assign
              fn-gns-groups-high-matchp fn-gns-prepared-insertion-preserves-catalog-high)))))
