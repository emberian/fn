; Persistent membership lookup; full catalog ordinal bridge uses the original
; fn-cat-number-seq reference from the exact lightweight numbering leaf.
(in-package "ACL2")
(include-book "group-number-source-high")
(include-book "catalog-number-assignment")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-gns-membership-presentp (group number members)
  (declare (xargs :guard t))
  (if (consp members)
      (or (and (consp (car members))
               (equal group (caar members)) (equal number (cdar members)))
          (fn-gns-membership-presentp group number (cdr members)))
    nil))
(defthm fn-gns-one-insertion-lookup
  (implies (and (posp number) (posp assigned) (stringp target))
    (equal (fn-gnix-get number
             (fn-gns-group-value-root
               (fn-gns-group-get group 0 0
                 (fn-gns-group-set target 0 0
                   (fn-gns-group-value
                     (max assigned (fn-gns-group-value-high (fn-gns-group-get target 0 0 root)))
                     (fn-gnix-set assigned (list :ordinal ordinal)
                       (fn-gns-group-value-root (fn-gns-group-get target 0 0 root)))) root))))
           (if (and (equal group target) (equal number assigned))
               (list :ordinal ordinal)
             (fn-gnix-get number (fn-gns-group-value-root (fn-gns-group-get group 0 0 root))))))
  :hints (("Goal" :in-theory (disable fn-gns-group-get fn-gns-group-set
                                      fn-gnix-get fn-gnix-set
                                      fn-gns-group-value-high fn-gns-group-value-root
                                      fn-gns-group-value))))
(defthm fn-gns-memberships-root-lookup
  (implies (and (posp number) (fn-gns-membershipsp members))
    (equal (fn-gnix-get number
             (fn-gns-group-value-root
               (fn-gns-group-get group 0 0 (fn-gns-memberships-root members ordinal root))))
           (if (fn-gns-membership-presentp group number members)
               (list :ordinal ordinal)
             (fn-gnix-get number (fn-gns-group-value-root (fn-gns-group-get group 0 0 root))))))
  :hints (("Goal" :induct (fn-gns-memberships-root members ordinal root)
           :in-theory (e/d (fn-gns-memberships-root fn-gns-membership-presentp fn-gns-membershipsp)
             (fn-gns-group-get fn-gns-group-set fn-gns-group-value-high
              fn-gns-group-value-root fn-gns-group-value fn-gnix-get fn-gnix-set)))))

(defthm fn-gns-actual-assigned-membership
  (equal (fn-gns-membership-presentp group number
           (fn-cat-assign-numbers groups catalog))
         (and (member-equal group groups)
              (equal number (1+ (fn-cat-group-high group catalog)))) )
  :hints (("Goal" :induct (fn-cat-assign-numbers groups catalog)
           :in-theory (disable fn-cat-group-high))))

(defthm fn-gns-number-above-catalog-high-is-absent
  (implies (and (posp number) (< (fn-cat-group-high group catalog) number))
           (equal (fn-cat-number-seq group number catalog ordinal) nil))
  :hints (("Goal" :induct (fn-cat-number-seq group number catalog ordinal))))

(defthm fn-gns-catalog-number-seq-append
  (implies (natp ordinal)
    (equal (fn-cat-number-seq group number (append catalog tail) ordinal)
           (or (fn-cat-number-seq group number catalog ordinal)
               (fn-cat-number-seq group number tail (+ ordinal (len catalog))))))
  :hints (("Goal" :induct (fn-cat-number-seq group number catalog ordinal))))

(local
 (defthm fn-gns-lookup-assoc-assigned
  (equal (fn-cat-assoc group (fn-cat-assign-numbers groups catalog))
         (if (member-equal group groups)
             (cons group (1+ (fn-cat-group-high group catalog))) nil))))
(local
 (defthm fn-gns-lookup-number-in-assigned
  (equal (fn-held-number-in group (fn-cat-assign h catalog))
         (if (member-equal group (fn-record-groups h))
             (1+ (fn-cat-group-high group catalog)) nil))
  :hints (("Goal" :in-theory (enable fn-held-number-in fn-cat-assign fn-held-with-numbers)))))

(defthm fn-gns-actual-assignment-number-seq
  (implies (posp number)
    (equal (fn-cat-number-seq group number
             (append catalog (list (fn-cat-assign h catalog))) 0)
           (if (and (member-equal group (fn-record-groups h))
                    (equal number (1+ (fn-cat-group-high group catalog))))
               (len catalog)
             (fn-cat-number-seq group number catalog 0))))
  :hints (("Goal" :use ((:instance fn-gns-number-above-catalog-high-is-absent
                        (ordinal 0)))
           :in-theory (disable fn-cat-assign fn-cat-assign-numbers
                               fn-cat-group-high fn-held-number-in))))

(defun fn-gns-ordinal-option (ordinal)
  (declare (xargs :guard t))
  (if (natp ordinal) (list :ordinal ordinal) nil))
(defthm fn-gns-catalog-number-seq-type
  (implies (natp ordinal)
    (or (not (fn-cat-number-seq group number catalog ordinal))
        (natp (fn-cat-number-seq group number catalog ordinal))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-cat-number-seq group number catalog ordinal))))

(defthm fn-gns-assigned-insertion-preserves-number-lookup
  (implies
    (and (posp number)
         (fn-gns-membershipsp (fn-cat-assign-numbers (fn-record-groups h) catalog))
         (equal (fn-gnix-get number
                  (fn-gns-group-value-root (fn-gns-group-get group 0 0 root)))
                (fn-gns-ordinal-option (fn-cat-number-seq group number catalog 0))))
    (equal (fn-gnix-get number
             (fn-gns-group-value-root
               (fn-gns-group-get group 0 0
                 (fn-gns-memberships-root
                   (fn-cat-assign-numbers (fn-record-groups h) catalog)
                   (len catalog) root))))
           (fn-gns-ordinal-option
             (fn-cat-number-seq group number
               (append catalog (list (fn-cat-assign h catalog))) 0))))
  :hints (("Goal"
    :in-theory (disable fn-gnix-get fn-gns-group-get fn-gns-group-value-root
                       fn-gns-memberships-root fn-cat-number-seq
                       fn-cat-assign fn-cat-assign-numbers fn-cat-group-high
                       fn-gns-membership-presentp fn-gns-membershipsp))))

(defthm fn-gns-completed-stage-preserves-number-lookup
  (implies
    (and (eq (fn-gns-at 0 c) :done)
         (equal (fn-gns-stage-denotation c)
                (fn-gns-memberships-root
                  (fn-cat-assign-numbers (fn-record-groups h) catalog)
                  (len catalog) root))
         (posp number)
         (fn-gns-membershipsp (fn-cat-assign-numbers (fn-record-groups h) catalog))
         (equal (fn-gnix-get number
                  (fn-gns-group-value-root (fn-gns-group-get group 0 0 root)))
                (fn-gns-ordinal-option (fn-cat-number-seq group number catalog 0))))
    (equal (fn-gnix-get number
             (fn-gns-group-value-root
               (fn-gns-group-get group 0 0 (fn-gns-at 1 (fn-gns-stage-result c)))))
           (fn-gns-ordinal-option
             (fn-cat-number-seq group number
               (append catalog (list (fn-cat-assign h catalog))) 0))))
  :hints (("Goal" :use ((:instance fn-gns-assigned-insertion-preserves-number-lookup))
    :in-theory (e/d (fn-gns-stage-result fn-gns-stage-denotation)
      (fn-gnix-get fn-gns-group-get fn-gns-group-value-root
       fn-gns-memberships-root fn-cat-number-seq fn-cat-assign
       fn-cat-assign-numbers fn-cat-group-high fn-gns-membershipsp
       fn-gns-assigned-insertion-preserves-number-lookup)))))
