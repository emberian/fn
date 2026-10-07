(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-store-groups-from-codes-step (groups x rest)
  (declare (xargs :guard (and (true-listp groups)
                              (or (equal rest :bad) (true-listp rest)))))
  (let ((group (if (natp x) (fn-store-group-name x groups) nil)))
    (if group
        (if (or (equal rest :bad) (member-equal group rest))
            :bad
          (cons group rest))
      :bad)))

(defun fn-store-groups-from-codes-loop (rev groups acc)
  (declare (xargs :guard (and (true-listp groups)
                              (or (equal acc :bad) (true-listp acc)))))
  (if (consp rev)
      (fn-store-groups-from-codes-loop (cdr rev) groups (fn-store-groups-from-codes-step groups (car rev) acc))
    acc))

(defun fn-store-groups-from-codes (codes groups)
  ; A code list becomes a distinct group list from the table, or :bad.
  ; Duplicate and unknown codes are refused here rather than deeper in the
  ; model.
  (declare (xargs :guard (true-listp groups) :verify-guards nil))
  (mbe :logic
   (if (consp codes)
      (let ((group (if (natp (car codes))
                       (fn-store-group-name (car codes) groups)
                     nil)))
        (if group
            (let ((rest (fn-store-groups-from-codes (cdr codes) groups)))
              (if (or (equal rest :bad) (member-equal group rest))
                  :bad
                (cons group rest)))
          :bad))
    (if (null codes) nil :bad))
   :exec (fn-store-groups-from-codes-loop (fn-ag-rev-onto codes nil) groups
                      (if (true-listp codes) nil :bad))))

(defthm fn-store-groups-from-codes-loop-of-rev-onto
  (equal (fn-store-groups-from-codes-loop (fn-ag-rev-onto codes zs) groups (if (true-listp codes) nil :bad))
         (fn-store-groups-from-codes-loop zs groups (fn-store-groups-from-codes codes groups)))
  :hints (("Goal" :induct (fn-ag-rev-onto codes zs)
                  :in-theory (disable fn-store-group-name))))

(verify-guards fn-store-groups-from-codes
  :hints (("Goal" :use ((:instance fn-store-groups-from-codes-loop-of-rev-onto (zs nil)))
                  :in-theory (disable fn-store-groups-from-codes-loop-of-rev-onto))))
