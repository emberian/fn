; Physical selected-pack prefix reclamation in the byte crash model.
(in-package "ACL2")
(include-book "byte-store-programs")
(include-book "byte-store-txn-name")
(include-book "checkpoint-compaction")

(defun fn-bs-pack-covered-names (pairs selected-lower)
  (declare (xargs :guard t))
  (if (consp pairs)
      (if (< (nfix (fn-store-event-nth 0 (car pairs))) (nfix selected-lower))
          (cons (fn-store-event-nth 1 (car pairs))
                (fn-bs-pack-covered-names (cdr pairs) selected-lower))
        nil)
    nil))

; Logical subject called by the native reclaim path.  Only surviving covered
; names are removed; missing covered names are an interrupted prior attempt,
; and the selected observer separately requires an exact contiguous suffix.
(defun fn-bs-pack-reclaim-plan (names maximum selected-lower)
  (declare (xargs :guard t))
  (if (and (natp maximum) (natp selected-lower) (true-listp names)
           (<= (len names) maximum))
      (let ((selected (fn-bs-txn-observation-selected names selected-lower)))
        (if (equal selected :invalid) :invalid
          (fn-bs-pack-covered-names (third selected) selected-lower)))
    :invalid))

(defun fn-bs-pack-reclaim-steps (names)
  (declare (xargs :guard t))
  (if (consp names)
      (cons (list :unlink :transactions (car names))
            (cons (list :cut "pack-reclaim-unlink")
                  (fn-bs-pack-reclaim-steps (cdr names))))
    (list (list :fsync-dir :transactions)
          (list :cut "pack-reclaim-directory"))))

(defun fn-bs-pack-reclaim-program (names maximum selected-lower)
  (declare (xargs :guard t))
  (let ((plan (fn-bs-pack-reclaim-plan names maximum selected-lower)))
    (if (equal plan :invalid) nil (fn-bs-pack-reclaim-steps plan))))

(verify-guards fn-bs-pack-covered-names)
(verify-guards fn-bs-pack-reclaim-plan)
(verify-guards fn-bs-pack-reclaim-steps)
(verify-guards fn-bs-pack-reclaim-program)

(defthm fn-bs-pack-reclaim-plan-is-selected-covered-names
  (implies (and (natp maximum) (natp selected-lower) (true-listp names)
                (<= (len names) maximum)
                (not (equal (fn-bs-txn-observation-selected names selected-lower)
                            :invalid)))
           (equal (fn-bs-pack-reclaim-plan names maximum selected-lower)
                  (fn-bs-pack-covered-names
                   (third (fn-bs-txn-observation-selected names selected-lower))
                   selected-lower)))
  :hints (("Goal" :in-theory (enable fn-bs-pack-reclaim-plan))))

(local
 (defthm fn-bs-pack-reclaim-steps-last
   (equal (last (fn-bs-pack-reclaim-steps names))
          (list (list :cut "pack-reclaim-directory")))
   :hints (("Goal" :induct (fn-bs-pack-reclaim-steps names)
            :in-theory (enable fn-bs-pack-reclaim-steps)))))

; The exact source text calls the logical subject above.  This executable fact
; pins the two physical cut labels to transitions rather than prose strings.
(defthm fn-bs-pack-reclaim-program-has-closing-directory-fence
  (implies (not (equal (fn-bs-pack-reclaim-plan names maximum selected-lower)
                       :invalid))
           (equal (last (fn-bs-pack-reclaim-program
                         names maximum selected-lower))
                  (list (list :cut "pack-reclaim-directory"))))
  :hints (("Goal" :in-theory (enable fn-bs-pack-reclaim-program
                                     fn-bs-pack-reclaim-steps))))
