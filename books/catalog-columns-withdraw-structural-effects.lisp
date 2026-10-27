; Withdrawal leaves number bindings, group keys and Message-ID indexing intact.
(in-package "ACL2")
(include-book "catalog-columns-withdraw-row-logical-effects")

(defthm fn-lbcwd-logical-membership-of-withdrawal-by-definition
 (and (equal (fn-held-numbers (fn-held-with-withdrawn row withdrawn)) (fn-held-numbers row))
      (equal (fn-record-groups (fn-held-with-withdrawn row withdrawn)) (fn-record-groups row)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-held-with-withdrawn fn-held-make fn-held-numbers fn-record-groups fn-cbor-ag-car fn-cbor-ag-cdr)))))

(local (defun-nx fn-lbcwd-update-induct (rows n)
 (declare (xargs :measure (acl2-count rows) :verify-guards nil))
 (if (and (consp rows) (posp n))
  (fn-lbcwd-update-induct (cdr rows) (- n 1)) nil)))

(local (defun-nx fn-lbcwd-number-update-induct (rows n base)
 (declare (xargs :measure (acl2-count rows) :verify-guards nil))
 (if (and (consp rows) (posp n))
  (fn-lbcwd-number-update-induct (cdr rows) (- n 1) (+ 1 base)) nil)))

(local (defun-nx fn-lbcwd-slot-update-induct (rows n start table)
 (declare (xargs :measure (acl2-count rows) :verify-guards nil))
 (if (and (consp rows) (posp n))
  (fn-lbcwd-slot-update-induct (cdr rows) (- n 1) (+ 1 (nfix start))
   (fn-lbc-canonical-slot-insert (+ 1 (nfix start))
    (mod (fn-lbc-msgid-hash (fn-record-msgid (car rows))) (max 1 (len table)))
    (len table) table)) nil)))

(defthm fn-lbcwd-number-seq-of-withdrawal-update
 (implies (and (natp n) (< n (len rows)))
  (equal (fn-cat-number-seq group number
          (update-nth n (fn-held-with-withdrawn (nth n rows) withdrawn) rows) base)
         (fn-cat-number-seq group number rows base)))
 :hints (("Goal" :induct (fn-lbcwd-number-update-induct rows n base)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcwd-number-update-induct fn-cat-number-seq fn-held-number-in
     fn-lbcwd-logical-membership-of-withdrawal-by-definition
     update-nth nth len natp posp nfix)))))

(defthm fn-lbcwd-row-group-keys-of-withdrawal-update
 (implies (and (natp n) (< n (len rows)))
  (equal (fn-lbc-row-group-keys
          (update-nth n (fn-held-with-withdrawn (nth n rows) withdrawn) rows))
         (fn-lbc-row-group-keys rows)))
 :hints (("Goal" :induct (fn-lbcwd-update-induct rows n)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcwd-update-induct fn-lbc-row-group-keys
     fn-lbcwd-logical-membership-of-withdrawal-by-definition
     update-nth nth len natp posp nfix)))))

(defthm fn-lbcwd-canonical-slots-from-of-withdrawal-update
 (implies (and (natp n) (< n (len rows)))
  (equal (fn-lbc-canonical-slots-from
          (update-nth n (fn-held-with-withdrawn (nth n rows) withdrawn) rows) start table)
         (fn-lbc-canonical-slots-from rows start table)))
 :hints (("Goal" :induct (fn-lbcwd-slot-update-induct rows n start table)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcwd-slot-update-induct fn-lbc-canonical-slots-from
     fn-lbcwd-logical-key-of-withdrawal-by-definition
     update-nth nth len natp posp nfix)))))

(defthm fn-lbcwd-rowsp-of-withdrawal-update
 (implies (and (natp n) (< n (len rows)) (fn-cat-rowsp rows)
               (fn-held-withdrawnp withdrawn))
  (fn-cat-rowsp (update-nth n (fn-held-with-withdrawn (nth n rows) withdrawn) rows)))
 :hints (("Goal" :induct (fn-lbcwd-update-induct rows n)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcwd-update-induct fn-cat-rowsp fn-lbcwd-logical-row-type-of-withdrawal
     update-nth nth len natp posp nfix)))))

(defthm fn-lbcwd-held-listp-of-withdrawal-update
 (implies (and (natp n) (< n (len rows)) (fn-held-listp rows)
               (fn-held-withdrawnp withdrawn))
  (fn-held-listp (update-nth n (fn-held-with-withdrawn (nth n rows) withdrawn) rows)))
 :hints (("Goal" :induct (fn-lbcwd-update-induct rows n)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcwd-update-induct fn-held-listp fn-cat-held-p-of-with-withdrawn
     update-nth nth len natp posp nfix)))))
