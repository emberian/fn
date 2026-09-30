; W8: logical obligations and resource state are different coordinates.
; This is a reference/refinement component over the retention ledger, not
; a served traversal or a claim about the full owner/snapshot composition.
(in-package "ACL2")
(include-book "history-knowledge")

(defun fn-hrf-pin (pin)
  (declare (xargs :guard t))
  (list (fn-retain-obligation-id pin)
        (fn-retain-obligation-subject pin)
        (fn-retain-obligation-kind pin)
        (fn-retain-obligation-evidence pin)))

(defun fn-hrf-pins (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (cons (fn-hrf-pin (car pins)) (fn-hrf-pins (cdr pins)))
    nil))

(defun fn-hrf-charges (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (cons (list (fn-retain-obligation-id (car pins))
                  (fn-retain-obligation-charge (car pins)))
            (fn-hrf-charges (cdr pins)))
    nil))

(defun fn-hrf-logical (r)
  (declare (xargs :guard t))
  (list (fn-hrf-pins (fn-retain-pins r)) (fn-retain-releases r)))

(defun fn-hrf-resource (r)
  (declare (xargs :guard t))
  (list (fn-retain-capacity r) (fn-retain-reserved r)
        (fn-hrf-charges (fn-retain-pins r))))

(defun fn-hrf-alpha (r)
  (declare (xargs :guard t))
  (list (fn-hrf-logical r) (fn-hrf-resource r)))

; Abstract maintenance changes the named charge and the reserved sum.
; It does not remove an obligation or edit its evidence, nor does it
; pretend that changing resource capacity is externally unobservable.
(defun fn-hrf-maintain-charges (charges id)
  (declare (xargs :guard (alistp charges)))
  (if (consp charges)
      (cons (if (equal (caar charges) id)
                (list id *fn-rclp-history-unit*)
              (car charges))
            (fn-hrf-maintain-charges (cdr charges) id))
    nil))

(defun fn-hrf-maintain (alpha id)
  (declare (xargs :guard
    (and (true-listp alpha)
         (true-listp (cadr alpha))
         (acl2-numberp (cadr (cadr alpha)))
         (alistp (caddr (cadr alpha)))
         (true-listp (assoc-equal id (caddr (cadr alpha))))
         (or (not (assoc-equal id (caddr (cadr alpha))))
             (acl2-numberp
               (cadr (assoc-equal id (caddr (cadr alpha)))))))))
  (let* ((logical (car alpha))
         (resource (cadr alpha))
         (capacity (car resource))
         (reserved (cadr resource))
         (charges (caddr resource))
         (found (assoc-equal id charges)))
    (if found
        (list logical
              (list capacity
                    (+ *fn-rclp-history-unit* (- reserved (cadr found)))
                    (fn-hrf-maintain-charges charges id)))
      alpha)))

(local
 (defthm fn-hrf-reduce-pin-keeps-logical-by-definition
   (equal (fn-hrf-pin (fn-hkn-reduce-pin pin)) (fn-hrf-pin pin))))

(local
 (defthm fn-hrf-reduce-pins-keeps-logical
   (equal (fn-hrf-pins (fn-hkn-reduce-pins pins id))
          (fn-hrf-pins pins))
   :hints (("Goal" :in-theory (disable fn-hkn-reduce-pin fn-hrf-pin)))))

(defthm fn-hrf-maintenance-preserves-logical-obligations
  (equal (fn-hrf-logical (fn-hkn-release-retention r id))
         (fn-hrf-logical r))
  :hints (("Goal" :in-theory (disable fn-hkn-reduce-pins fn-hrf-pins))))

(local
 (defthm fn-hrf-assoc-charges
   (implies (alistp pins)
    (equal (assoc-equal id (fn-hrf-charges pins))
          (if (consp (fn-retain-find-id id pins))
              (list id (fn-retain-obligation-charge
                        (fn-retain-find-id id pins)))
            nil)))
   :hints (("Goal" :in-theory (enable fn-retain-find-id)))))

(local
 (defthm fn-hrf-reduce-pins-charges
   (equal (fn-hrf-charges (fn-hkn-reduce-pins pins id))
          (fn-hrf-maintain-charges (fn-hrf-charges pins) id))
   :hints (("Goal" :in-theory (disable fn-hkn-reduce-pin)))))

; A commuting square for the existing logical-release operation.  R is
; not dropped: the full abstraction equals an explicit maintenance step.
(defthm fn-hrf-release-refines-abstract-maintenance
  (implies (alistp (fn-retain-pins r))
           (equal (fn-hrf-alpha (fn-hkn-release-retention r id))
                  (fn-hrf-maintain (fn-hrf-alpha r) id)))
  :hints (("Goal" :in-theory (disable fn-hkn-reduce-pins fn-hrf-charges
                                     fn-hrf-maintain-charges fn-retain-find-id
                                     fn-hrf-pins))))

; A common admitted operation has the same promised logical result even
; when its two starting resource states differ.  Capacity disagreement is
; deliberately outside this premise; it must remain in the external trace.
(defthm fn-hrf-common-admission-preserves-logical-equivalence
  (implies (and (equal (fn-hrf-logical left) (fn-hrf-logical right))
                (fn-retain-admissiblep left id subject kind evidence charge)
                (fn-retain-admissiblep right id subject kind evidence charge))
           (equal (fn-hrf-logical
                   (fn-retain-admit left id subject kind evidence charge))
                  (fn-hrf-logical
                   (fn-retain-admit right id subject kind evidence charge))))
  :hints (("Goal" :in-theory (e/d (fn-retain-admit)
                                 (fn-retain-admissiblep fn-hrf-pin)))))

(local
 (defthm fn-hrf-find-projected-pin
   (implies (alistp pins)
            (equal (fn-retain-find-id id (fn-hrf-pins pins))
                   (if (consp (fn-retain-find-id id pins))
                       (fn-hrf-pin (fn-retain-find-id id pins))
                     nil)))
   :hints (("Goal" :in-theory (enable fn-retain-find-id
                                     fn-retain-obligation-id)))))

(local
 (defthm fn-hrf-matching-release-uses-logical-pin
   (implies (alistp pins)
            (equal (fn-retain-matching-releasep
                    (fn-retain-find-id id pins) id subject kind evidence)
                   (equal (fn-retain-find-id id (fn-hrf-pins pins))
                          (list id subject kind evidence))))
   :hints (("Goal" :in-theory (e/d (fn-retain-matching-releasep)
                                  (fn-retain-find-id fn-hrf-pins))))))

(local
 (defthm fn-hrf-remove-id-projection
   (equal (fn-hrf-pins (fn-retain-remove-id id pins))
          (fn-retain-remove-id id (fn-hrf-pins pins)))
   :hints (("Goal" :in-theory (enable fn-retain-remove-id
                                     fn-retain-obligation-id)))))

(local
 (defthm fn-hrf-obligation-list-is-alist
   (implies (fn-retain-obligation-listp pins) (alistp pins))))

; Receipts discharge the same obligation, or neither one, with the same
; retained authorization evidence.  The amount returned belongs to R.
(defthm fn-hrf-release-preserves-logical-equivalence
  (implies (and (fn-retain-statep left) (fn-retain-statep right)
                (equal (fn-hrf-logical left) (fn-hrf-logical right)))
           (equal (fn-hrf-logical
                   (fn-retain-release left id subject kind evidence))
                  (fn-hrf-logical
                   (fn-retain-release right id subject kind evidence))))
  :hints (("Goal" :in-theory (e/d (fn-retain-release fn-retain-statep)
                                 (fn-retain-matching-releasep
                                  fn-retain-find-id fn-retain-remove-id
                                  fn-hrf-pins fn-hrf-pin)))))
