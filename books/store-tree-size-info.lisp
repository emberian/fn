; Exact generic size-info events factored from the same-parse reader.
; Provenance is proof-only; missing child annotations remain unavailable.
(in-package "ACL2")
(include-book "store-tree-size")

(defun fn-scsr-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-scsr-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

(defun fn-scsr-info-root (info)
  (declare (xargs :guard t))
  (if (consp info) (car info) nil))

(defun fn-scsr-info-leaf (carry)
  (declare (xargs :guard t))
  (list carry))

(defun fn-scsr-info-pair (a d)
  (declare (xargs :guard (and (fn-scs-carryp (fn-scsr-info-root a))
                              (fn-scs-carryp (fn-scsr-info-root d)))))
  (cons (fn-scs-cons (fn-scsr-info-root a) (fn-scsr-info-root d))
        (cons a d)))

(defun fn-scsr-pair-info (a d)
  (declare (xargs :guard t))
  (if (and (fn-scs-carryp (fn-scsr-info-root a))
           (fn-scs-carryp (fn-scsr-info-root d)))
      (fn-scsr-info-pair a d)
    nil))

(defun fn-scsr-info-provenancep (info x)
 (declare (xargs :measure (acl2-count x) :verify-guards nil))
 (if (not (fn-scs-carryp (fn-scsr-info-root info))) t
   (and (equal (fn-scsr-info-root info) (fn-scs-summary x))
        (if (consp (fn-scsr-cdr info))
            (let ((a (fn-scsr-car (fn-scsr-cdr info)))
                  (d (fn-scsr-cdr (fn-scsr-cdr info))))
              (and (consp x)
                   (fn-scs-carryp (fn-scsr-info-root a))
                   (fn-scs-carryp (fn-scsr-info-root d))
                   (fn-scsr-info-provenancep a (car x))
                   (fn-scsr-info-provenancep d (cdr x))))
          t))))

(defun fn-scsr-info-field (n info)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (and (fn-scs-carryp (fn-scsr-info-root info))
          (consp (fn-scsr-cdr info)))
     (if (zp n) (fn-scsr-car (fn-scsr-cdr info))
       (fn-scsr-info-field (1- n) (fn-scsr-cdr (fn-scsr-cdr info))))
   nil))

(local (defun fn-scsr-info-field-provenance-ind (n info x)
 (declare (xargs :measure (nfix n)))
 (if (zp n) (list info x)
   (fn-scsr-info-field-provenance-ind (1- n) (fn-scsr-cdr (fn-scsr-cdr info)) (cdr x)))))

(defthm fn-scsr-info-field-preserves-provenance
 (implies (and (natp n) (fn-scsr-info-provenancep info x))
          (fn-scsr-info-provenancep (fn-scsr-info-field n info) (nth n x)))
 :hints (("Goal" :induct (fn-scsr-info-field-provenance-ind n info x)
          :in-theory (e/d (fn-scsr-info-field fn-scsr-info-provenancep
                           fn-scsr-info-root fn-scsr-car fn-scsr-cdr nth)
                          (fn-scs-summary fn-scs-carryp fn-scs-atom)))))
