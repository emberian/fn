; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-catalog-correspondence")

(defun-nx fn-lb-reconstitute-row (r homes) (let* ((facts (nth 6 r)) (identity (nth 7 r))) (fn-held-make (nth 8 r) (car identity) (cadr identity)
      (nth 0 r) (nth 1 r) (nth 2 r)
      (nth 0 homes) (nth 1 homes) (nth 2 homes)
      (caddr identity) (nth 4 r)
      (fn-hf-make (nth 0 facts) (nth 1 facts) (nth 2 facts)
                  (fn-lbc-restore-control (nth 4 homes) (nth 3 facts)))
      (nth 3 homes) (nth 3 r) (nth 5 r))))

(defthm fn-lbc-at-by-reconstitution-definition
 (equal (fn-lbc-at i fn-lbc log)
        (fn-lb-reconstitute-row (fn-lbc-served-row i fn-lbc) (nth 7 (fn-lbc-home-entry i fn-lbc log))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-at fn-lb-reconstitute-row)))))

(local (defthm fn-lbrc-control-restore
 (implies (true-listp control)
 (equal (fn-lbc-restore-control
         (list (len control) (take (min 3 (len control)) control) (nthcdr 4 control))
         (nth 3 control)) control))
 :hints (("Goal" :do-not-induct t
 :expand ((len control) (len (cdr control)) (len (cddr control)) (len (cdddr control))
 (take 3 control) (take 2 (cdr control)) (take 1 (cddr control))
 (nth 3 control) (nth 2 (cdr control)) (nth 1 (cddr control))
 (nthcdr 4 control) (nthcdr 3 (cdr control)) (nthcdr 2 (cddr control)) (nthcdr 1 (cdddr control)))
 :cases ((consp control) (consp (cdr control)) (consp (cddr control)) (consp (cdddr control)))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-restore-control len true-listp take nthcdr nth nfix min binary-append)) '((tau-system)))))))

(local (defthm fn-lbrc-nov-is-fourth-control
 (equal (fn-hf-nov facts) (nth 3 (fn-hf-control facts)))
 :hints (("Goal" :expand ((nth 3 (fn-hf-control facts)) (nth 2 (cdr (fn-hf-control facts))) (nth 1 (cddr (fn-hf-control facts)))) :in-theory (union-theories (theory 'ground-zero)
 '(fn-hf-nov fn-cbor-ag-car fn-cbor-ag-cdr nth))))))

(local (defthm fn-lbrc-control-type
 (implies (fn-hf-p facts) (and (fn-hf-shapep facts) (true-listp (fn-hf-control facts))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-hf-p))))))

(local (defthm fn-lbrc-true-list-fix-identity
 (implies (true-listp xs) (equal (true-list-fix xs) xs))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero)
 '(len true-listp true-list-fix))))))

(defthm fn-lb-reconstitute-row-is-original
 (implies (and (fn-held-shapep row) (fn-hf-p (fn-held-facts row)))
 (equal (fn-lb-reconstitute-row (fn-cat-served-projection row) (fn-lb-log-model-homes row)) row))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbrc-control-restore (control (fn-hf-control (fn-held-facts row))))
 (:instance fn-held-make-of-accessors (x row))
       (:instance fn-hf-make-of-accessors (x (fn-held-facts row))))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lb-reconstitute-row fn-cat-served-projection fn-lb-log-model-homes
 fn-lbrc-nov-is-fourth-control fn-held-accessors-are-the-wire-accessors
 fn-lbrc-control-type fn-lbrc-true-list-fix-identity nth)) '((tau-system))))))
