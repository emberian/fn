; The Layer E control and consumer continuations (books/cns.lisp), in their
; own leaf section book so arm-body edits do not invalidate assembly.cert or executor.cert.
; After the published grants' exact reads (authority.lisp's
; fn2-auth-read-events): a consumer request's :check calls fn2-cns-authority-allows.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "cns")
(include-book "authority")
(local (defun fn2-ecns-core-child-type-terms (children)
         (declare (xargs :verify-guards nil))
         (if (atom children) nil
           (cons `(,(fn2-columns-sym (cadar children) "P") (,(caar children) fn2-core))
                 (fn2-ecns-core-child-type-terms (cdr children))))))
(make-event
 (value `(local (defthm fn2-ecns-core-child-types-fc
                  (implies (fn2-corep fn2-core)
                           (and ,@(fn2-ecns-core-child-type-terms *fn2-core-children*)))
                  :rule-classes :forward-chaining))))
(make-event
 (value `(local (in-theory (enable ,@(fn2-core-child-wfp-forward-runes *fn2-core-children*))))))
(local (in-theory (disable fn2-reads-rows fn2-fields-rows fn2-fc-rows fn2-id-decides-rows
                           fn2-digests-rows fn2-b3-rows fn2-extents-rows fn2-cns-sources-rows)))
(local (defun fn2-ecns-mentions-sym-p (sym x)
         (declare (xargs :guard (symbolp sym)))
         (if (atom x) (eq x sym)
           (or (fn2-ecns-mentions-sym-p sym (car x))
               (fn2-ecns-mentions-sym-p sym (cdr x))))))
(local (defun fn2-ecns-put-kw (key val kw)
         (declare (xargs :verify-guards nil))
         (cond ((atom kw) (list key val))
               ((eq (car kw) key) (list* key val (cddr kw)))
               (t (list* (car kw) (cadr kw) (fn2-ecns-put-kw key val (cddr kw)))))))
(local (defun fn2-ecns-subarm-syms (kind names)
         (declare (xargs :verify-guards nil))
         (if (atom names) nil
           (cons (fn2-columns-sym kind (concatenate 'string "-SUB-" (symbol-name (car names))))
                 (fn2-ecns-subarm-syms kind (cdr names))))))
(local (defun fn2-ecns-collect-compound-calls-lst (fns x acc)
         (declare (xargs :verify-guards nil))
         (if (atom x) acc
           (fn2-ecns-collect-compound-calls-lst
            fns (cdr x)
            (if (and (consp (car x))
                     (symbolp (caar x))
                     (not (eq (caar x) 'quote)))
                (let ((acc (fn2-ecns-collect-compound-calls-lst fns (cdar x) acc)))
                  (if (and (member-eq (caar x) fns)
                           (consp (cdar x))
                           (consp (car (last (cdar x))))
                           (not (member-equal (car x) acc)))
                      (cons (car x) acc)
                    acc))
              acc)))))
(local (defun fn2-ecns-compound-subarm-fns (clause world)
         (declare (xargs :verify-guards nil))
         (let* ((subarms (append (fn2-ecns-subarm-syms
                                  'fn2-ctl (strip-cars (fn2-machine-declared 'fn2-ctl :subarms world)))
                                 (fn2-ecns-subarm-syms
                                  'fn2-cns (strip-cars (fn2-machine-declared 'fn2-cns :subarms world)))))
                (calls (fn2-ecns-collect-compound-calls-lst subarms clause nil)))
           (fn2-defined-fns (remove-duplicates-eq (strip-cars calls)) world))))
(local (defun fn2-ecns-enable-fns-kw (kw fns)
         (declare (xargs :verify-guards nil))
         (if (null fns) kw
           (let ((th (cadr (member-eq :in-theory kw))))
             (cond ((null th) (fn2-ecns-put-kw :in-theory (list 'e/d fns nil) kw))
                   ((and (consp th) (eq (car th) 'e/d) (equal (len th) 3))
                    (fn2-ecns-put-kw :in-theory
                      (list 'e/d (append fns (cadr th)) (set-difference-eq (caddr th) fns))
                      kw))
                   (t kw))))))
(local (defun fn2-ecns-phase-cases (term n)
         (declare (xargs :guard (natp n)))
         (if (zp n) (list (list 'equal term 0))
           (cons (list 'equal term n) (fn2-ecns-phase-cases term (- n 1))))))
(local (defun fn2-ecns-success-charge-disables (kind world)
         (declare (xargs :verify-guards nil))
         (fn2-defined-fns
          (append (list 'fn2-machine-contract-check 'fn2-machine-refuse-phase
                        (fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                        (fn2-machine-row-reader kind 'phase) 'fn2-machine-phase
                        'fn2-core-success-p 'fn2-core-stopped-p 'fn2-core-stop-reason
                        (fn2-columns-sym kind "-ARM-CHARGE-OK-P")
                        (fn2-columns-sym kind "-ARM-NEXT-OK-P"))
                  (remove-duplicates-eq (strip-cadrs (fn2-machine-property kind :continuations world))))
          world)))
(local
 (defthm fn2-ecns-contract-check-projections
   (and (equal (car (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)) bytes)
        (equal (mv-nth 0 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)) bytes)
        (equal (mv-nth 1 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)) steps)
        (equal (mv-nth 2 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)) descriptors)
        (equal (fn2-core-success-p (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
               (and (if ok t nil) (fn2-core-success-p fn2-core)))
        (equal (fn2-core-success-p (mv-nth 4 (fn2-machine-refuse-phase id fn2-core)))
               nil)
        (equal (fn2-core-success-p (fn2-core-stop reason fn2-core))
               nil)
        (equal (fn2-core-ops (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
               (fn2-core-ops fn2-core))
        (equal (fn2-core-ops (mv-nth 4 (fn2-machine-refuse-phase id fn2-core)))
               (fn2-core-ops fn2-core)))
   :hints (("Goal" :in-theory (enable fn2-machine-contract-check fn2-machine-refuse-phase
                                      fn2-machine-finish fn2-machine-refuse-write)))))
(local
 (defthm fn2-ecns-core-success-p-dest
   (implies (fn2-core-success-p fn2-core)
            (and (not (fn2-core-stopped-p fn2-core))
                 (equal (fn2-core-stop-reason fn2-core) 0)))
   :hints (("Goal" :in-theory (enable fn2-core-success-p)))))
(local
 (defthm fn2-ecns-row-phase-when-ok
   (and (implies (equal (fn2-ctl-snapshot-read-code id fn2-core) :ok)
                 (equal (fn2-ctl-row-phase id fn2-core)
                        (fn2-machine-phase id fn2-core)))
        (implies (equal (fn2-cns-snapshot-read-code id fn2-core) :ok)
                 (equal (fn2-cns-row-phase id fn2-core)
                        (fn2-machine-phase id fn2-core))))
   :hints (("Goal" :in-theory (enable fn2-ctl-row-phase fn2-ctl-snapshot-read-code
                                      fn2-cns-row-phase fn2-cns-snapshot-read-code
                                      fn2-machine-phase fn2-machine-phase-read-code)))))
(local (add-default-hints
        '((and stable-under-simplificationp
               (not (fn2-ecns-mentions-sym-p 'fn2-ctl-run clause))
               (not (fn2-ecns-mentions-sym-p 'fn2-cns-run clause))
               (not (fn2-ecns-mentions-sym-p 'fn2-arm-kids clause))
               (let ((fns (fn2-ecns-compound-subarm-fns clause world)))
                 (and fns (list :in-theory (list 'e/d fns nil))))))))
(local (add-override-hints
        '((cond ((not (equal id '((0) nil . 0))) keyword-alist)
                ((and (fn2-ecns-mentions-sym-p 'fn2-ctl-run clause)
                      (fn2-ecns-mentions-sym-p 'fn2-ctl-arm-charge-ok-p clause))
                 (list :cases (fn2-ecns-phase-cases '(fn2-machine-phase id fn2-core)
                                (max 0 (1- (len (fn2-machine-property 'fn2-ctl :states world)))))
                       :in-theory (list 'e/d
                                        '(fn2-ctl-run fn2-ctl-arm-ok-p)
                                        (fn2-ecns-success-charge-disables 'fn2-ctl world))))
                ((and (fn2-ecns-mentions-sym-p 'fn2-cns-run clause)
                      (fn2-ecns-mentions-sym-p 'fn2-cns-arm-charge-ok-p clause))
                 (list :cases (fn2-ecns-phase-cases '(fn2-machine-phase id fn2-core)
                                (max 0 (1- (len (fn2-machine-property 'fn2-cns :states world)))))
                       :in-theory (list 'e/d
                                        '(fn2-cns-run fn2-cns-arm-ok-p)
                                        (fn2-ecns-success-charge-disables 'fn2-cns world))))
                ((and (or (fn2-ecns-mentions-sym-p 'fn2-ctl-run clause)
                          (fn2-ecns-mentions-sym-p 'fn2-cns-run clause))
                      (or (fn2-ecns-mentions-sym-p 'fn2-run-quantitiesp clause)
                          (fn2-ecns-mentions-sym-p 'fn2-ops-issued-count clause)
                          (and (fn2-ecns-mentions-sym-p 'fn2-core-ops clause)
                               (fn2-ecns-mentions-sym-p 'nth clause))))
                 (let ((th (cadr (member-eq :in-theory keyword-alist))))
                   (if (and (consp th) (eq (car th) 'e/d) (equal (len th) 3))
                       (fn2-ecns-put-kw :in-theory
                         (list 'e/d
                               (remove-eq 'fn2-machine-contract-check (cadr th))
                               (append '(fn2-machine-contract-check
                                         fn2-ctl-snapshot-read-code fn2-cns-snapshot-read-code)
                                       (caddr th)))
                         keyword-alist)
                     keyword-alist)))
                (t keyword-alist)))))
(fn2-auth-read-events)
(fn2-authority-depend-events)
(fn2-cns-events)
