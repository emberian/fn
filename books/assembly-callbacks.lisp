; Other layers' continuations follow layer A's section, before final dispatch.
(in-package "ACL2")
(include-book "assembly-callbacks-s")
(include-book "assembly-callbacks-d")
; Recovery's payload pass reads layers C's and D's record shapes.
(include-book "recovery-payload")
; Other layers' continuation event macros go HERE, before final dispatch.
; B5 recovery's arms (recovery-machine.lisp, in the arm language).
(defcost ceiling :doc "Integer ceiling.")
(local (defun fn2-ac-mentions-sym-p (sym x)
         (declare (xargs :guard (symbolp sym)))
         (if (atom x) (eq x sym)
           (or (fn2-ac-mentions-sym-p sym (car x))
               (fn2-ac-mentions-sym-p sym (cdr x))))))
(local (defun fn2-ac-put-kw (key val kw)
         (declare (xargs :verify-guards nil))
         (cond ((atom kw) (list key val))
               ((eq (car kw) key) (list* key val (cddr kw)))
               (t (list* (car kw) (cadr kw) (fn2-ac-put-kw key val (cddr kw)))))))
(local (defun fn2-ac-subarm-syms (kind names)
         (declare (xargs :verify-guards nil))
         (if (atom names) nil
           (cons (fn2-columns-sym kind (concatenate 'string "-SUB-" (symbol-name (car names))))
                 (fn2-ac-subarm-syms kind (cdr names))))))
(local (defun fn2-ac-collect-compound-calls-lst (fns x acc)
         (declare (xargs :verify-guards nil))
         (if (atom x) acc
           (fn2-ac-collect-compound-calls-lst
            fns (cdr x)
            (if (and (consp (car x))
                     (symbolp (caar x))
                     (not (eq (caar x) 'quote)))
                (let ((acc (fn2-ac-collect-compound-calls-lst fns (cdar x) acc)))
                  (if (and (member-eq (caar x) fns)
                           (consp (cdar x))
                           (consp (car (last (cdar x))))
                           (not (member-equal (car x) acc)))
                      (cons (car x) acc)
                    acc))
              acc)))))
(local (defun fn2-ac-compound-subarm-fns (clause kind world)
         (declare (xargs :verify-guards nil))
         (let* ((subarms (fn2-ac-subarm-syms
                          kind (strip-cars (fn2-machine-declared kind :subarms world))))
                (calls (fn2-ac-collect-compound-calls-lst subarms clause nil)))
           (fn2-defined-fns (remove-duplicates-eq (strip-cars calls)) world))))
(local (defun fn2-ac-enable-fns-kw (kw fns)
         (declare (xargs :verify-guards nil))
         (if (null fns) kw
           (let ((th (cadr (member-eq :in-theory kw))))
             (cond ((null th) (fn2-ac-put-kw :in-theory (list 'e/d fns nil) kw))
                   ((and (consp th) (eq (car th) 'e/d) (equal (len th) 3))
                    (fn2-ac-put-kw :in-theory
                      (list 'e/d (append fns (cadr th)) (set-difference-eq (caddr th) fns))
                      kw))
                   (t kw))))))
(local (defun fn2-ac-phase-cases (term n)
         (declare (xargs :guard (natp n)))
         (if (zp n) (list (list 'equal term 0))
           (cons (list 'equal term n) (fn2-ac-phase-cases term (- n 1))))))
(local (defun fn2-ac-success-charge-disables (kind world)
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
 (defthm fn2-ac-contract-check-projections
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
 (defthm fn2-ac-core-success-p-dest
   (implies (fn2-core-success-p fn2-core)
            (and (not (fn2-core-stopped-p fn2-core))
                 (equal (fn2-core-stop-reason fn2-core) 0)))
   :hints (("Goal" :in-theory (enable fn2-core-success-p)))))
(local
 (defthm fn2-ac-recovery-row-phase-when-ok
   (implies (equal (fn2-recovery-machine-snapshot-read-code id fn2-core) :ok)
            (equal (fn2-recovery-machine-row-phase id fn2-core)
                   (fn2-machine-phase id fn2-core)))
   :hints (("Goal" :in-theory (enable fn2-recovery-machine-row-phase fn2-recovery-machine-snapshot-read-code
                                      fn2-machine-phase fn2-machine-phase-read-code)))))
(local (add-default-hints
        '((and stable-under-simplificationp
               (not (fn2-ac-mentions-sym-p 'fn2-recovery-machine-run clause))
               (not (fn2-ac-mentions-sym-p 'fn2-boot-run clause))
               (not (fn2-ac-mentions-sym-p 'fn2-arm-kids clause))
               (let ((fns (append (fn2-ac-compound-subarm-fns clause 'fn2-recovery-machine world)
                                  (fn2-ac-compound-subarm-fns clause 'fn2-boot world))))
                 (and fns (list :in-theory (list 'e/d fns nil))))))))
(local (add-override-hints
        '((cond ((not (equal id '((0) nil . 0))) keyword-alist)
                ((and (fn2-ac-mentions-sym-p 'fn2-recovery-machine-run clause)
                      (fn2-ac-mentions-sym-p 'fn2-recovery-machine-arm-charge-ok-p clause))
                 (list :cases (fn2-ac-phase-cases '(fn2-machine-phase id fn2-core)
                                (max 0 (1- (len (fn2-machine-property 'fn2-recovery-machine :states world)))))
                       :in-theory (list 'e/d
                                        '(fn2-recovery-machine-run fn2-recovery-machine-arm-ok-p)
                                        (fn2-ac-success-charge-disables 'fn2-recovery-machine world))))
                ((and (fn2-ac-mentions-sym-p 'fn2-boot-run clause)
                      (fn2-ac-mentions-sym-p 'fn2-boot-arm-charge-ok-p clause))
                 (list :cases (fn2-ac-phase-cases '(fn2-machine-phase id fn2-core)
                                (max 0 (1- (len (fn2-machine-property 'fn2-boot :states world)))))
                       :in-theory (list 'e/d
                                        '(fn2-boot-run fn2-boot-arm-ok-p)
                                        (fn2-ac-success-charge-disables 'fn2-boot world))))
                ((and (or (fn2-ac-mentions-sym-p 'fn2-recovery-machine-run clause)
                          (fn2-ac-mentions-sym-p 'fn2-boot-run clause))
                      (or (fn2-ac-mentions-sym-p 'fn2-run-quantitiesp clause)
                          (fn2-ac-mentions-sym-p 'fn2-ops-issued-count clause)
                          (and (fn2-ac-mentions-sym-p 'fn2-core-ops clause)
                               (fn2-ac-mentions-sym-p 'nth clause))))
                 (fn2-ac-enable-fns-kw
                  (let ((th (cadr (member-eq :in-theory keyword-alist))))
                    (if (and (consp th) (eq (car th) 'e/d) (equal (len th) 3))
                        (fn2-ac-put-kw :in-theory
                          (list 'e/d
                                (remove-eq 'fn2-machine-contract-check (cadr th))
                                (append '(fn2-machine-contract-check
                                          fn2-recovery-machine-snapshot-read-code fn2-boot-snapshot-read-code)
                                        (caddr th)))
                          keyword-alist)
                      keyword-alist))
                  nil))
                (t keyword-alist)))))
(fn2-recovery-events-3)
(include-book "boot")
(local
 (defthm fn2-ac-boot-row-phase-when-ok
   (implies (equal (fn2-boot-snapshot-read-code id fn2-core) :ok)
            (equal (fn2-boot-row-phase id fn2-core)
                   (fn2-machine-phase id fn2-core)))
   :hints (("Goal" :in-theory (enable fn2-boot-row-phase fn2-boot-snapshot-read-code
                                      fn2-machine-phase fn2-machine-phase-read-code)))))
(fn2-boot-events)

(table fn2-costs 'fn2-conn-run-greeting nil)
(fn2-resolve :callbacks)
