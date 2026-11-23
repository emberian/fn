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
(make-event
 (value `(local (in-theory (disable nth fn2-reads-rows fn2-fields-rows fn2-fc-rows
                                    fn2-digests-rows fn2-b3-rows fn2-pool-fill fn2-pool-base fn2-pool-data-length
                                    fn2-cns-sources-rows fn2-ctl-rows fn2-cns-rows fn2-succ-slots-rows)))))
(local
 (defun fn2-ecns-arm-fns (arms)
   (declare (xargs :mode :program))
   (if (atom arms) nil (cons (cadar arms) (fn2-ecns-arm-fns (cdr arms))))))
(local
 (defun fn2-ecns-wrap-success-charge (x kind arm-fns)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((and (eq (car x) 'make-event) (consp (cdr x)) (consp (cadr x))
               (eq (caadr x) 'value) (consp (cdadr x)) (consp (cadadr x))
               (eq (car (cadadr x)) 'fn2-machine-success-charge-event))
          (let ((arm-ok (fn2-columns-sym kind "-ARM-OK-P"))
                (arm-charge (fn2-columns-sym kind "-ARM-CHARGE-OK-P"))
                (arm-next (fn2-columns-sym kind "-ARM-NEXT-OK-P"))
                (row-phase (fn2-columns-sym kind "-ROW-PHASE"))
                (snap-code (fn2-columns-sym kind "-SNAPSHOT-READ-CODE"))
                (run-fn (fn2-columns-sym kind "-RUN"))
                (thm-name (fn2-columns-sym (fn2-columns-sym kind "-RUN") "-SUCCESS-CHARGE"))
                (cc-thm (fn2-columns-sym kind "-FAST-CONTRACT-CHECK-CHARGE"))
                (rp-thm (fn2-columns-sym kind "-FAST-ROW-PHASE-IS-MACHINE-PHASE")))
            `(make-event
              (let ((guard (getpropc ',run-fn 'guard t (w state))))
                (value
                 `(encapsulate ()
                    (local
                     (defthm ,',cc-thm
                       (implies (fn2-core-success-p
                                 (mv-nth 4 (fn2-machine-contract-check
                                            (,',arm-ok id phase bytes steps descriptors c1)
                                            bytes steps descriptors runnable c1)))
                                (,',arm-charge
                                 phase
                                 (car (fn2-machine-contract-check
                                       (,',arm-ok id phase bytes steps descriptors c1)
                                       bytes steps descriptors runnable c1))
                                 (mv-nth 1 (fn2-machine-contract-check
                                            (,',arm-ok id phase bytes steps descriptors c1)
                                            bytes steps descriptors runnable c1))
                                 (mv-nth 2 (fn2-machine-contract-check
                                            (,',arm-ok id phase bytes steps descriptors c1)
                                            bytes steps descriptors runnable c1))))
                       :hints (("Goal" :in-theory
                                (remove-equal '(:rewrite fn2-core-stopped-p-is-exec-stop)
                                 (e/d (fn2-machine-contract-check ,',arm-ok
                                       fn2-core-success-p fn2-core-stopped-p fn2-core-stop-reason
                                       fn2-core-stop fn2-control-record-stop fn2-control-stop
                                       update-fn2-control-stop update-fn2-control-stop-reason)
                                      (,',arm-charge ,',arm-next
                                       fn2-machine-phase fn2-machine-phase-read-code)))))))
                    (local
                     (defthm ,',rp-thm
                       (implies (eq (,',snap-code id fn2-core) :ok)
                                (equal (,',row-phase id fn2-core)
                                       (fn2-machine-phase id fn2-core)))
                       :hints (("Goal" :in-theory
                                (enable ,',row-phase fn2-machine-phase
                                        ,',snap-code fn2-machine-phase-read-code)))))
                    (defthm ,',thm-name
                      (implies (and (fn2-corep fn2-core)
                                    ,guard
                                    (fn2-core-success-p (mv-nth 4 (,',run-fn id budget fn2-core))))
                               (,',arm-charge
                                (fn2-machine-phase id fn2-core)
                                (car (,',run-fn id budget fn2-core))
                                (mv-nth 1 (,',run-fn id budget fn2-core))
                                (mv-nth 2 (,',run-fn id budget fn2-core))))
                      :hints (("Goal" :in-theory
                               (e/d (,',run-fn ,',cc-thm ,',rp-thm fn2-core-stop-not-success)
                                    (fn2-machine-contract-check
                                     ,',arm-ok ,',arm-charge ,',arm-next ,',row-phase
                                     fn2-machine-phase ,',snap-code fn2-machine-phase-read-code
                                     fn2-core-success-p fn2-core-stop fn2-machine-refuse-phase
                                     ,@',arm-fns)))))))))))
         (t (cons (fn2-ecns-wrap-success-charge (car x) kind arm-fns)
                  (fn2-ecns-wrap-success-charge (cdr x) kind arm-fns))))))
(local
 (defun fn2-ecns-find-result-fn (x)
   (declare (xargs :mode :program))
   (cond ((atom x) nil)
         ((and (eq (car x) 'fn2-machine-core-result-events)
               (consp (cdr x)) (consp (cadr x)) (eq (caadr x) 'quote))
          (cadadr x))
         (t (or (fn2-ecns-find-result-fn (car x))
                (fn2-ecns-find-result-fn (cdr x)))))))
(local
 (defun fn2-ecns-augment-arms-list (xs)
   (declare (xargs :mode :program))
   (if (atom xs) nil
     (let ((fn (fn2-ecns-find-result-fn (car xs))))
       (if fn
           (list* (car xs)
                  `(local
                    (make-event
                     (let ((guard (getpropc ',fn 'guard t (w state)))
                           (iss (fn2-columns-sym ',fn "-ISSUED-EFFECT"))
                           (gen (fn2-columns-sym ',fn "-ISSUED-EFFECT-GENERAL-N")))
                       (value
                        `(defthm ,gen
                           (implies (and (equal n (fn2-ops-rows (fn2-core-ops fn2-core)))
                                         (fn2-corep fn2-core)
                                         ,guard)
                                    (equal (fn2-ops-issued-count n (fn2-core-ops (mv-nth 4 (,',fn id budget fn2-core))))
                                           (+ (fn2-ops-issued-count n (fn2-core-ops fn2-core))
                                              (mv-nth 2 (,',fn id budget fn2-core)))))
                           :hints (("Goal" :use ,iss
                                           :in-theory (disable ,iss ,',fn fn2-core-ops fn2-corep fn2-core-wfp
                                                               fn2-ops-issued-count fn2-ops-rows))))))))
                  (fn2-ecns-augment-arms-list (cdr xs)))
         (cons (car xs) (fn2-ecns-augment-arms-list (cdr xs))))))))
(local
 (defun fn2-ecns-patch-form (x wrld)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((equal x '(fn2-append-outcome-read-events))
          (mv-let (erp exp) (macroexpand1-cmp x 'assembly-callbacks-e-cns wrld (default-state-vars nil))
            (if erp x (fn2-ecns-patch-form exp wrld))))
         ((equal x '(in-theory (disable fn2-outcome-lookup-step)))
          '(progn
             (local
              (defthm fn2-outcome-lookup-step-preserves-machines-and-cns
                (and (equal (fn2-core-machines (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-core-machines fn2-core))
                     (equal (fn2-cns-table (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-cns-table fn2-core)))
                :hints (("Goal" :in-theory (enable fn2-outcome-lookup-step fn2-read-key fn2-read-lookup fn2-read-release)))))
             (in-theory (disable fn2-outcome-lookup-step))))
         ((equal x '(in-theory (disable fn2-cns-append-read-contextp)))
          '(progn
             (in-theory (disable fn2-cns-append-read-contextp))
             (local
              (defthm fn2-cns-append-read-contextp-cns-row-guard
                (implies (fn2-cns-append-read-contextp cns gen request op fn2-core)
                         (and (equal (fn2-cns-snapshot-read-code cns fn2-core) :ok)
                              (fn2-machine-idp cns fn2-core)
                              (equal (fn2-machine-kind cns fn2-core) *fn2-cns-kind*)
                              (< (fn2-machine-slot cns fn2-core)
                                 (fn2-cns-rows (fn2-cns-table fn2-core)))))
                :rule-classes (:rewrite :forward-chaining)
                :hints (("Goal" :in-theory (enable fn2-cns-append-read-contextp
                                                   fn2-cns-snapshot-read-code
                                                   fn2-machine-phase-read-code)))))))
         ((eq (car x) 'fn2-core-preserves)
          `(encapsulate ()
             (local (in-theory (disable nfix min posp floor mod
                                        |(< x (if a b c))| |(< (if a b c) x)|)))
             ,x))
         ((and (equal (car x) 'defmachine-arms) (consp (cdr x)) (symbolp (cadr x)) (null (cddr x)))
          (let ((k (cadr x)))
            `(progn
               (make-event
                (mv-let (err events) (fn2-arms-link-core-events ',k (fn2-arms-links ',k (w state)) (w state))
                  (if err (er soft 'assembly-callbacks-e-cns "~@0" err) (value (cons 'progn events)))))
               (defcost-faces ,k)
               (make-event
                (mv-let (err form) (fn2-arms-events ',k ':core (w state))
                  (if err (er soft 'assembly-callbacks-e-cns "~@0" err)
                    (value (cons 'progn (fn2-ecns-augment-arms-list (cdr form))))))))))
         ((and (equal (car x) 'defmachine-run) (consp (cdr x)) (symbolp (cadr x)))
          (let ((k (cadr x)))
            `(make-event
              (let* ((ev (fn2-machine-run-event ',k (w state)))
                     (arm-fns (fn2-ecns-arm-fns (fn2-machine-property ',k :continuations (w state))))
                     (patched (fn2-ecns-wrap-success-charge ev ',k arm-fns)))
                (if (equal patched ev)
                    (er soft 'assembly-callbacks-e-cns "Could not patch ~x0." ',k)
                  (value patched))))))
         (t (cons (fn2-ecns-patch-form (car x) wrld) (fn2-ecns-patch-form (cdr x) wrld))))))
(defmacro fn2-ecns-fast-events (form)
  `(make-event
    (mv-let (erp exp) (macroexpand1-cmp ',form 'assembly-callbacks-e-cns (w state) (default-state-vars nil))
      (if erp (er soft 'assembly-callbacks-e-cns "Expand failed: ~x0" ',form)
        (value (fn2-ecns-patch-form exp (w state)))))))
(fn2-ecns-fast-events (fn2-auth-read-events))
(fn2-ecns-fast-events (fn2-authority-depend-events))
(fn2-ecns-fast-events (fn2-cns-events))
