; The transaction kind's operations and continuations (D5,
; books/txn.lisp), after the upload's: their own book keeps each layer D section under the one-minute rule.
; After the control connection's section (e-cns): the append check
; (authority.lisp's fn2-authority-allows-events) reads a consumer request's
; connection and the owner's principal through its operations.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")
(include-book "txn")
(include-book "authority")
(local (defun fn2-dt-core-child-type-terms (children)
         (declare (xargs :verify-guards nil))
         (if (atom children) nil
           (cons `(,(fn2-columns-sym (cadar children) "P") (,(caar children) fn2-core))
                 (fn2-dt-core-child-type-terms (cdr children))))))
(make-event
 (value `(local (defthm fn2-dt-core-child-types-fc
                  (implies (fn2-corep fn2-core)
                           (and ,@(fn2-dt-core-child-type-terms *fn2-core-children*)))
                  :rule-classes :forward-chaining))))
(make-event
 (value `(local (in-theory (enable ,@(fn2-core-child-wfp-forward-runes *fn2-core-children*))))))
(local
 (defthm fn2-dt-dir-readers-over-other-child
   (implies (not (equal (nfix k) *fn2-core-machines*))
            (and (equal (fn2-machine-idp i (update-nth k v c)) (fn2-machine-idp i c))
                 (equal (fn2-machine-kind i (update-nth k v c)) (fn2-machine-kind i c))
                 (equal (fn2-machine-slot i (update-nth k v c)) (fn2-machine-slot i c))
                 (equal (fn2-core-machines (update-nth k v c)) (fn2-core-machines c))))
   :hints (("Goal" :in-theory (enable fn2-machine-idp fn2-machine-kind fn2-machine-kind-read-code
                                      fn2-machine-slot fn2-machine-slot-read-code fn2-core-machines)))))
(local
 (defun fn2-dt-arm-fns (arms)
   (declare (xargs :mode :program))
   (if (atom arms) nil (cons (cadar arms) (fn2-dt-arm-fns (cdr arms))))))
(local
 (defun fn2-dt-wrap-success-charge (x kind arm-fns)
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
         (t (cons (fn2-dt-wrap-success-charge (car x) kind arm-fns)
                  (fn2-dt-wrap-success-charge (cdr x) kind arm-fns))))))
(local
 (defun fn2-dt-add-cor-hints (rules)
   (declare (xargs :mode :program))
   (if (atom rules) nil
     (cons (append (car rules)
                   '(:hints (("Goal" :in-theory
                              (union-theories '(fn2-run-quantitiesp natp)
                                (union-theories (executable-counterpart-theory :here)
                                                (theory 'minimal-theory)))))))
           (fn2-dt-add-cor-hints (cdr rules))))))
(local
 (defun fn2-dt-patch-result-tree (x extra-dis)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((and (eq (car x) ':rule-classes) (consp (cdr x)))
          (list* ':rule-classes (fn2-dt-add-cor-hints (cadr x))
                 (fn2-dt-patch-result-tree (cddr x) extra-dis)))
         ((and (eq (car x) 'e/d) (consp (cdr x)) (consp (cddr x)))
          (list 'e/d (cadr x) (append extra-dis (caddr x))))
         (t (cons (fn2-dt-patch-result-tree (car x) extra-dis)
                  (fn2-dt-patch-result-tree (cdr x) extra-dis))))))
(local
 (defun fn2-dt-rewrite-core-ev (x kind)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((eq (car x) 'fn2-machine-core-result-events)
          `(fn2-dt-patch-result-tree
            ,x
            ',(list (fn2-columns-sym kind "-ARM-OK-P")
                    (fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                    'fn2-machine-phase-read-code
                    '(:definition unsigned-byte-p)
                    '(:definition integer-range-p)
                    'ceiling 'floor 'mod 'min)))
         ((eq (car x) 'fn2-core-preserves)
          `(encapsulate ()
             (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p)
                                        nfix min floor mod ceiling fn2-machine-phase-read-code
                                        ,(fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                                        ,(fn2-columns-sym kind "-ARM-OK-P"))))
             ,x))
         (t (cons (fn2-dt-rewrite-core-ev (car x) kind)
                  (fn2-dt-rewrite-core-ev (cdr x) kind))))))
(local
 (defun fn2-dt-find-result-fn (x)
   (declare (xargs :mode :program))
   (cond ((atom x) nil)
         ((and (eq (car x) 'fn2-machine-core-result-events)
               (consp (cdr x)) (consp (cadr x)) (eq (caadr x) 'quote))
          (cadadr x))
         (t (or (fn2-dt-find-result-fn (car x))
                (fn2-dt-find-result-fn (cdr x)))))))
(local
 (defun fn2-dt-augment-arms-list (xs)
   (declare (xargs :mode :program))
   (if (atom xs) nil
     (let ((fn (fn2-dt-find-result-fn (car xs))))
       (cond
        (fn
         (list* `(encapsulate ()
                   (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p))))
                   ,(fn2-dt-rewrite-core-ev (car xs) 'fn2-txn))
                `(local
                  (make-event
                   (let ((guard (getpropc ',fn 'guard t (w state)))
                         (iss (fn2-columns-sym ',fn "-ISSUED-EFFECT"))
                         (qnt (fn2-columns-sym ',fn "-QUANTITIES"))
                         (nums (fn2-columns-sym ',fn "-RESULT-NUMBERS"))
                         (gen (fn2-columns-sym ',fn "-ISSUED-EFFECT-GENERAL-N")))
                     (value
                      `(progn
                         (defthm ,nums
                           (implies (and (fn2-corep fn2-core) ,guard)
                                    (and (natp (car (,',fn id budget fn2-core)))
                                         (integerp (car (,',fn id budget fn2-core)))
                                         (<= 0 (car (,',fn id budget fn2-core)))
                                         (acl2-numberp (car (,',fn id budget fn2-core)))
                                         (natp (mv-nth 1 (,',fn id budget fn2-core)))
                                         (integerp (mv-nth 1 (,',fn id budget fn2-core)))
                                         (<= 0 (mv-nth 1 (,',fn id budget fn2-core)))
                                         (acl2-numberp (mv-nth 1 (,',fn id budget fn2-core)))
                                         (natp (mv-nth 2 (,',fn id budget fn2-core)))
                                         (integerp (mv-nth 2 (,',fn id budget fn2-core)))
                                         (<= 0 (mv-nth 2 (,',fn id budget fn2-core)))
                                         (acl2-numberp (mv-nth 2 (,',fn id budget fn2-core)))))
                           :rule-classes (:rewrite
                                          (:linear :corollary
                                           (implies (and (fn2-corep fn2-core) ,guard)
                                                    (and (<= 0 (car (,',fn id budget fn2-core)))
                                                         (<= 0 (mv-nth 1 (,',fn id budget fn2-core)))
                                                         (<= 0 (mv-nth 2 (,',fn id budget fn2-core)))))))
                           :hints (("Goal" :use ,qnt
                                           :in-theory (e/d (fn2-run-quantitiesp)
                                                           (,qnt ,',fn fn2-corep fn2-core-wfp)))))
                         (defthm ,gen
                           (implies (and (equal n (fn2-ops-rows (fn2-core-ops fn2-core)))
                                         (fn2-corep fn2-core)
                                         ,guard)
                                    (equal (fn2-ops-issued-count n (fn2-core-ops (mv-nth 4 (,',fn id budget fn2-core))))
                                           (+ (fn2-ops-issued-count n (fn2-core-ops fn2-core))
                                              (mv-nth 2 (,',fn id budget fn2-core)))))
                           :hints (("Goal" :use ,iss
                                           :in-theory (disable ,iss ,',fn fn2-core-ops fn2-corep fn2-core-wfp
                                                               fn2-ops-issued-count fn2-ops-rows)))))))))
                (fn2-dt-augment-arms-list (cdr xs))))
        ((and (consp (car xs)) (eq (caar xs) 'progn)
              (consp (cdar xs)) (consp (cadar xs)) (eq (caadar xs) 'defun)
              (symbolp (cadr (cadar xs)))
              (search "-WRITE+" (symbol-name (cadr (cadar xs)))))
         (let ((w (cadr (cadar xs)))
               (fms (caddr (cadar xs))))
           (list* `(encapsulate ()
                     (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p))))
                     ,(car xs))
                  `(local
                    (make-event
                     (value
                      `(defthm ,(fn2-columns-sym ',w "-PRESERVES-MACHINE-DIR")
                         (and (equal (fn2-machine-idp fn2-any-id (,',w ,@',fms)) (fn2-machine-idp fn2-any-id fn2-core))
                              (equal (fn2-machine-kind fn2-any-id (,',w ,@',fms)) (fn2-machine-kind fn2-any-id fn2-core))
                              (equal (fn2-machine-slot fn2-any-id (,',w ,@',fms)) (fn2-machine-slot fn2-any-id fn2-core)))
                         :hints (("Goal" :in-theory
                                  (union-theories
                                   '(,',w fn2-machine-refuse-write fn2-core-stop fn2-control-record-stop
                                     update-fn2-core-control update-fn2-txn-table
                                     fn2-machine-idp-bounds fn2-dt-dir-readers-over-other-child
                                     ,(fn2-arm-frame-name ',w "-ARM-SLOT")
                                     ,@(fn2-arm-frame-directory-runes (strip-cars *fn2-machine-directory-fields*)))
                                   (theory 'fn2-arm-frame-base))))))))
                  `(local (in-theory (disable ,w)))
                  (fn2-dt-augment-arms-list (cdr xs)))))
        ((and (consp (car xs)) (member-eq (caar xs) '(defun progn)))
         (cons `(encapsulate ()
                  (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p))))
                  ,(fn2-dt-rewrite-core-ev (car xs) 'fn2-txn))
               (fn2-dt-augment-arms-list (cdr xs))))
        (t (cons (car xs) (fn2-dt-augment-arms-list (cdr xs)))))))))
(fn2-txn-op-events)
(fn2-authority-allows-events)
(assert-event (equal *fn2-auth-depend-slot* *fn2-txn-slot-depend*))
(make-event
 (mv-let (err events) (fn2-arms-link-core-events 'fn2-txn (fn2-arms-links 'fn2-txn (w state)) (w state))
   (if err (er soft 'assembly-callbacks-d-txn "~@0" err) (value (cons 'progn events)))))
(defcost-faces fn2-txn)
(make-event
 (mv-let (err form) (fn2-arms-events 'fn2-txn ':core (w state))
   (if err (er soft 'assembly-callbacks-d-txn "~@0" err)
     (value (cons 'progn (fn2-dt-augment-arms-list (cdr form)))))))
(make-event
 (let* ((ev (fn2-dt-rewrite-core-ev (fn2-machine-run-event 'fn2-txn (w state)) 'fn2-txn))
        (arm-fns (fn2-dt-arm-fns (fn2-machine-property 'fn2-txn :continuations (w state))))
        (patched (fn2-dt-wrap-success-charge ev 'fn2-txn arm-fns)))
   (if (equal patched ev)
       (er soft 'assembly-callbacks-d-txn "Could not patch fn2-txn-run-success-charge.")
     (value patched))))
