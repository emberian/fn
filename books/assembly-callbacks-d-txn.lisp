; The transaction kind's operations and continuations (D5,
; books/txn.lisp), after the upload's: their own book keeps each layer D section under the one-minute rule.
; After the control connection's section (e-cns): the append check
; (authority.lisp's fn2-authority-allows-events) reads a consumer request's
; connection and the owner's principal through its operations.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")
(include-book "assembly-callbacks-d-upload")
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
 (defun fn2-dt-rewrite-core-ev (x kind runp arm-fns)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((eq (car x) 'fn2-machine-core-result-events)
          `(fn2-dt-patch-result-tree
            ,x
            ',(append (and runp (cons (fn2-columns-sym kind "-ARM-OK-P") arm-fns))
                      (list (fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                            'fn2-machine-phase-read-code
                            '(:definition unsigned-byte-p)
                            '(:definition integer-range-p)
                            'ceiling 'floor 'mod))))
         ((eq (car x) 'fn2-core-preserves)
          `(encapsulate ()
             (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p)
                                        nfix min floor mod ceiling fn2-machine-phase-read-code
                                        ,(fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                                        ,@(and runp (cons (fn2-columns-sym kind "-ARM-OK-P") arm-fns)))))
             ,x))
         (t (cons (fn2-dt-rewrite-core-ev (car x) kind runp arm-fns)
                  (fn2-dt-rewrite-core-ev (cdr x) kind runp arm-fns))))))
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
                   ,(fn2-dt-rewrite-core-ev (car xs) 'fn2-txn nil nil))
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
                  ,(fn2-dt-rewrite-core-ev (car xs) 'fn2-txn nil nil))
               (fn2-dt-augment-arms-list (cdr xs))))
        (t (cons (car xs) (fn2-dt-augment-arms-list (cdr xs)))))))))
(local
 (defun fn2-dt-subst-sym (new old x)
   (declare (xargs :mode :program))
   (cond ((eq x old) new)
         ((atom x) x)
         (t (cons (fn2-dt-subst-sym new old (car x))
                  (fn2-dt-subst-sym new old (cdr x)))))))
(local
 (defun fn2-dt-patch-op-events (x)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((and (eq (car x) 'defun) (eq (cadr x) 'fn2-txn-post-article-result))
          `(encapsulate ()
             (local (in-theory (e/d (fn2-claim-rowp)
                                    (nth nfix min posp
                                     fn2-cns-snapshot-read-code fn2-upload-snapshot-read-code
                                     fn2-machine-phase-read-code fn2-machine-generation-read-code
                                     (:definition unsigned-byte-p) (:definition integer-range-p)))))
             (defun ,(cadr x) ,(caddr x)
               (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                               :guard-hints (("Goal" :do-not '(preprocess)))))
               ,@(nthcdr 4 x))))
         ((and (eq (car x) 'fn2-core-preserves) (consp (cdr x)) (eq (cadr x) 'fn2-txn-post-article-result))
          `(encapsulate ()
             (local (in-theory (e/d (fn2-claim-rowp)
                                    (nth nfix min posp
                                     fn2-cns-snapshot-read-code fn2-upload-snapshot-read-code
                                     fn2-machine-phase-read-code fn2-machine-generation-read-code
                                     (:definition unsigned-byte-p) (:definition integer-range-p)))))
             (fn2-core-preserves ,(cadr x) ,(caddr x)
               :position 1 :rows nil :hints (("Goal" :do-not '(preprocess))))))
         ((and (eq (car x) 'defun) (eq (cadr x) 'fn2-txn-retry-append))
          `(encapsulate ()
             (local (in-theory (disable nth nfix min posp
                                        fn2-cns-snapshot-read-code fn2-upload-snapshot-read-code
                                        fn2-machine-phase-read-code fn2-machine-generation-read-code
                                        (:definition unsigned-byte-p) (:definition integer-range-p))))
             (defun ,(cadr x) ,(caddr x)
               (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                               :guard-hints (("Goal" :do-not '(preprocess)))))
               ,@(nthcdr 4 x))))
         ((and (eq (car x) 'fn2-core-preserves) (consp (cdr x)) (eq (cadr x) 'fn2-txn-retry-append))
          `(encapsulate ()
             (local (in-theory (disable nth nfix min posp
                                        fn2-cns-snapshot-read-code fn2-upload-snapshot-read-code
                                        fn2-machine-phase-read-code fn2-machine-generation-read-code
                                        (:definition unsigned-byte-p) (:definition integer-range-p))))
             (fn2-core-preserves ,(cadr x) ,(caddr x)
               :position 1 :rows nil :hints (("Goal" :do-not '(preprocess) :in-theory (disable fn2-cns-read-append-outcome))))))
         (t (cons (fn2-dt-patch-op-events (car x))
                  (fn2-dt-patch-op-events (cdr x)))))))
(local
 (defthm fn2-dt-cns-snapshot-ok-implies-idp
   (implies (equal (fn2-cns-snapshot-read-code cns fn2-core) :ok)
            (and (fn2-machine-idp cns fn2-core)
                 (equal (fn2-machine-kind cns fn2-core) *fn2-cns-kind*)
                 (equal (fn2-machine-phase-read-code cns fn2-core) :ok)
                 (equal (fn2-machine-generation-read-code cns fn2-core) :ok)
                 (< (fn2-machine-slot cns fn2-core) (fn2-cns-rows (fn2-cns-table fn2-core)))
                 (natp cns) (integerp cns) (<= 0 cns)
                 (< cns (fn2-machines-rows (fn2-core-machines fn2-core)))))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn2-cns-snapshot-read-code fn2-machine-idp
                                      fn2-machine-phase-read-code fn2-machine-generation-read-code)))))
(local
 (defthm fn2-dt-upload-snapshot-ok-implies-idp
   (implies (equal (fn2-upload-snapshot-read-code u fn2-core) :ok)
            (and (fn2-machine-idp u fn2-core)
                 (equal (fn2-machine-kind u fn2-core) *fn2-upload-kind*)
                 (equal (fn2-machine-phase-read-code u fn2-core) :ok)
                 (equal (fn2-machine-generation-read-code u fn2-core) :ok)
                 (< (fn2-machine-slot u fn2-core) (fn2-upload-rows (fn2-upload-table fn2-core)))
                 (natp u) (integerp u) (<= 0 u)
                 (< u (fn2-machines-rows (fn2-core-machines fn2-core)))))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn2-upload-snapshot-read-code fn2-machine-idp
                                      fn2-machine-phase-read-code fn2-machine-generation-read-code)))))
(local
 (encapsulate ()
   (local
    (defthm fn2-dt-read-steps-tables
      (and (equal (fn2-core-machines (mv-nth 1 (fn2-read-key x region j val c))) (fn2-core-machines c))
           (equal (fn2-cns-table (mv-nth 1 (fn2-read-key x region j val c))) (fn2-cns-table c))
           (equal (fn2-core-machines (mv-nth 1 (fn2-read-lookup x sid budget c))) (fn2-core-machines c))
           (equal (fn2-cns-table (mv-nth 1 (fn2-read-lookup x sid budget c))) (fn2-cns-table c))
           (equal (fn2-core-machines (mv-nth 3 (fn2-read-octets x f from n dslot dgen doff dk ds dg c))) (fn2-core-machines c))
           (equal (fn2-cns-table (mv-nth 3 (fn2-read-octets x f from n dslot dgen doff dk ds dg c))) (fn2-cns-table c))
           (equal (fn2-core-machines (mv-nth 1 (fn2-read-release x c))) (fn2-core-machines c))
           (equal (fn2-cns-table (mv-nth 1 (fn2-read-release x c))) (fn2-cns-table c)))
      :hints (("Goal" :do-not '(preprocess)
                      :in-theory (union-theories
                                   '(fn2-read-key fn2-read-lookup fn2-read-octets fn2-read-release
                                     fn2-core-machines fn2-cns-table
                                     update-fn2-core-reads update-fn2-core-fields
                                     update-fn2-core-seeks update-fn2-core-ranges
                                     update-fn2-core-range-sources update-fn2-core-succ-txns
                                     update-fn2-core-run-cursors update-fn2-core-run-paths
                                     update-fn2-core-pool nth-update-nth mv-nth car-cons cdr-cons
                                     (:type-prescription fn2-read-key-children)
                                     (:type-prescription fn2-read-lookup-children)
                                     (:type-prescription fn2-read-octets-children)
                                     (:type-prescription fn2-read-release-children))
                                   (union-theories
                                    (set-difference-theories (executable-counterpart-theory :here)
                                                             '((:executable-counterpart bubble-down)))
                                    (theory 'minimal-theory)))))))
   (local
    (defthm fn2-dt-mv-nth-if
      (equal (mv-nth n (if a b c))
             (if a (mv-nth n b) (mv-nth n c)))))
   (local
    (defthm fn2-dt-tables-if
      (and (equal (fn2-core-machines (if a b c))
                  (if a (fn2-core-machines b) (fn2-core-machines c)))
           (equal (fn2-cns-table (if a b c))
                  (if a (fn2-cns-table b) (fn2-cns-table c))))))
   (local
    (defthm fn2-dt-outcome-substeps-tables
      (and (equal (fn2-core-machines (mv-nth 1 (fn2-outcome-lookup-step x principal op budget c))) (fn2-core-machines c))
           (equal (fn2-cns-table (mv-nth 1 (fn2-outcome-lookup-step x principal op budget c))) (fn2-cns-table c))
           (equal (fn2-core-machines (mv-nth 1 (fn2-cns-release-append-outcome cns gen request principal op c))) (fn2-core-machines c))
           (equal (fn2-cns-table (mv-nth 1 (fn2-cns-release-append-outcome cns gen request principal op c))) (fn2-cns-table c))
           (equal (fn2-core-machines (mv-nth 5 (fn2-cns-take-append-outcome x cns gen ws wg ns ng c))) (fn2-core-machines c))
           (equal (fn2-cns-table (mv-nth 5 (fn2-cns-take-append-outcome x cns gen ws wg ns ng c))) (fn2-cns-table c)))
      :hints (("Goal" :do-not '(preprocess)
                      :in-theory (union-theories
                                   '(fn2-outcome-lookup-step fn2-cns-release-append-outcome fn2-cns-take-append-outcome
                                     fn2-dt-read-steps-tables fn2-dt-mv-nth-if fn2-dt-tables-if
                                     mv-nth car-cons cdr-cons posp member-equal
                                     (:type-prescription fn2-outcome-read-mode)
                                     (:type-prescription fn2-read-key)
                                     (:type-prescription fn2-read-lookup)
                                     (:type-prescription fn2-read-release)
                                     (:type-prescription fn2-read-value)
                                     (:type-prescription fn2-read-octets))
                                   (union-theories
                                    (set-difference-theories (executable-counterpart-theory :here)
                                                             '((:executable-counterpart bubble-down)))
                                    (theory 'minimal-theory)))))))
   (defthm fn2-dt-read-append-outcome-tables
     (let ((c1 (mv-nth 5 (fn2-cns-read-append-outcome cns gen request principal op budget fn2-core))))
       (and (equal (fn2-core-machines c1) (fn2-core-machines fn2-core))
            (equal (fn2-cns-table c1) (fn2-cns-table fn2-core))))
     :hints (("Goal" :do-not '(preprocess)
                     :in-theory (union-theories
                                  '(fn2-cns-read-append-outcome fn2-dt-outcome-substeps-tables
                                    fn2-dt-mv-nth-if fn2-dt-tables-if
                                    mv-nth car-cons cdr-cons
                                    (:type-prescription fn2-cns-principal)
                                    (:type-prescription fn2-cns-release-append-outcome)
                                    (:type-prescription fn2-outcome-lookup-step)
                                    (:type-prescription fn2-cns-take-append-outcome))
                                  (union-theories
                                   (set-difference-theories (executable-counterpart-theory :here)
                                                            '((:executable-counterpart bubble-down)))
                                   (theory 'minimal-theory))))))))
(local
 (defthm fn2-dt-read-append-outcome-cns-ok
   (let ((c1 (mv-nth 5 (fn2-cns-read-append-outcome cns gen request principal op budget fn2-core))))
     (and (equal (fn2-machine-idp id c1) (fn2-machine-idp id fn2-core))
          (implies (equal (fn2-cns-snapshot-read-code id fn2-core) :ok)
                   (equal (fn2-cns-snapshot-read-code id c1) :ok))))
   :hints (("Goal" :do-not '(preprocess)
                   :in-theory (union-theories
                                '(fn2-dt-read-append-outcome-tables
                                  fn2-cns-snapshot-read-code fn2-machine-phase-read-code
                                  fn2-machine-idp fn2-machine-kind fn2-machine-kind-read-code
                                  fn2-machine-slot fn2-machine-slot-read-code natp)
                                (union-theories
                                 (executable-counterpart-theory :here)
                                 (theory 'minimal-theory)))))))
(make-event
 (mv-let (erp exp) (macroexpand1-cmp '(fn2-txn-op-events) 'assembly-callbacks-d-txn (w state) (default-state-vars nil))
   (if erp (er soft 'assembly-callbacks-d-txn "Expand failed: ~@0" erp)
     (value (fn2-dt-patch-op-events (fn2-dt-subst-sym 'rfill 'fill exp))))))
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
 (let* ((raw-ev (fn2-machine-run-event 'fn2-txn (w state)))
        (arm-fns (fn2-dt-arm-fns (fn2-machine-property 'fn2-txn :continuations (w state))))
        (ev (fn2-dt-rewrite-core-ev raw-ev 'fn2-txn t arm-fns))
        (patched (fn2-dt-wrap-success-charge ev 'fn2-txn arm-fns)))
   (cond ((and (consp raw-ev) (eq (car raw-ev) 'make-event)) (value raw-ev))
         ((equal patched ev)
          (er soft 'assembly-callbacks-d-txn "Could not patch fn2-txn-run-success-charge."))
         (t (value patched)))))
