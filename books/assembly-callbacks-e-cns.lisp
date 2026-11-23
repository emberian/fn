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
(local
 (defthm fn2-ecns-dir-readers-over-other-child
   (implies (not (equal (nfix k) *fn2-core-machines*))
            (and (equal (fn2-machine-idp i (update-nth k v c)) (fn2-machine-idp i c))
                 (equal (fn2-machine-kind i (update-nth k v c)) (fn2-machine-kind i c))
                 (equal (fn2-machine-slot i (update-nth k v c)) (fn2-machine-slot i c))
                 (equal (fn2-core-machines (update-nth k v c)) (fn2-core-machines c))))
   :hints (("Goal" :in-theory (enable fn2-machine-idp fn2-machine-kind fn2-machine-kind-read-code
                                      fn2-machine-slot fn2-machine-slot-read-code fn2-core-machines)))))
(local
 (defthm fn2-ecns-cns-snapshot-ok-implies-idp
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
 (defthm fn2-ecns-ctl-snapshot-ok-implies-idp
   (implies (equal (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
            (and (fn2-machine-idp ctl fn2-core)
                 (equal (fn2-machine-kind ctl fn2-core) *fn2-ctl-kind*)
                 (equal (fn2-machine-phase-read-code ctl fn2-core) :ok)
                 (equal (fn2-machine-generation-read-code ctl fn2-core) :ok)
                 (< (fn2-machine-slot ctl fn2-core) (fn2-ctl-rows (fn2-ctl-table fn2-core)))
                 (natp ctl) (integerp ctl) (<= 0 ctl)
                 (< ctl (fn2-machines-rows (fn2-core-machines fn2-core)))))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn2-ctl-snapshot-read-code fn2-machine-idp
                                      fn2-machine-phase-read-code fn2-machine-generation-read-code)))))
(make-event
 (value `(local (in-theory (disable nth fn2-reads-rows fn2-fields-rows fn2-fc-rows
                                    fn2-digests-rows fn2-b3-rows fn2-pool-fill fn2-pool-base fn2-pool-data-length
                                    fn2-cns-sources-rows fn2-ctl-rows fn2-cns-rows fn2-succ-slots-rows
                                    fn2-cns-snapshot-read-code fn2-ctl-snapshot-read-code
                                    fn2-machine-phase-read-code fn2-machine-generation-read-code
                                    fn2-cns-item-binding-answer fn2-cns-item-fits fn2-cns-put-answer)))))
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
 (defun fn2-ecns-add-cor-hints (rules)
   (declare (xargs :mode :program))
   (if (atom rules) nil
     (cons (append (car rules)
                   '(:hints (("Goal" :in-theory
                              (union-theories '(fn2-run-quantitiesp natp)
                                (union-theories (executable-counterpart-theory :here)
                                                (theory 'minimal-theory)))))))
           (fn2-ecns-add-cor-hints (cdr rules))))))
(local
 (defun fn2-ecns-patch-result-tree (x extra-dis)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((and (eq (car x) ':rule-classes) (consp (cdr x)))
          (list* ':rule-classes (fn2-ecns-add-cor-hints (cadr x))
                 (fn2-ecns-patch-result-tree (cddr x) extra-dis)))
         ((and (eq (car x) 'e/d) (consp (cdr x)) (consp (cddr x)))
          (list 'e/d (cadr x) (append extra-dis (caddr x))))
         (t (cons (fn2-ecns-patch-result-tree (car x) extra-dis)
                  (fn2-ecns-patch-result-tree (cdr x) extra-dis))))))
(local
 (defun fn2-ecns-rewrite-core-ev (x kind runp arm-fns)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((eq (car x) 'fn2-machine-core-result-events)
          `(fn2-ecns-patch-result-tree
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
         (t (cons (fn2-ecns-rewrite-core-ev (car x) kind runp arm-fns)
                  (fn2-ecns-rewrite-core-ev (cdr x) kind runp arm-fns))))))
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
 (defun fn2-ecns-augment-arms-list (xs kind)
   (declare (xargs :mode :program))
   (if (atom xs) nil
     (let ((fn (fn2-ecns-find-result-fn (car xs))))
       (cond
        (fn
         (list* `(encapsulate ()
                   (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p))))
                   ,(fn2-ecns-rewrite-core-ev (car xs) kind nil nil))
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
                (fn2-ecns-augment-arms-list (cdr xs) kind)))
        ((and (consp (car xs)) (eq (caar xs) 'progn)
              (consp (cdar xs)) (consp (cadar xs)) (eq (caadar xs) 'defun)
              (symbolp (cadr (cadar xs)))
              (search "-WRITE+" (symbol-name (cadr (cadar xs)))))
         (let ((w (cadr (cadar xs)))
               (fms (caddr (cadar xs)))
               (upd-tbl (fn2-columns-pre "UPDATE-" (fn2-columns-sym kind "-TABLE"))))
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
                                     update-fn2-core-control ,',upd-tbl
                                     fn2-machine-idp-bounds fn2-ecns-dir-readers-over-other-child
                                     ,(fn2-arm-frame-name ',w "-ARM-SLOT")
                                     ,@(fn2-arm-frame-directory-runes (strip-cars *fn2-machine-directory-fields*)))
                                   (theory 'fn2-arm-frame-base))))))))
                  `(local (in-theory (disable ,w)))
                  (fn2-ecns-augment-arms-list (cdr xs) kind))))
        ((and (consp (car xs)) (member-eq (caar xs) '(defun progn)))
         (cons `(encapsulate ()
                  (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p))))
                  ,(fn2-ecns-rewrite-core-ev (car xs) kind nil nil))
               (fn2-ecns-augment-arms-list (cdr xs) kind)))
        (t (cons (car xs) (fn2-ecns-augment-arms-list (cdr xs) kind))))))))
(local
 (defun fn2-ecns-subst-sym (new old x)
   (declare (xargs :mode :program))
   (cond ((eq x old) new)
         ((atom x) x)
         (t (cons (fn2-ecns-subst-sym new old (car x))
                  (fn2-ecns-subst-sym new old (cdr x)))))))
(local
 (defun fn2-ecns-natp-conjuncts (call idxs)
   (declare (xargs :mode :program))
   (if (atom idxs) nil
     (cons `(natp (mv-nth ,(car idxs) ,call))
           (fn2-ecns-natp-conjuncts call (cdr idxs))))))
(local
 (defun fn2-ecns-fast-natp-corollaries (name args idxs all-thm)
   (declare (xargs :mode :program))
   (if (atom idxs) nil
     (cons `(defthm ,(intern-in-package-of-symbol
                      (concatenate 'string (symbol-name name) "-NATP-"
                                   (coerce (explode-nonnegative-integer (car idxs) 10 nil) 'string))
                      name)
              (natp (mv-nth ,(car idxs) (,name ,@args)))
              :rule-classes (:rewrite :type-prescription)
              :hints (("Goal" :use ,all-thm
                              :in-theory (theory 'minimal-theory))))
           (fn2-ecns-fast-natp-corollaries name args (cdr idxs) all-thm)))))
(local
 (defun fn2-ecns-fast-natp-outputs (name args idxs extra-runes)
   (declare (xargs :mode :program))
   (let ((all-thm (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name name) "-NATP-ALL")
                   name)))
     (cons `(local
             (defthm ,all-thm
               (and ,@(fn2-ecns-natp-conjuncts (cons name args) idxs))
               :rule-classes nil
               :hints (("Goal" :do-not '(preprocess)
                               :in-theory (union-theories '(,name ,@extra-runes)
                                            (union-theories
                                             (set-difference-theories (executable-counterpart-theory :here)
                                                                      '((:executable-counterpart bubble-down)))
                                             (theory 'minimal-theory)))))))
           (fn2-ecns-fast-natp-corollaries name args idxs all-thm)))))
(local
 (defun fn2-ecns-patch-form (x wrld)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((equal x '(fn2-append-outcome-read-events))
          (mv-let (erp exp) (macroexpand1-cmp x 'assembly-callbacks-e-cns wrld (default-state-vars nil))
            (if erp x (fn2-ecns-patch-form exp wrld))))
         ((equal x '(fn2-cns-source-core-events))
          (mv-let (erp exp) (macroexpand1-cmp x 'assembly-callbacks-e-cns wrld (default-state-vars nil))
            (if erp x
              `(progn
                 (encapsulate ()
                   (local (in-theory (enable fn2-cns-rows fn2-ctl-rows fn2-cns-sources-rows)))
                   ,(fn2-ecns-patch-form exp wrld))
                 (local (in-theory (disable fn2-cns-stream-source-capture
                                            fn2-cns-stream-source-next
                                            fn2-cns-stream-source-finish
                                            fn2-cns-stream-source-abort
                                            fn2-cns-stream-source-clear
                                            fn2-cns-stream-source-issue
                                            fn2-cns-stream-source-step)))))))
         ((and (eq (car x) 'defun) (eq (cadr x) 'fn2-cns-stream-source-capture))
          (list (car x) (cadr x) (caddr x) (cadddr x)
                `(if (not (eq (fn2-cns-snapshot-read-code cns fn2-core) :ok))
                     (mv :bad 0 fn2-core)
                   ,(nth 4 x))))
         ((and (eq (car x) 'defun) (eq (cadr x) 'fn2-cns-source-preheader-quiet-p))
          (list (car x) (cadr x) (caddr x) (cadddr x)
                `(and (eq (fn2-cns-snapshot-read-code cns fn2-core) :ok)
                      (eq (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
                      ,(nth 4 x))))
         ((and (eq (car x) 'defun) (eq (cadr x) 'fn2-cns-stream-source-open))
          (list (car x) (cadr x) (caddr x) (cadddr x)
                `(if (not (eq (fn2-cns-snapshot-read-code cns fn2-core) :ok))
                     (mv :bad fn2-core)
                   ,(nth 4 x))))
         ((and (eq (car x) 'stobj-let) (equal (len x) 5)
               (equal (nth 4 x) '(mv mode fn2-reads)))
          (list (car x) (cadr x) (caddr x) (cadddr x)
                '(mv mode fn2-core)))
         ((equal x '(fn2-ctl-stream-events))
          (mv-let (erp exp) (macroexpand1-cmp x 'assembly-callbacks-e-cns wrld (default-state-vars nil))
            (if erp x (fn2-ecns-patch-form (fn2-ecns-subst-sym 'rfill 'fill exp) wrld))))
         ((equal x '(in-theory (disable fn2-outcome-lookup-step)))
          '(progn
             (local
              (defthm fn2-outcome-lookup-step-preserves-tables
                (and (equal (fn2-core-machines (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-core-machines fn2-core))
                     (equal (fn2-cns-table (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-cns-table fn2-core)))
                :hints (("Goal" :in-theory (e/d (fn2-outcome-lookup-step
                                                 fn2-read-key fn2-read-lookup fn2-read-release)
                                                (fn2-read-key-children fn2-read-lookup-children fn2-read-release-children
                                                 (:definition unsigned-byte-p) nfix min))))))
             (in-theory (disable fn2-outcome-lookup-step))
             (local
              (defthm fn2-outcome-lookup-step-preserves-machines-and-cns
                (and (equal (fn2-machine-idp cns (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-machine-idp cns fn2-core))
                     (equal (fn2-machine-kind cns (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-machine-kind cns fn2-core))
                     (equal (fn2-machine-slot cns (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-machine-slot cns fn2-core))
                     (equal (fn2-cns-row-ws-slot cns (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-cns-row-ws-slot cns fn2-core))
                     (equal (fn2-cns-row-ws-gen cns (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-cns-row-ws-gen cns fn2-core))
                     (equal (fn2-cns-row-ns-slot cns (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-cns-row-ns-slot cns fn2-core))
                     (equal (fn2-cns-row-ns-gen cns (mv-nth 1 (fn2-outcome-lookup-step x principal op budget fn2-core)))
                            (fn2-cns-row-ns-gen cns fn2-core)))
                :hints (("Goal" :in-theory (e/d (fn2-machine-idp fn2-machine-kind fn2-machine-kind-read-code
                                                 fn2-machine-slot fn2-machine-slot-read-code
                                                 fn2-cns-row-ws-slot fn2-cns-row-ws-gen
                                                 fn2-cns-row-ns-slot fn2-cns-row-ns-gen)
                                                (fn2-outcome-lookup-step))))))))
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
         ((and (eq (car x) 'defun) (eq (cadr x) 'fn2-cns-range-contextp))
          `(progn
             ,x
             (local
              (defthm fn2-ecns-read-contextp-guards
                (implies (fn2-cns-read-contextp cns gen x fn2-core)
                         (and (equal (fn2-cns-snapshot-read-code cns fn2-core) :ok)
                              (equal (fn2-machine-generation cns fn2-core) gen)
                              (equal (fn2-cns-row-xrow cns fn2-core) x)
                              (natp x) (integerp x) (<= 0 x)
                              (< x (fn2-reads-rows (fn2-core-reads fn2-core)))
                              (< x (nth *fn2-ranges-rows* (fn2-core-ranges fn2-core)))
                              (< x (nth *fn2-seeks-rows* (fn2-core-seeks fn2-core)))
                              (< (+ (nth *fn2-id-decides-rows* (fn2-core-id-decides fn2-core)) x)
                                 (nth *fn2-succ-txns-rows* (fn2-core-succ-txns fn2-core)))
                              (equal (fn2-seeks-phase x (fn2-core-seeks fn2-core))
                                     *fn2-seek-phase-idle*)))
                :rule-classes :forward-chaining
                :hints (("Goal" :in-theory (union-theories '(fn2-cns-read-contextp natp
                                                             fn2-ranges-rows fn2-seeks-rows
                                                             fn2-id-decides-rows fn2-succ-txns-rows)
                                                           (theory 'minimal-theory))))))
             (local
              (defthm fn2-ecns-range-contextp-implies-read-contextp
                (implies (fn2-cns-range-contextp cns gen x fn2-core)
                         (and (fn2-cns-read-contextp cns gen x fn2-core)
                              (equal (fn2-succ-txns-lphase
                                      (+ (nth *fn2-id-decides-rows* (fn2-core-id-decides fn2-core)) x)
                                      (fn2-core-succ-txns fn2-core))
                                     *fn2-succ-lookup-idle*)))
                :rule-classes :forward-chaining
                :hints (("Goal" :in-theory (union-theories '(fn2-cns-range-contextp fn2-id-decides-rows)
                                                           (theory 'minimal-theory))))))
             (local (in-theory (disable fn2-cns-read-contextp fn2-cns-range-contextp)))))
         ((and (eq (car x) 'defun) (eq (cadr x) 'fn2-cns-range-scalar-keyp))
          `(progn
             ,x
             (local (in-theory (disable fn2-cns-range-ownerp fn2-cns-range-scalar-keyp)))))
         ((and (eq (car x) 'defthm) (eq (cadr x) 'fn2-cns-fill-cap-types))
          `(progn
             ,x
             (local (in-theory (disable fn2-cns-fill-cap)))))
         ((and (eq (car x) 'defun)
               (member-eq (cadr x) '(fn2-cns-range-ready fn2-cns-article-ready fn2-cns-article-next)))
          `(encapsulate ()
             (local (in-theory (disable nfix min posp floor mod
                                        fn2-cns-read-row fn2-read-stripe)))
             ,(cons (car x) (cons (cadr x) (cons (caddr x) (cons (cadddr x) (fn2-ecns-patch-form (nthcdr 4 x) wrld)))))))
         ((and (eq (car x) 'defun) (eq (cadr x) 'fn2-cns-post-reply))
          `(encapsulate ()
             (local (in-theory (disable nfix min posp floor mod
                                        (:definition unsigned-byte-p) (:definition integer-range-p))))
             (defun ,(cadr x) ,(caddr x)
               (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                               :guard-hints (("Goal" :do-not '(preprocess)
                                                     :in-theory (enable fn2-core-wfp)))))
               ,@(fn2-ecns-patch-form (nthcdr 4 x) wrld))))
         ((and (eq (car x) 'fn2-core-preserves)
               (consp (cdr x))
               (eq (cadr x) 'fn2-cns-post-reply))
          `(encapsulate ()
             (local (in-theory (disable nfix min posp floor mod
                                        (:definition unsigned-byte-p) (:definition integer-range-p)
                                        |(< x (if a b c))| |(< (if a b c) x)|)))
             (fn2-core-preserves ,(cadr x) ,(caddr x)
               :position 1 :rows nil :hints (("Goal" :do-not '(preprocess) :in-theory (enable fn2-core-wfp))))))
         ((and (eq (car x) 'fn2-cns-natp-outputs)
               (consp (cdr x))
               (eq (cadr x) 'fn2-cns-article-next))
          (cons 'progn
                (fn2-ecns-fast-natp-outputs
                 (cadr x) (caddr x) (cadddr x)
                 '(fn2-cns-item-answer-types
                   (:type-prescription fn2-cns-article-ready)
                   (:type-prescription fn2-read-lookup)
                   (:type-prescription fn2-read-value)
                   (:type-prescription fn2-cns-article-answer)
                   (:type-prescription fn2-cns-fill-cap)
                   (:type-prescription fn2-cns-item-answer)
                   (:type-prescription fn2-core-reset)
                   (:type-prescription fn2-cns-stream-source-capture)
                   (:type-prescription fn2-read-octets)
                   (:type-prescription fn2-cns-article-release)))))
         ((eq (car x) 'fn2-cns-natp-outputs)
          `(encapsulate ()
             (local (in-theory (disable nfix min posp floor mod
                                        fn2-core-reset
                                        fn2-cns-snapshot-read-code fn2-ctl-snapshot-read-code
                                        fn2-machine-phase-read-code)))
             ,x))
         ((and (eq (car x) 'defthm) (eq (cadr x) 'fn2-cns-decode-port-at-types))
          `(defthm fn2-cns-decode-port-at-types
             ,(caddr x)
             :hints (("Goal" :do-not '(preprocess)
                             :in-theory (union-theories
                                          '(fn2-cns-decode-port-at natp unsigned-byte-p integer-range-p nfix
                                            (:type-prescription fn2-ctl-fc-row)
                                            (:type-prescription fn2-core-history-values)
                                            (:type-prescription fn2-cns-decode-port-pool))
                                          (union-theories
                                           (set-difference-theories (executable-counterpart-theory :here)
                                                                    '((:executable-counterpart bubble-down)))
                                           (theory 'minimal-theory)))))))
         ((and (eq (car x) 'defthm) (eq (cadr x) 'fn2-cns-decode-port-types))
          `(defthm fn2-cns-decode-port-types
             ,(caddr x)
             :hints (("Goal" :do-not '(preprocess)
                             :in-theory (union-theories
                                          '(fn2-cns-decode-port fn2-cns-decode-port-at-types
                                            (:type-prescription fn2-cns-stream-frontier)
                                            (:type-prescription fn2-cns-decode-port-at))
                                          (union-theories
                                           (set-difference-theories (executable-counterpart-theory :here)
                                                                    '((:executable-counterpart bubble-down)))
                                           (theory 'minimal-theory)))))))
         ((and (eq (car x) 'fn2-core-preserves)
               (consp (cdr x))
               (eq (cadr x) 'fn2-cns-article-next))
          `(encapsulate ()
             (local (in-theory (disable nfix min posp floor mod
                                        fn2-cns-snapshot-read-code fn2-ctl-snapshot-read-code
                                        fn2-machine-phase-read-code
                                        fn2-read-stripe
                                        |(< x (if a b c))| |(< (if a b c) x)|)))
             (fn2-core-preserves ,(cadr x) ,(caddr x)
               :position 9 :rows nil :hints (("Goal" :do-not '(preprocess) :in-theory (disable nfix))))))
         ((and (eq (car x) 'fn2-core-preserves)
               (consp (cdr x))
               (eq (cadr x) 'fn2-cns-stream-source-open))
          `(progn
             (encapsulate ()
               (local (in-theory (disable nfix min posp floor mod
                                          fn2-cns-snapshot-read-code fn2-ctl-snapshot-read-code
                                          fn2-machine-phase-read-code
                                          |(< x (if a b c))| |(< (if a b c) x)|)))
               ,x)
             (local (in-theory (disable fn2-cns-stream-source-open)))))
         ((and (eq (car x) 'fn2-core-preserves)
               (consp (cdr x)))
          `(encapsulate ()
             (local (in-theory (disable nfix min posp floor mod
                                        fn2-cns-snapshot-read-code fn2-ctl-snapshot-read-code
                                        fn2-machine-phase-read-code
                                        fn2-read-stripe
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
                    (value (cons 'progn (fn2-ecns-augment-arms-list (cdr form) ',k)))))))))
         ((and (equal (car x) 'defmachine-run) (consp (cdr x)) (symbolp (cadr x)))
          (let ((k (cadr x)))
            `(make-event
              (let* ((raw-ev (fn2-machine-run-event ',k (w state)))
                     (arm-fns (fn2-ecns-arm-fns (fn2-machine-property ',k :continuations (w state))))
                     (ev (fn2-ecns-rewrite-core-ev raw-ev ',k t arm-fns))
                     (patched (fn2-ecns-wrap-success-charge ev ',k arm-fns)))
                (cond ((and (consp raw-ev) (eq (car raw-ev) 'make-event)) (value raw-ev))
                      ((equal patched ev)
                       (er soft 'assembly-callbacks-e-cns "Could not patch ~x0." ',k))
                      (t (value patched)))))))
         (t (cons (fn2-ecns-patch-form (car x) wrld) (fn2-ecns-patch-form (cdr x) wrld))))))
(defmacro fn2-ecns-fast-events (form)
  `(make-event
    (mv-let (erp exp) (macroexpand1-cmp ',form 'assembly-callbacks-e-cns (w state) (default-state-vars nil))
      (if erp (er soft 'assembly-callbacks-e-cns "Expand failed: ~x0" ',form)
        (value (fn2-ecns-patch-form exp (w state)))))))
(fn2-ecns-fast-events (fn2-auth-read-events))
(fn2-ecns-fast-events (fn2-authority-depend-events))
(local
 (defthm fn2-ecns-b3-ready-implies-natp
   (implies (fn2-b3-ready row fn2-b3 fn2-digests)
            (and (natp row) (integerp row) (<= 0 row)))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn2-b3-ready)))))
(local
 (defthm fn2-ecns-fnct-stream-start-shape
   (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
                 (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3))
            (b* (((mv & d b) (fn2-fnct-stream-start row fn2-digests fn2-b3)))
              (and (fn2-digestsp d) (fn2-digests-wfp d)
                   (fn2-b3p b) (fn2-b3-wfp b))))
   :hints (("Goal" :in-theory (e/d (fn2-fnct-stream-start)
                                   (fn2-b3-ready fn2-digest-rowp fn2-digest-slot fn2-b3-init))))))
(local
 (defthm fn2-ecns-fnct-stream-update-shape
   (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
                 (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
                 (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
            (b* (((mv & & d b) (fn2-fnct-stream-update row slot gen off count okind oslot ogen fn2-digests fn2-b3 fn2-pool)))
              (and (fn2-digestsp d) (fn2-digests-wfp d)
                   (fn2-b3p b) (fn2-b3-wfp b))))
   :hints (("Goal" :in-theory (e/d (fn2-fnct-stream-update)
                                   (fn2-b3-ready fn2-b3-update (:definition unsigned-byte-p)))))))
(local
 (defthm fn2-ecns-fnct-stream-finish-shape
   (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
                 (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3))
            (b* (((mv & d b) (fn2-fnct-stream-finish row fn2-digests fn2-b3)))
              (and (fn2-digestsp d) (fn2-digests-wfp d)
                   (fn2-b3p b) (fn2-b3-wfp b))))
   :hints (("Goal" :in-theory (e/d (fn2-fnct-stream-finish)
                                   (fn2-b3-ready fn2-digest-rowp fn2-b3-finalize))))))
(local (in-theory (disable fn2-fnct-stream-start fn2-fnct-stream-update fn2-fnct-stream-finish)))
(fn2-ecns-fast-events (fn2-cns-events))
