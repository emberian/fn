; The commit kind's second section, second half: install, publish,
; settlement, drop and the drain's operations, then the kind's arms
; (commit-arms.lisp, generated here) and its run (split from
; assembly-callbacks-r under the one-minute rule).
(in-package "ACL2")

(include-book "commit-arms")
(local (assert-event (and (function-symbolp 'fn2-commit-phase (w state))
                          (function-symbolp 'fn2-commit-table (w state))
                          (function-symbolp 'fn2-machine-slot (w state))
                          (function-symbolp 'fn2-commit-row-phase (w state)))))
(local (defun fn2-r2-mentions-sym-p (sym x)
         (declare (xargs :guard (symbolp sym)))
         (if (atom x)
             (eq x sym)
           (or (fn2-r2-mentions-sym-p sym (car x))
               (fn2-r2-mentions-sym-p sym (cdr x))))))
(local (defun fn2-r2-phase-cases (term n)
         (declare (xargs :guard (natp n)))
         (if (zp n)
             (list (list 'equal term 0))
           (cons (list 'equal term n)
                 (fn2-r2-phase-cases term (- n 1))))))
(local (set-default-hints '((and (consp id)
                                 (null (cadr id))
                                 (eql (cddr id) 0)
                                 (<= (len (car id)) 2)
                                 (fn2-r2-mentions-sym-p 'fn2-retirement-control-set-install-offset clause)
                                 '(:do-not '(preprocess))))))
(local
 (defthm fn2-r2-contract-check-projections
   (and (equal (car (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)) bytes)
        (equal (mv-nth 0 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)) bytes)
        (equal (mv-nth 1 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)) steps)
        (equal (mv-nth 2 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)) descriptors)
        (equal (fn2-core-success-p (mv-nth 4 (fn2-machine-contract-check ok bytes steps descriptors runnable fn2-core)))
               (and (if ok t nil) (fn2-core-success-p fn2-core)))
        (equal (fn2-core-success-p (mv-nth 4 (fn2-machine-refuse-phase id fn2-core)))
               nil))
   :hints (("Goal" :in-theory (enable fn2-machine-contract-check fn2-machine-refuse-phase
                                      fn2-machine-finish fn2-machine-refuse-write)))))
(local
 (defthm fn2-r2-commit-row-phase-when-ok
   (implies (equal (fn2-commit-snapshot-read-code id fn2-core) :ok)
            (equal (fn2-commit-row-phase id fn2-core)
                   (fn2-machine-phase id fn2-core)))
   :hints (("Goal" :in-theory (enable fn2-commit-row-phase fn2-commit-snapshot-read-code
                                      fn2-machine-phase fn2-machine-phase-read-code)))))
(local (add-override-hints
        '((cond ((and (equal id '((0) nil . 0))
                      (fn2-r2-mentions-sym-p 'fn2-commit-run clause)
                      (fn2-r2-mentions-sym-p 'fn2-commit-arm-charge-ok-p clause))
                 (list :do-not ''(preprocess)
                       :cases (fn2-r2-phase-cases '(fn2-machine-phase id fn2-core) 12)
                       :in-theory '(e/d (fn2-commit-run fn2-commit-arm-ok-p fn2-core-success-p)
                                         (fn2-machine-contract-check fn2-machine-refuse-phase
                                          fn2-commit-snapshot-read-code fn2-commit-row-phase fn2-machine-phase
                                          fn2-core-stopped-p fn2-core-stop-reason
                                          fn2-commit-arm-charge-ok-p fn2-commit-arm-next-ok-p
                                          fn2-commit-run-free fn2-commit-run-collect fn2-commit-run-seal
                                          fn2-commit-run-dependencies fn2-commit-run-log-write
                                          fn2-commit-run-fence fn2-commit-run-durable
                                          fn2-commit-run-install fn2-commit-run-publish
                                          fn2-commit-run-notify fn2-commit-run-draining
                                          fn2-commit-run-uncertain fn2-commit-run-dropping))))
                (t keyword-alist)))))
(local (in-theory (disable fn2-alloc-frozenp fn2-alloc-snapshot-activep
                           fn2-format-allocation-decode fn2-checkpoint-allocation-install
                           fn2-format-checkpoint-installation-decode fn2-checkpoint-install
                           fn2-checkpoint-staging-match-p fn2-alloc-retirement-intentp)))
(local
 (defun fn2-r2-child-rows-natp-rewrites (children world)
   (declare (xargs :verify-guards nil))
   (if (atom children) nil
     (let* ((type (cadar children))
            (pred (fn2-columns-sym type "P"))
            (rows (fn2-columns-sym type "-ROWS")))
       (if (and (fn2-decl-row (list :columns type) world)
                (function-symbolp rows world))
           (cons `(defthm ,(fn2-columns-sym rows "-NATP-REWRITE-R2")
                    (implies (,pred x)
                             (and (integerp (,rows x))
                                  (rationalp (,rows x))
                                  (acl2-numberp (,rows x))
                                  (<= 0 (,rows x)))))
                 (fn2-r2-child-rows-natp-rewrites (cdr children) world))
         (fn2-r2-child-rows-natp-rewrites (cdr children) world))))))
(make-event
 (value `(progn ,@(fn2-r2-child-rows-natp-rewrites *fn2-core-children* (w state)))))
(make-event
 (value `(local (in-theory (disable ,@(fn2-columns-getter-runes
                                       '(fn2-extents fn2-checkpoint-construction
                                         fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                         fn2-retirement-control fn2-checkpoint-future
                                         fn2-checkpoint-future-windows fn2-fields)
                                       (w state)))))))
(local
 (defthm fn2-r2-commit-member-ws-types
   (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
            (and (integerp (mv-nth 1 (fn2-commit-member-ws r fn2-core)))
                 (rationalp (mv-nth 1 (fn2-commit-member-ws r fn2-core)))
                 (acl2-numberp (mv-nth 1 (fn2-commit-member-ws r fn2-core)))
                 (<= 0 (mv-nth 1 (fn2-commit-member-ws r fn2-core)))
                 (integerp (mv-nth 2 (fn2-commit-member-ws r fn2-core)))
                 (rationalp (mv-nth 2 (fn2-commit-member-ws r fn2-core)))
                 (acl2-numberp (mv-nth 2 (fn2-commit-member-ws r fn2-core)))
                 (<= 0 (mv-nth 2 (fn2-commit-member-ws r fn2-core)))
                 (integerp (mv-nth 3 (fn2-commit-member-ws r fn2-core)))
                 (rationalp (mv-nth 3 (fn2-commit-member-ws r fn2-core)))
                 (acl2-numberp (mv-nth 3 (fn2-commit-member-ws r fn2-core)))
                 (<= 0 (mv-nth 3 (fn2-commit-member-ws r fn2-core)))
                 (integerp (mv-nth 4 (fn2-commit-member-ws r fn2-core)))
                 (rationalp (mv-nth 4 (fn2-commit-member-ws r fn2-core)))
                 (acl2-numberp (mv-nth 4 (fn2-commit-member-ws r fn2-core)))
                 (<= 0 (mv-nth 4 (fn2-commit-member-ws r fn2-core)))
                 (integerp (mv-nth 5 (fn2-commit-member-ws r fn2-core)))
                 (rationalp (mv-nth 5 (fn2-commit-member-ws r fn2-core)))
                 (acl2-numberp (mv-nth 5 (fn2-commit-member-ws r fn2-core)))
                 (<= 0 (mv-nth 5 (fn2-commit-member-ws r fn2-core)))
                 (integerp (mv-nth 6 (fn2-commit-member-ws r fn2-core)))
                 (rationalp (mv-nth 6 (fn2-commit-member-ws r fn2-core)))
                 (acl2-numberp (mv-nth 6 (fn2-commit-member-ws r fn2-core)))
                 (<= 0 (mv-nth 6 (fn2-commit-member-ws r fn2-core)))
                 (integerp (mv-nth 7 (fn2-commit-member-ws r fn2-core)))
                 (rationalp (mv-nth 7 (fn2-commit-member-ws r fn2-core)))
                 (acl2-numberp (mv-nth 7 (fn2-commit-member-ws r fn2-core)))
                 (<= 0 (mv-nth 7 (fn2-commit-member-ws r fn2-core)))))
   :hints (("Goal" :use (fn2-core-commit-members-type fn2-commit-member-wfp-of-fn2-core-commit-members)
                   :in-theory (e/d (fn2-commit-member-ws)
                                   (fn2-core-commit-members-type
                                    fn2-commit-member-wfp-of-fn2-core-commit-members
                                    fn2-commit-member-rows fn2-commit-member-kind fn2-commit-member-slot
                                    fn2-commit-member-gen fn2-commit-member-len fn2-commit-member-okind
                                    fn2-commit-member-oslot fn2-commit-member-ogen nfix))))))
(local
 (defthm fn2-r2-fields-value-numberp
   (implies (and (fn2-fieldsp x) (fn2-fields-wfp x) (natp i) (< i (fn2-fields-rows x)))
            (and (integerp (fn2-fields-value i x))
                 (rationalp (fn2-fields-value i x))
                 (acl2-numberp (fn2-fields-value i x))
                 (<= 0 (fn2-fields-value i x))
                 (integerp (fn2-fields-decode-next i x))
                 (rationalp (fn2-fields-decode-next i x))
                 (acl2-numberp (fn2-fields-decode-next i x))
                 (<= 0 (fn2-fields-decode-next i x))))))
(local
 (defthm fn2-r2-format-retirement-scan-end-natp
   (implies (natp next)
            (and (integerp (mv-nth 1 (fn2-format-retirement-scan
                                      fuel base phase pos v hi size ref payload next
                                      slot gen end okind oslot ogen fn2-fields fn2-pool)))
                 (<= 0 (mv-nth 1 (fn2-format-retirement-scan
                                  fuel base phase pos v hi size ref payload next
                                  slot gen end okind oslot ogen fn2-fields fn2-pool)))))
   :hints (("Goal" :in-theory (e/d (fn2-format-retirement-scan)
                                   (fn2-pool-read fn2-layout-store fn2-codec-save))))))
(local
 (defthm fn2-r2-format-retirement-decode-end-numberp
   (implies (and (natp off) (natp base) (< base (fn2-fields-rows fn2-fields))
                 (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))
            (and (integerp (mv-nth 1 (fn2-format-retirement-decode
                                      base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
                 (rationalp (mv-nth 1 (fn2-format-retirement-decode
                                       base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
                 (acl2-numberp (mv-nth 1 (fn2-format-retirement-decode
                                          base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
                 (<= 0 (mv-nth 1 (fn2-format-retirement-decode
                                  base slot gen off end okind oslot ogen fn2-fields fn2-pool)))))
   :hints (("Goal" :in-theory (e/d (fn2-format-retirement-decode fn2-format-retirement-decode-step)
                                   (fn2-format-retirement-scan fn2-layout-range-code fn2-fields-decode-next))))))
(fn2-commit-events-2b)
