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
(local (in-theory (disable fn2-ecns-core-success-p-dest)))
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
                ;; The nested key reads and successor writes duplicate their
                ;; intermediate cores during guard and preservation preprocessing.
                ((and (consp ctx)
                      (member-eq (cdr ctx)
                                 '(fn2-cns-article-next-natp-1 fn2-cns-article-next-natp-2
                                   fn2-cns-article-next-natp-3 fn2-cns-article-next-natp-4
                                   fn2-cns-article-next-natp-5 fn2-cns-article-next-natp-6
                                   fn2-cns-article-next-natp-7 fn2-cns-article-next-natp-8)))
                 '(:do-not '(preprocess)
                   :in-theory (union-theories
                                '(fn2-cns-article-next fn2-cns-item-answer-types
                                  (:type-prescription fn2-cns-article-ready)
                                  (:type-prescription fn2-read-lookup)
                                  (:type-prescription fn2-read-value)
                                  (:type-prescription fn2-cns-article-answer)
                                  (:type-prescription fn2-cns-fill-cap)
                                  (:type-prescription fn2-cns-item-answer)
                                  (:type-prescription fn2-core-reset)
                                  (:type-prescription fn2-cns-stream-source-capture)
                                  (:type-prescription fn2-read-octets)
                                  (:type-prescription fn2-cns-article-release))
                                (union-theories
                                 (set-difference-theories (executable-counterpart-theory :here)
                                                          '((:executable-counterpart bubble-down)))
                                 (theory 'minimal-theory)))))
                ((and (consp ctx) (eq (cdr ctx) 'fn2-cns-decode-port-at-types))
                 '(:do-not '(preprocess)
                   :in-theory (union-theories
                                '(fn2-cns-decode-port-at natp unsigned-byte-p integer-range-p nfix
                                  (:type-prescription fn2-ctl-fc-row)
                                  (:type-prescription fn2-core-history-values)
                                  (:type-prescription fn2-cns-decode-port-pool))
                                (union-theories
                                 (set-difference-theories (executable-counterpart-theory :here)
                                                          '((:executable-counterpart bubble-down)))
                                 (theory 'minimal-theory)))))
                ((and (consp ctx) (eq (cdr ctx) 'fn2-cns-decode-port-types))
                 '(:do-not '(preprocess)
                   :in-theory (union-theories
                                '(fn2-cns-decode-port fn2-cns-decode-port-at-types
                                  (:type-prescription fn2-cns-stream-frontier)
                                  (:type-prescription fn2-cns-decode-port-at))
                                (union-theories
                                 (set-difference-theories (executable-counterpart-theory :here)
                                                          '((:executable-counterpart bubble-down)))
                                 (theory 'minimal-theory)))))
                ((and (consp ctx)
                      (member-eq (cdr ctx)
                                 '(fn2-auth-find-current fn2-auth-find-current-preserves-type
                                   fn2-auth-find-current-preserves-wfp
                                   fn2-authority-depend fn2-authority-depend-preserves-type
                                   fn2-authority-depend-preserves-wfp
                                   fn2-cns-article-next-preserves-type
                                   fn2-cns-article-next-preserves-wfp
                                   fn2-cns-post-reply
                                   fn2-cns-post-reply-preserves-type
                                   fn2-cns-post-reply-preserves-wfp)))
                 (append '(:do-not '(preprocess)) keyword-alist))
                ((and (fn2-ecns-mentions-sym-p 'fn2-ctl-run clause)
                      (fn2-ecns-mentions-sym-p 'fn2-ctl-arm-charge-ok-p clause))
                 (list :cases (fn2-ecns-phase-cases '(fn2-machine-phase id fn2-core)
                                (max 0 (1- (len (fn2-machine-property 'fn2-ctl :states world)))))
                       :in-theory (list 'e/d
                                        '(fn2-ctl-run fn2-ctl-arm-ok-p fn2-ecns-core-success-p-dest)
                                        (fn2-ecns-success-charge-disables 'fn2-ctl world))))
                ((and (fn2-ecns-mentions-sym-p 'fn2-cns-run clause)
                      (fn2-ecns-mentions-sym-p 'fn2-cns-arm-charge-ok-p clause))
                 (list :cases (fn2-ecns-phase-cases '(fn2-machine-phase id fn2-core)
                                (max 0 (1- (len (fn2-machine-property 'fn2-cns :states world)))))
                       :in-theory (list 'e/d
                                        '(fn2-cns-run fn2-cns-arm-ok-p fn2-ecns-core-success-p-dest)
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

; Install the leaf's guard facts as soon as both context predicates exist.
(local
 (defun fn2-ecns-insert-context-guards (events)
   (declare (xargs :guard (true-listp events)))
   (cond
    ((endp events) nil)
    ((let ((event (car events)))
       (case-match event (('defun 'fn2-cns-range-contextp . &) t)))
     (list*
      (car events)
      '(local
        (defthm fn2-ecns-read-contextp-guards
          (implies (fn2-cns-read-contextp cns gen x fn2-core)
                   (and (equal (fn2-cns-snapshot-read-code cns fn2-core) :ok)
                        (equal (fn2-machine-generation cns fn2-core) gen)
                        (equal (fn2-cns-row-xrow cns fn2-core) x)
                        (natp x) (integerp x) (<= 0 x)
                        (< x (fn2-reads-rows (fn2-core-reads fn2-core)))
                        (< x (nth *fn2-ranges-rows* (fn2-core-ranges fn2-core)))
                        (< x (nth *fn2-seeks-rows* (fn2-core-seeks fn2-core)))
                        (< (+ (fn2-id-decides-rows (fn2-core-id-decides fn2-core)) x)
                           (nth *fn2-succ-txns-rows* (fn2-core-succ-txns fn2-core)))
                        (equal (fn2-seeks-phase x (fn2-core-seeks fn2-core))
                               *fn2-seek-phase-idle*)))
          :rule-classes :forward-chaining
          :hints (("Goal" :in-theory (union-theories '(fn2-cns-read-contextp natp
                                                       fn2-ranges-rows fn2-seeks-rows
                                                       fn2-succ-txns-rows)
                                                     (theory 'minimal-theory))))))
      '(local
        (defthm fn2-ecns-range-contextp-implies-read-contextp
          (implies (fn2-cns-range-contextp cns gen x fn2-core)
                   (and (fn2-cns-read-contextp cns gen x fn2-core)
                        (equal (fn2-succ-txns-lphase
                                (+ (fn2-id-decides-rows (fn2-core-id-decides fn2-core)) x)
                                (fn2-core-succ-txns fn2-core))
                               *fn2-succ-lookup-idle*)))
          :rule-classes :forward-chaining
          :hints (("Goal" :in-theory (union-theories '(fn2-cns-range-contextp)
                                                     (theory 'minimal-theory))))))
      '(local (in-theory (disable fn2-cns-read-contextp fn2-cns-range-contextp)))
      (cdr events)))
    (t (let ((tail (fn2-ecns-insert-context-guards (cdr events))))
         (and tail (cons (car events) tail)))))))
(make-event
 (mv-let (erp expansion)
   (macroexpand1-cmp '(fn2-cns-events) 'assembly-callbacks-e-cns (w state) (default-state-vars nil))
   (let ((events (and (not erp) (eq (car expansion) 'progn)
                      (fn2-ecns-insert-context-guards (cdr expansion)))))
     (if events (value (cons 'progn events))
       (er soft 'assembly-callbacks-e-cns "Missing FN2-CNS-RANGE-CONTEXTP in FN2-CNS-EVENTS.")))))
