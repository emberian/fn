; Batch empty control steps without buffering reply output. Each accepted
; control transition debits one visit; the first output/dependency/yield stops.
;
; With :demand-proof (the step's NAME-STEP-DEMAND-BOUND from def-cursor's
; :demand-metric) the batch takes a DEMAND budget after BYTES: it yields at
; once on a zero budget, continues past an empty control step only while
; that step's demand (the rise of (nfix D)) is below the budget left, and
; proves NAME-BATCH-DEMAND-BOUND: the whole batch raises (nfix D) by at most
; (nfix DEMAND).  A caller that passes a budget below the realizer's cache
; (fn-arx-read-cache-entries) gets a quantum whose cold misses fit it.
(in-package "ACL2")
(include-book "def-cursor")

(defmacro def-cursor/batch (name formals &key step stobjs byte-proof call-proof remaining residual-proof
                                 demand-metric demand-proof)
  (let ((batch (intern-in-package-of-symbol
                (concatenate 'string (symbol-name name) "-BATCH") name))
        (byte-bound (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-BATCH-BYTE-BOUND") name))
        (call-bound (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-BATCH-CALL-BOUND") name))
        (demand-bound (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name name) "-BATCH-DEMAND-BOUND") name))
        (source-byte (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-BYTE") name))
        (source-call (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-CALL") name))
        (source-demand (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-DEMAND") name))
        (demand-of (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-DEMAND-OF") name))
        (demand-self (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-DEMAND-OF-SELF") name))
        (demand-split (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-DEMAND-OF-SPLIT") name))
        (demand-sum (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-DEMAND-OF-BOUND") name))
        (call-type (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-CALL-NATP") name))
        (source-type (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-NATP") name))
        (source-empty (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-EMPTY") name))
        (source-rest (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-REST") name))
        (residual (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name name) "-BATCH-RESIDUAL") name)))
    (if (or (not (symbolp name)) (not (true-listp formals))
            (not (symbolp step)) (not (symbolp byte-proof))
            (not (symbolp call-proof)) (not (consp remaining))
            (not (symbolp residual-proof))
            (and (or demand-metric demand-proof)
                 (or (not (consp demand-metric)) (not (symbolp demand-proof)) (not demand-proof))))
        '(assert-event nil :msg "def-cursor/batch requires literal step contracts (and, with :demand-metric, the step's named demand bound)")
      (let* ((budget (if demand-metric '(demand) nil))
             (cur-demand (and demand-metric (subst '(fn-cur-progress cur) 'progress demand-metric)))
             (out-demand (and demand-metric
                              (subst `(fn-cur-progress (mv-nth 1 (,batch cur visits bytes ,@budget ,@formals)))
                                     'progress demand-metric)))
             (step-next `(mv-nth 1 (,step cur visits bytes ,@formals)))
             (rest-call `(mv-nth 1 (,batch ,step-next (1- visits) bytes
                                           ,@(and demand-metric `((- demand (,demand-of cur ,step-next))))
                                           ,@formals))))
      `(progn
         (make-event
          (fn-cur-visit-proof-event ',byte-proof
           '(<= (len (mv-nth 0 (,step cur visits bytes ,@formals))) (nfix bytes)) state))
         (make-event
          (fn-cur-visit-proof-event ',call-proof
           '(<= (mv-nth 2 (,step cur visits bytes ,@formals)) (nfix visits)) state))
         (make-event
          (fn-cur-visit-proof-event ',residual-proof
           '(equal (append (car (,step cur visits bytes ,@formals))
                           ,(subst `(mv-nth 1 (,step cur visits bytes ,@formals)) 'cur remaining))
                   ,remaining) state))
         ,@(if demand-metric
               `((make-event
                  (fn-cur-visit-proof-event ',demand-proof
                   '(<= (- (nfix ,(subst `(fn-cur-progress ,step-next) 'progress demand-metric))
                           (nfix ,cur-demand))
                        1) state)))
             nil)
         (local (defthm ,source-byte
           (<= (len (car (,step cur visits bytes ,@formals))) (nfix bytes))
           :rule-classes :linear
           :hints (("Goal" :use ,byte-proof :in-theory (disable ,step)))))
         (local (defthm ,source-call
           (<= (mv-nth 2 (,step cur visits bytes ,@formals)) (nfix visits))
           :rule-classes :linear
           :hints (("Goal" :use ,call-proof :in-theory (disable ,step)))))
         ,@(if demand-metric
               ; The rise of (nfix D) from one cursor to the next, as the batch
               ; computes and reasons about it: one function, opaque to every
               ; proof below but the ones that open it on purpose.
               `((defun ,demand-of (cur next)
                   (declare (xargs :guard t))
                   (- (nfix ,(subst '(fn-cur-progress next) 'progress demand-metric))
                      (nfix ,cur-demand)))
                 (local (defthm ,demand-self
                   (equal (,demand-of cur cur) 0)
                   :hints (("Goal" :in-theory (union-theories '(,demand-of) (theory 'minimal-theory))))))
                 (local (defthm ,source-demand
                   (<= (,demand-of cur ,step-next) 1)
                   :rule-classes :linear
                   :hints (("Goal" :use ,demand-proof
                            :in-theory (union-theories '(,demand-of) (theory 'minimal-theory))))))
                 (in-theory (disable ,demand-of)))
             nil)
         (local (defthm ,source-rest
           (equal (append (car (,step cur visits bytes ,@formals))
                          ,(subst `(mv-nth 1 (,step cur visits bytes ,@formals)) 'cur remaining))
                  ,remaining)
           :hints (("Goal" :use ,residual-proof
                    :in-theory (disable ,step ,(car remaining))))))
         (local (defthm ,source-empty
           (implies (not (car (,step cur visits bytes ,@formals)))
                    (equal ,(subst `(mv-nth 1 (,step cur visits bytes ,@formals)) 'cur remaining)
                           ,remaining))
           :hints (("Goal" :use ,residual-proof
                    :in-theory (disable ,step ,(car remaining) ,source-rest)))))
         (local (defthm ,source-type
           (natp (mv-nth 2 (,step cur visits bytes ,@formals)))
           :rule-classes (:rewrite :type-prescription)
           :hints (("Goal" :in-theory (enable ,step)))))
         (defun ,batch (cur visits bytes ,@budget ,@formals)
           (declare (xargs :guard (and (natp visits) (natp bytes) ,@(if demand-metric '((natp demand)) nil))
                           :measure (nfix visits)
                           ,@(if stobjs `(:stobjs ,stobjs) nil)
                           :verify-guards nil))
           ,(if demand-metric
                `(if (zp demand)
                     (mv nil cur 0 :yield)
                   (mv-let (octets next calls status) (,step cur visits bytes ,@formals)
                     (let ((d (,demand-of cur next)))
                       (if (and (not octets) (eq status :candidate)
                                (equal calls 1) (posp visits) (< d demand))
                           (mv-let (out rest more state) (,batch next (1- visits) bytes (- demand d) ,@formals)
                             (mv out rest (+ 1 more) state))
                         (mv octets next calls status)))))
              `(mv-let (octets next calls status) (,step cur visits bytes ,@formals)
                 (if (and (not octets) (eq status :candidate)
                          (equal calls 1) (posp visits))
                     (mv-let (out rest more state) (,batch next (1- visits) bytes ,@formals)
                       (mv out rest (+ 1 more) state))
                   (mv octets next calls status)))))
         (defthm ,byte-bound
           (<= (len (mv-nth 0 (,batch cur visits bytes ,@budget ,@formals))) (nfix bytes))
           :rule-classes :linear
           :hints (("Goal" :induct (,batch cur visits bytes ,@budget ,@formals)
                    :in-theory (e/d (,batch) (,step ,(car remaining))))))
         (defthm ,call-bound
           (<= (mv-nth 2 (,batch cur visits bytes ,@budget ,@formals)) (nfix visits))
           :rule-classes :linear
           :hints (("Goal" :induct (,batch cur visits bytes ,@budget ,@formals)
                    :in-theory (e/d (,batch) (,step ,(car remaining))))
                   ,@(and demand-metric
                          `((and stable-under-simplificationp
                                 '(:use (,source-call ,source-type)))))))
         (defthm ,residual
           (equal (append (car (,batch cur visits bytes ,@budget ,@formals))
                          ,(subst `(mv-nth 1 (,batch cur visits bytes ,@budget ,@formals)) 'cur remaining))
                  ,remaining)
           :rule-classes nil
           :hints (("Goal" :induct (,batch cur visits bytes ,@budget ,@formals)
                    :in-theory (e/d (,batch) (,step ,(car remaining))))))
         (defthm ,call-type
           (natp (mv-nth 2 (,batch cur visits bytes ,@budget ,@formals)))
           :rule-classes (:rewrite :type-prescription)
           :hints (("Goal" :induct (,batch cur visits bytes ,@budget ,@formals)
                    :in-theory (e/d (,batch) (,step ,(car remaining))))))
         ,@(if demand-metric
               `((local (defthm ,demand-split
                   (equal (,demand-of cur ,rest-call)
                          (+ (,demand-of cur ,step-next) (,demand-of ,step-next ,rest-call)))
                   :hints (("Goal" :in-theory (union-theories '(,demand-of) (theory 'minimal-theory))))))
                 (local (defthm ,demand-sum
                   (<= (,demand-of cur (mv-nth 1 (,batch cur visits bytes ,@budget ,@formals))) (nfix demand))
                   :rule-classes :linear
                   :hints (("Goal" :induct (,batch cur visits bytes ,@budget ,@formals)
                            :in-theory (e/d (,batch) (,step ,(car remaining)))))))
                 (defthm ,demand-bound
                   (<= (- (nfix ,out-demand) (nfix ,cur-demand)) (nfix demand))
                   :rule-classes :linear
                   :hints (("Goal" :use ,demand-sum
                            :expand ((,demand-of cur (mv-nth 1 (,batch cur visits bytes ,@budget ,@formals))))
                            :in-theory (theory 'minimal-theory)))))
             nil)
         (verify-guards ,batch
           :hints (("Goal" :in-theory (disable ,step)))))))))
