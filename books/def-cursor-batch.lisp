; Batch empty control steps without buffering reply output. Each accepted
; control transition debits one visit; the first output/dependency/yield stops.
(in-package "ACL2")
(include-book "def-cursor")

(defmacro def-cursor/batch (name formals &key step stobjs byte-proof call-proof remaining residual-proof)
  (let ((batch (intern-in-package-of-symbol
                (concatenate 'string (symbol-name name) "-BATCH") name))
        (byte-bound (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-BATCH-BYTE-BOUND") name))
        (call-bound (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-BATCH-CALL-BOUND") name))
        (source-byte (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-BYTE") name))
        (source-call (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-CALL") name))
        (call-type (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-CALL-NATP") name))
        (source-type (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-NATP") name))
        (source-empty (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-EMPTY") name))
        (source-rest (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-BATCH-SOURCE-REST") name))
        (residual (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name name) "-BATCH-RESIDUAL") name)))
    (if (or (not (symbolp name)) (not (true-listp formals))
            (not (symbolp step)) (not (symbolp byte-proof))
            (not (symbolp call-proof)) (not (consp remaining))
            (not (symbolp residual-proof)))
        '(assert-event nil :msg "def-cursor/batch requires literal step contracts")
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
         (local (defthm ,source-byte
           (<= (len (car (,step cur visits bytes ,@formals))) (nfix bytes))
           :rule-classes :linear
           :hints (("Goal" :use ,byte-proof :in-theory (disable ,step)))))
         (local (defthm ,source-call
           (<= (mv-nth 2 (,step cur visits bytes ,@formals)) (nfix visits))
           :rule-classes :linear
           :hints (("Goal" :use ,call-proof :in-theory (disable ,step)))))
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
         (defun ,batch (cur visits bytes ,@formals)
           (declare (xargs :guard (and (natp visits) (natp bytes))
                           :measure (nfix visits)
                           ,@(if stobjs `(:stobjs ,stobjs) nil)
                           :verify-guards nil))
           (mv-let (octets next calls status) (,step cur visits bytes ,@formals)
             (if (and (not octets) (eq status :candidate)
                      (equal calls 1) (posp visits))
                 (mv-let (out rest more state) (,batch next (1- visits) bytes ,@formals)
                   (mv out rest (+ 1 more) state))
               (mv octets next calls status))))
         (defthm ,byte-bound
           (<= (len (mv-nth 0 (,batch cur visits bytes ,@formals))) (nfix bytes))
           :rule-classes :linear
           :hints (("Goal" :induct (,batch cur visits bytes ,@formals)
                    :in-theory (e/d (,batch) (,step ,(car remaining))))))
         (defthm ,call-bound
           (<= (mv-nth 2 (,batch cur visits bytes ,@formals)) (nfix visits))
           :rule-classes :linear
           :hints (("Goal" :induct (,batch cur visits bytes ,@formals)
                    :in-theory (e/d (,batch) (,step ,(car remaining))))))
         (defthm ,residual
           (equal (append (car (,batch cur visits bytes ,@formals))
                          ,(subst `(mv-nth 1 (,batch cur visits bytes ,@formals)) 'cur remaining))
                  ,remaining)
           :rule-classes nil
           :hints (("Goal" :induct (,batch cur visits bytes ,@formals)
                    :in-theory (e/d (,batch) (,step ,(car remaining))))))
         (defthm ,call-type
           (natp (mv-nth 2 (,batch cur visits bytes ,@formals)))
           :rule-classes (:rewrite :type-prescription)
           :hints (("Goal" :induct (,batch cur visits bytes ,@formals)
                    :in-theory (e/d (,batch) (,step ,(car remaining))))))
         (verify-guards ,batch
           :hints (("Goal" :in-theory (disable ,step))))))))
