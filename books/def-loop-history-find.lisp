; History cursor extension of def-loop. A first-match reader traverses the
; concrete history columns without constructing their logical list. Each
; instance names its list reference and exports the cursor equality.
(in-package "ACL2")
(include-book "def-loop")
(include-book "history-columns")
(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-dlh-consp-nthcdr
  (implies (natp k) (equal (consp (nthcdr k xs)) (< k (len xs))))
  :hints (("Goal" :induct (nthcdr k xs) :in-theory (enable nthcdr len natp zp))))

(defthm fn-dlh-car-nthcdr
  (equal (car (nthcdr k xs)) (nth k xs))
  :hints (("Goal" :induct (nthcdr k xs) :in-theory (enable nthcdr nth))))

(defthm fn-dlh-cdr-nthcdr
  (implies (natp k) (equal (cdr (nthcdr k xs)) (nthcdr (1+ k) xs)))
  :hints (("Goal" :induct (nthcdr k xs) :in-theory (enable nthcdr natp zp))))

(defmacro def-loop-history-find (name formals reference test)
  (let ((loop (intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "-FROM") name))
        (bridge (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-FROM-IS-REFERENCE") name))
        (theorem (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-IS-REFERENCE") name)))
    `(progn
       (defun ,loop (k ,@formals fn-hist)
         (declare (xargs :stobjs fn-hist :guard (natp k)
                         :measure (nfix (- (fn-hist-count fn-hist) (nfix k)))))
         (if (and (natp k) (< k (fn-hist-count fn-hist)))
             (let ((event (fn-hist-at k fn-hist)))
               (if ,test event (,loop (1+ k) ,@formals fn-hist)))
           nil))
       (defthm ,bridge
         (implies (natp k)
                  (equal (,loop k ,@formals hist)
                         (,reference ,@formals (nthcdr k hist))))
         :hints (("Goal" :induct (,loop k ,@formals hist)
                  :expand ((:free ,formals (,reference ,@formals (nthcdr k hist))))
                  :in-theory (e/d (,loop) (,reference nthcdr nth)))))
       (defun ,name (,@formals fn-hist)
         (declare (xargs :stobjs fn-hist :guard t))
         (,loop 0 ,@formals fn-hist))
       (defthm ,theorem
         (equal (,name ,@formals hist) (,reference ,@formals hist))
         :hints (("Goal" :in-theory (e/d (,name) (,reference ,loop)))))
       (in-theory (disable ,loop ,name))
       (table fn-generated ',name
              '(:def-loop :shape :history-find :loop ,loop :bridge ,bridge)))))
