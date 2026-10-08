; Tail-recursive resident cursor, equal to a list fold with a carried accumulator.
(in-package "ACL2")
(include-book "def-loop-history-find")

(defmacro def-loop-history-fold (name reference step)
 (let ((loop (intern-in-package-of-symbol
              (concatenate 'string (symbol-name name) "-FROM") name))
       (bridge (intern-in-package-of-symbol
              (concatenate 'string (symbol-name name) "-FROM-IS-REFERENCE") name))
       (theorem (intern-in-package-of-symbol
              (concatenate 'string (symbol-name name) "-IS-REFERENCE") name)))
  `(progn
    (defun ,loop (k acc fn-hist)
     (declare (xargs :stobjs fn-hist :guard (natp k)
                     :measure (nfix (- (fn-hist-count fn-hist) (nfix k)))))
     (if (and (natp k) (< k (fn-hist-count fn-hist)))
         (let ((event (fn-hist-at k fn-hist)))
          (,loop (1+ k) ,step fn-hist))
       acc))
    (defthm ,bridge
     (implies (natp k)
      (equal (,loop k acc hist) (,reference (nthcdr k hist) acc)))
     :hints (("Goal" :induct (,loop k acc hist)
       :expand ((:free (acc) (,reference (nthcdr k hist) acc)))
       :in-theory (e/d (,loop) (,reference nthcdr nth)))))
    (defun ,name (acc fn-hist)
     (declare (xargs :stobjs fn-hist :guard t))
     (,loop 0 acc fn-hist))
    (defthm ,theorem
     (equal (,name acc hist) (,reference hist acc))
     :hints (("Goal" :in-theory (e/d (,name) (,reference ,loop)))))
    (in-theory (disable ,loop ,name))
    (table fn-generated ',name
      '(:def-loop :shape :history-fold :loop ,loop :bridge ,bridge)))))
