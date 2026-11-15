; Constant-size row exchange generated from the canonical column declaration.
; Extra fields are global carrier state and intentionally remain untouched.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defun fn2-columns-swap-saves (name cols)
 (declare (xargs :verify-guards nil))
 (if (atom cols) nil
  (cons (list (fn2-columns-col-name name (fn2-columns-pre "OLD-" (caar cols)))
              (list (fn2-columns-col-name name (caar cols)) 'left name))
        (fn2-columns-swap-saves name (cdr cols)))))
(defun fn2-columns-swap-writes (name cols rightp)
 (declare (xargs :verify-guards nil))
 (if (atom cols) nil
  (cons (list name
         (list (fn2-columns-col-name name (fn2-columns-pre "SET-" (caar cols)))
               (if rightp 'right 'left)
               (if rightp (fn2-columns-col-name name (fn2-columns-pre "OLD-" (caar cols)))
                 (list (fn2-columns-col-name name (caar cols)) 'right name)) name))
        (fn2-columns-swap-writes name (cdr cols) rightp))))
; Logical model only: copy the declared scalar columns from an immutable
; source snapshot. Executable source operations never construct this list.
(defun-nx fn2-columns-row-copy-model (n dst src original table)
 (declare (xargs :measure (nfix n)))
 (if (zp n) table
  (let* ((i (- (nfix n) 1))
         (table (fn2-columns-row-copy-model i dst src original table)))
   (update-nth i (update-nth dst (nth src (nth i original)) (nth i table)) table))))
(defun-nx fn2-columns-row-swap-model (n left right table)
 (fn2-columns-row-copy-model n right left table
  (fn2-columns-row-copy-model n left right table table)))
(defun fn2-columns-row-swap-events (name cols)
 (declare (xargs :verify-guards nil))
 (let* ((fn (fn2-columns-sym name "-SWAP-ROWS"))
        (wfp (fn2-columns-sym name "-WFP")) (rows (fn2-columns-sym name "-ROWS"))
        (preserves (fn2-columns-sym name "-PRESERVES")))
  `(progn
    (defun ,fn (left right ,name)
     (declare (xargs :stobjs ,name :guard (and (,wfp ,name) (natp left) (natp right)
                                              (< left (,rows ,name)) (< right (,rows ,name)))))
     (let* (,@(fn2-columns-swap-saves name cols)
             ,@(fn2-columns-swap-writes name cols nil)
             ,@(fn2-columns-swap-writes name cols t)) ,name))
    (,preserves ,fn (left right ,name) :position nil :raw-rows t)
    (defthm ,(fn2-columns-sym fn "-REFINES-ROW-MODEL")
     (implies (and (,wfp ,name) (natp left) (natp right)
                   (< left (,rows ,name)) (< right (,rows ,name)))
      (equal (,fn left right ,name)
             (fn2-columns-row-swap-model ,(len cols) left right ,name)))
     :rule-classes nil
     :hints (("Goal" :in-theory (enable ,fn fn2-columns-row-swap-model fn2-columns-row-copy-model
                                      ,@(fn2-columns-accessor-names name cols))))))))
(defmacro defcolumn-row-swap (name)
 `(make-event
   (let ((cols (fn2-decl-get :columns (fn2-decl-row '(:columns ,name) (w state)))))
    (if (consp cols) (value (fn2-columns-row-swap-events ',name cols))
     (er soft 'defcolumn-row-swap "No actual column declaration for ~x0." ',name)))))
