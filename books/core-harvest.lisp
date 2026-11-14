; Completion extensions are declared with their owning core child. They run
; after a validated completion and pool settlement, before operation recycle.
; In particular they cannot mutate the operation table or issuance history.
(in-package "ACL2")
(include-book "core-children")

(defun fn2-core-harvest-bindingsp (bindings entries)
 (declare (xargs :verify-guards nil))
 (if (atom bindings) (null bindings)
  (and (true-listp (car bindings)) (equal (len (car bindings)) 2)
       (not (member-eq (caar bindings) '(fn2-core-ops fn2-core-control fn2-core-pool)))
       (equal (cadar bindings)
         (fn2-core-child-property (assoc-eq (caar bindings) entries) :stobj))
       (not (assoc-eq (caar bindings) (cdr bindings)))
       (fn2-core-harvest-bindingsp (cdr bindings) entries))))

(defconst *fn2-core-harvest-args*
 '(opslot opgen cell evkind outcome reason count aux0 aux1))

(defun fn2-core-harvest-hook-events (entries all)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((entry (car entries)) (hook (fn2-core-child-property entry :harvest))
         (callback (car hook)) (children (cadr hook))
         (name (fn2-columns-sym (car entry) "-HARVEST"))
         (args *fn2-core-harvest-args*) (stobjs (strip-cadrs children)))
   (append
    (and hook
     (if (and (true-listp hook) (equal (len hook) 2)
              (symbolp callback) callback (consp children)
              (fn2-core-harvest-bindingsp children all))
      `((fn2-defoperation (:operation-set fn2-core-harvest) :core :infer
          (defun ,name (,@args fn2-core)
           (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
           (stobj-let ,(fn2-core-child-bindings children)
            (code ,@stobjs)
            (,callback ,@args ,@stobjs)
            (mv code fn2-core))))
        (fn2-core-preserves ,name (,@args fn2-core) :position 1 :rows nil)
        (defthm ,(fn2-columns-sym name "-OPS-UNCHANGED")
         (equal (fn2-core-ops (mv-nth 1 (,name ,@args fn2-core)))
                (fn2-core-ops fn2-core))
         :hints (("Goal" :in-theory (enable ,name)))))
      (er hard 'fn2-core-harvest-hook-events "Invalid harvest extension on ~x0." (car entry))))
    (fn2-core-harvest-hook-events (cdr entries) all)))))

(defun fn2-core-harvest-calls (entries)
 (declare (xargs :verify-guards nil))
 (if (atom entries) '(mv :ok fn2-core)
  (if (fn2-core-child-property (car entries) :harvest)
   `(mv-let (code fn2-core)
      (,(fn2-columns-sym (caar entries) "-HARVEST")
         ,@*fn2-core-harvest-args* fn2-core)
      (if (eq code :ok) ,(fn2-core-harvest-calls (cdr entries))
        (mv code fn2-core)))
   (fn2-core-harvest-calls (cdr entries)))))

(defmacro fn2-core-harvest-events ()
 '(make-event
   (let ((entries (fn2-core-child-registry (w state))))
    (value
     `(progn
       ,@(fn2-core-harvest-hook-events entries entries)
       (fn2-defoperation (:operation-set fn2-core-harvest) :core :infer
        (defun fn2-core-harvest-hooks (,@*fn2-core-harvest-args* fn2-core)
         (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core))
                  (ignorable ,@*fn2-core-harvest-args*))
         ,(fn2-core-harvest-calls entries)))
       (fn2-core-preserves fn2-core-harvest-hooks
         (,@*fn2-core-harvest-args* fn2-core) :position 1 :rows nil)
       (defthm fn2-core-harvest-hooks-ops-unchanged
        (equal (fn2-core-ops (mv-nth 1
                 (fn2-core-harvest-hooks ,@*fn2-core-harvest-args* fn2-core)))
               (fn2-core-ops fn2-core))
        :hints (("Goal" :in-theory (enable fn2-core-harvest-hooks)))))))))
