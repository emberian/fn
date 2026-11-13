; Derive child faces from admitted core definitions. This first lowering rule
; handles read-only projections; unsupported core uses fail closed. No new
; operation registration precedes guard verification and full-result equality.
(in-package "ACL2")
(include-book "machine-arms")

(defun fn2-lower-projections (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (cons (list (caar entries) 'fn2-core)
                (fn2-core-child-property (car entries) :stobj))
          (fn2-lower-projections (cdr entries)))))

(mutual-recursion
 (defun fn2-lower-substitute (term replacements)
   (declare (xargs :verify-guards nil))
   (let ((hit (assoc-equal term replacements)))
     (cond (hit (cdr hit))
           ((atom term) term)
           ((eq (car term) 'quote) term)
           ((consp (car term))
            (cons (list 'lambda (cadar term)
                        (fn2-lower-substitute (caddar term) replacements))
                  (fn2-lower-substitute-list (cdr term) replacements)))
           (t (cons (car term) (fn2-lower-substitute-list (cdr term) replacements))))))
 (defun fn2-lower-substitute-list (terms replacements)
   (declare (xargs :verify-guards nil))
   (if (atom terms) nil
     (cons (fn2-lower-substitute (car terms) replacements)
           (fn2-lower-substitute-list (cdr terms) replacements)))))

(defun fn2-lower-used-entries (entries body)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (append (and (member-eq (caar entries) (all-fnnames body)) (list (car entries)))
            (fn2-lower-used-entries (cdr entries) body))))
(defun fn2-lower-predicates (children suffix)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (cons (list (fn2-columns-sym (car children) suffix) (car children))
          (fn2-lower-predicates (cdr children) suffix))))
(defun fn2-lower-core-args (args entries)
  (declare (xargs :verify-guards nil))
  (if (atom args) nil
    (cons (let ((entry (assoc-eq (car args)
                               (pairlis$ (fn2-core-child-types entries) (strip-cars entries)))))
            (if entry (list (cdr entry) 'fn2-core) (car args)))
          (fn2-lower-core-args (cdr args) entries))))

(defun fn2-lower-readonly-events (fn child world)
  (declare (xargs :verify-guards nil))
  (let* ((body (getpropc fn 'unnormalized-body nil world))
         (ins (getpropc fn 'stobjs-in nil world))
         (outs (getpropc fn 'stobjs-out nil world))
         (formals (getpropc fn 'formals nil world))
         (entries (and (pseudo-termp body)
                       (fn2-lower-used-entries (fn2-core-child-registry world) body)))
         (children (fn2-core-child-types entries))
         (replacement (fn2-lower-projections entries))
         (lowered (fn2-lower-substitute body replacement))
         (guard (fn2-lower-substitute
                 (getpropc fn 'guard t world)
                 (acons '(fn2-core-wfp fn2-core) (cons 'and (fn2-lower-predicates children "-WFP"))
                        (acons '(fn2-corep fn2-core) (cons 'and (fn2-lower-predicates children "P")) replacement))))
         (args (append (remove-eq 'fn2-core formals) children))
         (problem
          (cond ((not (pseudo-termp body)) :missing-body)
                ((not (equal (remove-eq nil ins) '(fn2-core))) :input-shape)
                ((fn2-arms-stobjs-of outs) :writes-state)
                ((getpropc fn 'recursivep nil world) :recursive)
                ((or (member-eq 'fn2-core (all-vars lowered))
                     (member-eq 'fn2-core (all-vars guard))) :unlowered-core)
                ((intersectp-eq children (remove-eq 'fn2-core formals)) :formal-collision)
                ((function-symbolp child world) :child-already-defined)
                (t nil))))
    (if problem
        `(make-event (er soft 'defcore-readonly-child "Cannot lower ~x0: ~x1." ',fn ',problem))
      `(progn
         (defun ,child ,args
           (declare (xargs :stobjs ,children :guard ,guard))
           ,lowered)
         (defthm ,(fn2-columns-sym child "-REFINES-CORE")
           (equal (,child ,@(fn2-lower-core-args args entries)) (,fn ,@formals))
           :hints (("Goal" :in-theory (enable ,fn ,child))))
         (in-theory (disable ,child))
         (table fn2-core-lowered ',fn
                '(:child ,child :refinement ,(fn2-columns-sym child "-REFINES-CORE")
                  :children ,children))))))
(defmacro defcore-readonly-child (fn child)
  `(make-event (value (fn2-lower-readonly-events ',fn ',child (w state)))))
