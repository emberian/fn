; Derive child faces from admitted core definitions. This first lowering rule
; handles read-only projections; unsupported core uses fail closed. No new
; operation registration precedes guard verification and full-result equality.
(in-package "ACL2")
(include-book "machine-arms")
(include-book "owed")

(defun fn2-lower-projections (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (cons (cons (list (caar entries) 'fn2-core)
                (fn2-core-child-property (car entries) :stobj))
          (fn2-lower-projections (cdr entries)))))

; This walk also accepts emitted source macros (mv-list and and), before
; ACL2 translation; all-vars requires an already translated pseudo-term.
(mutual-recursion
 (defun fn2-lower-vars (term)
  (declare (xargs :verify-guards nil))
  (cond ((atom term) (and (symbolp term) term (not (eq term t)) (not (keywordp term)) (list term)))
        ((eq (car term) 'quote) nil)
        ((consp (car term))
         (union-eq (set-difference-eq (fn2-lower-vars (caddar term)) (cadar term))
                   (fn2-lower-vars-list (cdr term))))
        (t (fn2-lower-vars-list (cdr term)))))
 (defun fn2-lower-vars-list (terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
    (union-eq (fn2-lower-vars (car terms)) (fn2-lower-vars-list (cdr terms))))))

(mutual-recursion
 (defun fn2-lower-substitute (term replacements world)
   (declare (xargs :verify-guards nil))
   (let ((hit (assoc-equal term replacements)))
     (cond (hit (cdr hit))
           ((atom term) term)
           ((eq (car term) 'quote) term)
           ((consp (car term))
            (let* ((body (fn2-lower-substitute (caddar term) replacements world))
                   (free (set-difference-eq (fn2-lower-vars body) (cadar term))))
              (cons (list 'lambda (append (cadar term) free) body)
                    (append (fn2-lower-substitute-list (cdr term) replacements world) free))))
           (t (let* ((call (cons (car term) (fn2-lower-substitute-list (cdr term) replacements world)))
                     (outputs (getpropc (car term) 'stobjs-out nil world)))
                (if (< 1 (len outputs)) (list 'mv-list (len outputs) call) call))))))
 (defun fn2-lower-substitute-list (terms replacements world)
   (declare (xargs :verify-guards nil))
   (if (atom terms) nil
     (cons (fn2-lower-substitute (car terms) replacements world)
           (fn2-lower-substitute-list (cdr terms) replacements world)))))

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

; Keep ordinary lambda bindings: substituting their values can duplicate a
; bounded scan at each mv-nth use. Reader mode erases the core carrier;
; product mode retains it for the typed state-lowering pass.
(defun fn2-lower-without-core-args (formals args)
  (declare (xargs :verify-guards nil))
  (if (atom formals) nil
    (append (and (not (eq (car formals) 'fn2-core)) (list (car args)))
            (fn2-lower-without-core-args (cdr formals) (cdr args)))))
; A certified reader boundary is a modular leaf. Keep its verified guard
; and refinement instead of duplicating the transitive machine dispatch tree.
; Product lowering still expands state-returning boundaries through its IR.
(defun fn2-lower-reader-leaf (term world)
 (declare (xargs :verify-guards nil))
 (let* ((fn (car term))
        (row (cdr (assoc-eq fn (table-alist 'fn2-core-lowered world)))))
  (if (or (null row) (fn2-arms-stobjs-of (getpropc fn 'stobjs-out nil world)))
      (mv nil nil nil)
   (let* ((child (fn2-decl-get :child row))
          (children (fn2-decl-get :children row))
          (ins (getpropc fn 'stobjs-in nil world))
          (formals (getpropc fn 'formals nil world))
          (bindings (fn2-arms-core-stobj-lets children world)))
    (if (not (and (function-symbolp child world)
                  (equal (nth (position-eq 'fn2-core formals) (cdr term)) 'fn2-core)
                  (equal (getpropc child 'stobjs-in nil world)
                         (append (remove-eq 'fn2-core ins) children))
                  (equal (getpropc child 'stobjs-out nil world)
                         (getpropc fn 'stobjs-out nil world))
                  (equal (len bindings) (len children))))
        (mv t :reader-leaf-shape nil)
      (mv t nil (cons child
                  (append (fn2-lower-without-core-args formals (cdr term))
                          (strip-cadrs bindings)))))))))
(mutual-recursion
 (defun fn2-lower-expand (term fields world stack fuel readonlyp)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond
   ((zp fuel) (mv :expansion-budget nil nil))
   ((or (atom term) (eq (car term) 'quote)) (mv nil term nil))
   ((consp (car term))
    (let* ((formals (cadar term)) (body (caddar term))
           (corepos (position-eq 'fn2-core formals))
           (erase (and readonlyp corepos (eq (nth corepos (cdr term)) 'fn2-core))))
      (mv-let (problem body opened) (fn2-lower-expand body fields world stack (1- fuel) readonlyp)
        (mv-let (problem2 args opened2)
          (fn2-lower-expand-list (if erase (fn2-lower-without-core-args formals (cdr term)) (cdr term))
                                fields world stack (1- fuel) readonlyp)
          (mv (or problem problem2)
              (cons (list 'lambda (if erase (remove-eq 'fn2-core formals) formals) body) args)
              (union-eq opened opened2))))))
   ((and readonlyp (assoc-eq (car term) (table-alist 'fn2-core-lowered world))
         (not (fn2-arms-stobjs-of (getpropc (car term) 'stobjs-out nil world))))
    (mv-let (hit problem call) (fn2-lower-reader-leaf term world)
     (declare (ignore hit))
     (if problem (mv problem nil nil)
      (mv-let (problem args opened)
       (fn2-lower-expand-list (cdr call) fields world stack (1- fuel) readonlyp)
       (mv problem (cons (car call) args) opened)))))
   ((and (not (member-eq (car term) fields))
         (not (member-eq (car term) '(fn2-corep fn2-core-wfp)))
         (member-eq 'fn2-core (getpropc (car term) 'stobjs-in nil world)))
    (let* ((fn (car term)) (formals (getpropc fn 'formals nil world))
           (body (getpropc fn 'unnormalized-body nil world))
           (problem (cond ((and readonlyp (fn2-arms-stobjs-of (getpropc fn 'stobjs-out nil world))) :callee-writes-state)
                          ((member-eq fn stack) :recursive-callee)
                          ((or (null body) (not (pseudo-termp body))) :constrained-callee)
                          (t nil))))
      (if problem (mv problem nil nil)
        (mv-let (problem expanded opened)
          (fn2-lower-expand (cons (list 'lambda formals body) (cdr term)) fields world (cons fn stack) (1- fuel) readonlyp)
          (mv problem expanded (cons fn opened))))))
   (t (mv-let (problem args opened)
        (fn2-lower-expand-list (cdr term) fields world stack (1- fuel) readonlyp)
        (mv problem (cons (car term) args) opened)))))
 (defun fn2-lower-expand-list (terms fields world stack fuel readonlyp)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((atom terms) (mv nil nil nil))
        ((zp fuel) (mv :expansion-budget nil nil))
        (t (mv-let (problem term opened) (fn2-lower-expand (car terms) fields world stack (1- fuel) readonlyp)
             (mv-let (problem2 rest opened2) (fn2-lower-expand-list (cdr terms) fields world stack (1- fuel) readonlyp)
               (mv (or problem problem2) (cons term rest) (union-eq opened opened2))))))))

; Logical translated bodies represent multiple values as a fixed-arity list.
; Materialize that small result tuple once, never repeat the producer per
; component; restore the executable multiple-value ABI at the boundary.
(defun fn2-lower-result-parts (left index)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (cons (list 'nth index 'fn2-lower-result)
          (fn2-lower-result-parts (1- left) (1+ index)))))
(defun fn2-lower-result-body (body count)
  (declare (xargs :verify-guards nil))
  (if (< 1 count)
      `(let ((fn2-lower-result ,body)) (mv ,@(fn2-lower-result-parts count 0)))
    body))

; Refinement is compiler evidence, not an independent behavioural contract.
; Keep its proof and evaluating teeth in the promoted obligation store.
(defun fn2-lower-teeth-problem (teeth)
 (declare (xargs :verify-guards nil))
 (and teeth (not (and (true-listp teeth) (equal (len teeth) 2)
                     (no-duplicatesp-eq teeth) (fn2-owed-teethp teeth)))))
(defun fn2-lower-obligation-events (fn child concrete vars formula theorem teeth)
 (declare (xargs :verify-guards nil) (ignore child))
 (let ((teeth (or teeth (list (fn2-columns-sym theorem "-POSITIVE")
                             (fn2-columns-sym theorem "-NEGATIVE")))))
  `((defthm-owed ,theorem ,vars ,formula
      :schema :g1 :claim :compiler :shared ((:function ,fn))
      :sides (:concrete ,concrete :reference ,fn)
      :boundary :core-child-extraction :teeth ,teeth
      :doc "The generated child boundary preserves the original operation's complete result and effects.")
    (make-event
      (value (list 'table 'fn2-squares (list 'quote ',theorem)
                   (list 'quote (fn2-decl-set :proof '(:proved ,theorem)
                                  (fn2-decl-row '(:square ,theorem) (w state))))))))))
(defun fn2-lower-obligations (functions world)
 (declare (xargs :verify-guards nil))
 (if (atom functions) nil
  (let ((row (cdr (assoc-eq (car functions) (table-alist 'fn2-core-lowered world)))))
   (cons (fn2-decl-get :obligation row) (fn2-lower-obligations (cdr functions) world)))))
(defmacro fn2-check-lowering-teeth (&rest functions)
 `(make-event (value (cons 'fn2-assert-owed-teeth (fn2-lower-obligations ',functions (w state))))))

(defun fn2-lower-readonly-events (fn child teeth world)
  (declare (xargs :verify-guards nil))
  (mv-let (expansion-problem body opened)
    (fn2-lower-expand (getpropc fn 'unnormalized-body nil world)
                      (strip-cars (fn2-core-child-registry world)) world (list fn) 10000 t)
  (let* ((body body)
         (ins (getpropc fn 'stobjs-in nil world))
         (outs (getpropc fn 'stobjs-out nil world))
         (formals (getpropc fn 'formals nil world))
         (entries (and (pseudo-termp body)
                       (fn2-lower-used-entries (fn2-core-child-registry world) body)))
         (children (fn2-core-child-types entries))
         (replacement (fn2-lower-projections entries))
         (lowered (fn2-lower-substitute body replacement world))
         (guard (fn2-lower-substitute
                 (getpropc fn 'guard t world)
                 (acons '(fn2-core-wfp fn2-core) (cons 'and (fn2-lower-predicates children "-WFP"))
                        (acons '(fn2-corep fn2-core) (cons 'and (fn2-lower-predicates children "P")) replacement)) world))
         (args (append (remove-eq 'fn2-core formals) children))
         (problem
          (cond ((fn2-lower-teeth-problem teeth) :evidence-pair)
                (expansion-problem expansion-problem)
                ((or (null body) (not (pseudo-termp body))) :missing-body)
                ((not (and (equal (remove-eq nil ins) '(fn2-core))
                           (member-eq 'fn2-core formals)
                           (equal (position-eq 'fn2-core formals) (position-eq 'fn2-core ins)))) :input-shape)
                ((fn2-arms-stobjs-of outs) :writes-state)
                ((getpropc fn 'recursivep nil world) :recursive)
                ((or (member-eq 'fn2-core (fn2-lower-vars lowered))
                     (member-eq 'fn2-core (fn2-lower-vars guard))) :unlowered-core)
                ((intersectp-eq children (remove-eq 'fn2-core formals)) :formal-collision)
                ((function-symbolp child world) :child-already-defined)
                (t nil))))
    (if problem
        `(make-event (er soft 'defcore-readonly-child "Cannot lower ~x0: ~x1." ',fn ',problem))
      `(progn
         (defun ,child ,args
           (declare (xargs :stobjs ,children :guard ,guard :verify-guards t))
           ,(fn2-lower-result-body lowered (len outs)))
         (assert-event
          (and (equal (getpropc ',child 'stobjs-out nil (w state)) ',outs)
               (equal (getpropc ',child 'stobjs-in nil (w state))
                      ',(append (remove-eq 'fn2-core ins) children))))
         (defthm ,(fn2-columns-sym child "-REFINES-CORE")
           (equal (,child ,@(fn2-lower-core-args args entries)) (,fn ,@formals))
           :hints (("Goal" :in-theory (e/d (,fn ,child ,@opened) (,@(strip-cars entries))))))
         ,@(fn2-lower-obligation-events fn child child formals
             `(equal (,child ,@(fn2-lower-core-args args entries)) (,fn ,@formals))
             (fn2-columns-sym child "-REFINES-CORE") teeth)
         (in-theory (disable ,child))
         (table fn2-core-lowered ',fn
                '(:child ,child :refinement ,(fn2-columns-sym child "-REFINES-CORE")
                  :children ,children :obligation ,(fn2-columns-sym child "-REFINES-CORE"))))))))
(defmacro defcore-readonly-child (fn child &key teeth)
  `(make-event (value (fn2-lower-readonly-events ',fn ',child ',teeth (w state)))))

; Plan the nonrecursive reader dependency DAG before emitting any events.
; A refusal leaves no partially generated family in the world.
(mutual-recursion
 (defun fn2-lower-reader-plan (fn fields world seen stack fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond
   ((zp fuel) (mv :expansion-budget nil seen))
   ((or (member-eq fn fields)
        (not (member-eq 'fn2-core (getpropc fn 'stobjs-in nil world)))
        (member-eq fn seen)
        (assoc-eq fn (table-alist 'fn2-core-lowered world)))
    (mv nil nil seen))
   ((or (member-eq fn stack) (getpropc fn 'recursivep nil world))
    (mv :recursive-callee nil seen))
   ((member-eq fn '(fn2-corep fn2-core-wfp)) (mv :unlowered-core nil seen))
   ((fn2-arms-stobjs-of (getpropc fn 'stobjs-out nil world))
    (mv :callee-writes-state nil seen))
   (t
    (let ((body (getpropc fn 'unnormalized-body nil world)))
     (if (or (null body) (not (pseudo-termp body)))
         (mv :missing-body nil seen)
      (mv-let (problem order seen)
       (fn2-lower-reader-plan-list (all-fnnames body) fields world seen
                                   (cons fn stack) (1- fuel))
       (mv problem (append order (list fn)) (cons fn seen))))))))
 (defun fn2-lower-reader-plan-list (fns fields world seen stack fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((atom fns) (mv nil nil seen))
        ((zp fuel) (mv :expansion-budget nil seen))
        (t
         (mv-let (problem first seen)
          (fn2-lower-reader-plan (car fns) fields world seen stack (1- fuel))
          (if problem (mv problem nil seen)
           (mv-let (problem rest seen)
            (fn2-lower-reader-plan-list (cdr fns) fields world seen stack (1- fuel))
            (mv problem (append first rest) seen))))))))
(defun fn2-lower-reader-family-events (order root child teeth)
 (declare (xargs :verify-guards nil))
 (if (atom order) nil
  (cons `(defcore-readonly-child ,(car order)
           ,(if (eq (car order) root) child
              (fn2-columns-sym (car order) "-LOWERED-CHILD"))
           ,@(and (eq (car order) root) teeth `(:teeth ,teeth)))
        (fn2-lower-reader-family-events (cdr order) root child teeth))))
(defmacro defcore-readonly-closure (fn child &key teeth)
 `(make-event
   (mv-let (problem order seen)
    (fn2-lower-reader-plan ',fn (strip-cars (fn2-core-child-registry (w state)))
                           (w state) nil nil 10000)
    (declare (ignore seen))
    (if (or problem (not (member-eq ',fn order)))
        (er soft 'defcore-readonly-closure "Cannot plan ~x0: ~x1." ',fn
            (or problem :already-lowered-or-not-core))
      (value (cons 'progn (fn2-lower-reader-family-events order ',fn ',child ',teeth)))))))
