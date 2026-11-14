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
; Mutable boundaries with spine refinements are retained for the product IR.
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
; Singleton recursion is admitted only with a scalar, source-owned measure.
; The generated child must independently prove termination with that measure.
(defun fn2-lower-scalar-measure (fn world)
 (declare (xargs :verify-guards nil))
 (let* ((justification (getpropc fn 'justification nil world))
        (measure (and justification (access justification justification :measure)))
        (formal (cadr measure)))
  (and (equal (getpropc fn 'recursivep nil world) (list fn))
       (equal measure (list 'nfix formal))
       (symbolp formal) formal
       (member-eq formal (getpropc fn 'formals nil world))
       (not (nth (position-eq formal (getpropc fn 'formals nil world))
                 (getpropc fn 'stobjs-in nil world)))
       measure)))
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
   ((and (assoc-eq (car term) (table-alist 'fn2-core-lowered world))
         (or readonlyp
             (fn2-decl-get :reverse (cdr (assoc-eq (car term) (table-alist 'fn2-core-lowered world)))))
         (not (fn2-arms-stobjs-of (getpropc (car term) 'stobjs-out nil world))))
    (mv-let (hit problem call) (fn2-lower-reader-leaf term world)
     (declare (ignore hit))
     (if problem (mv problem nil nil)
      (mv-let (problem args opened)
       (fn2-lower-expand-list (cdr call) fields world stack (1- fuel) readonlyp)
       (mv problem (cons (car call) args) opened)))))
   ((and (not readonlyp) (eq (car term) (car (last stack)))
         (fn2-lower-scalar-measure (car term) world))
    (mv-let (problem args opened)
     (fn2-lower-expand-list (cdr term) fields world stack (1- fuel) readonlyp)
     (mv problem (cons (car term) args) opened)))
   ((and (not readonlyp)
         (fn2-decl-get :shape-reverse
           (cdr (assoc-eq (car term) (table-alist 'fn2-core-lowered world))))
         (member-eq 'fn2-core (getpropc (car term) 'stobjs-out nil world)))
    (mv-let (problem args opened)
     (fn2-lower-expand-list (cdr term) fields world stack (1- fuel) readonlyp)
     (mv problem (cons (car term) args) opened)))
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

; Preserve lexical bindings and evaluation count while making unused aliases
; explicitly ignorable in executable syntax. Translated lambda terms have no
; declarations, including the aliases introduced for ignored MV components.
(mutual-recursion
 (defun fn2-lower-source-form (term)
  (declare (xargs :verify-guards nil))
  (cond ((atom term) term) ((eq (car term) 'quote) term)
        ((consp (car term))
         `(let ,(pairlis$ (cadar term) (pairlis$ (fn2-lower-source-forms (cdr term)) nil))
            (declare (ignorable ,@(cadar term)))
            ,(fn2-lower-source-form (caddar term))))
        (t (cons (car term) (fn2-lower-source-forms (cdr term))))))
 (defun fn2-lower-source-forms (terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
   (cons (fn2-lower-source-form (car terms)) (fn2-lower-source-forms (cdr terms))))))

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

; Result arity is proved, not inferred as a logical fact from ABI metadata.
(defun fn2-lower-shape-parts (call left index)
 (declare (xargs :verify-guards nil :measure (nfix left)))
 (if (zp left) nil
  (cons (if (zp index) (list 'car call) (list 'nth index call))
        (fn2-lower-shape-parts call (1- left) (1+ index)))))
(defun fn2-lower-instance-bindings (vars terms)
 (declare (xargs :verify-guards nil))
 (if (atom vars) nil
  (cons (list (car vars) (car terms))
        (fn2-lower-instance-bindings (cdr vars) (cdr terms)))))
(defun fn2-lower-shape-events (fn child formals args entries count)
 (declare (xargs :verify-guards nil))
 (if (< count 2) nil
  (let* ((child-call (cons child args)) (source-call (cons fn formals))
         (child-shape (fn2-columns-sym child "-RESULT-SHAPE"))
         (source-shape (fn2-columns-sym child "-CORE-RESULT-SHAPE"))
         (refinement (fn2-columns-sym child "-REFINES-CORE")))
   `((defthm ,child-shape
       (equal (list ,@(fn2-lower-shape-parts child-call count 0)) ,child-call)
       :hints (("Goal" :in-theory (enable ,child))))
     (defthm ,source-shape
       (equal (list ,@(fn2-lower-shape-parts source-call count 0)) ,source-call)
       :hints (("Goal"
                :use ((:instance ,refinement)
                      (:instance ,child-shape
                        ,@(fn2-lower-instance-bindings args (fn2-lower-core-args args entries))))
                :in-theory (disable ,fn ,child ,refinement ,child-shape))))))))

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
   (append (list (fn2-decl-get :obligation row))
           (and (fn2-decl-get :execution-obligation row)
                (list (fn2-decl-get :execution-obligation row)))
           (fn2-lower-obligations (cdr functions) world)))))
(defmacro fn2-check-lowering-teeth (&rest functions)
 `(make-event (value (cons 'fn2-assert-owed-teeth (fn2-lower-obligations ',functions (w state))))))

; Guard predicates carry the facts needed by primitive column accesses.
; Open only the generated reader closure reachable from the guard, leaving
; ordinary data-producing body calls behind their verified contracts.
(defun fn2-lower-registered-children (rows)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (cons (fn2-decl-get :child (cdar rows))
        (fn2-lower-registered-children (cdr rows)))))
; Emitted mv-list forms contain a literal arity, so they are source forms,
; not translated pseudo-terms accepted by ACL2's all-fnnames.
(mutual-recursion
 (defun fn2-lower-call-names (term)
  (declare (xargs :verify-guards nil))
  (cond ((atom term) nil)
        ((eq (car term) 'quote) nil)
        ((consp (car term))
         (union-eq (fn2-lower-call-names (caddar term))
                   (fn2-lower-call-names-list (cdr term))))
        (t (cons (car term) (fn2-lower-call-names-list (cdr term))))))
 (defun fn2-lower-call-names-list (terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
   (union-eq (fn2-lower-call-names (car terms))
             (fn2-lower-call-names-list (cdr terms))))))
; Slice branch predicates through lambda bindings. The environment maps
; variables to dependency names, never runtime values; data calls outside
; the predicate slice stay opaque during guard verification.
(mutual-recursion
 (defun fn2-lower-predicate-names (term env tests-only fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((zp fuel) nil)
        ((atom term) (and (not tests-only) (cdr (assoc-eq term env))))
        ((eq (car term) 'quote) nil)
        ((consp (car term))
         (union-eq
          (fn2-lower-predicate-names
           (caddar term)
           (append (fn2-lower-name-bindings (cadar term) (cdr term) env (1- fuel)) env)
           tests-only (1- fuel))
          (and tests-only (fn2-lower-predicate-names-list (cdr term) env t (1- fuel)))))
        ((and tests-only (eq (car term) 'if))
         (union-eq (fn2-lower-predicate-names (cadr term) env nil (1- fuel))
                   (fn2-lower-predicate-names-list (cdr term) env t (1- fuel))))
        (t (union-eq (and (not tests-only) (list (car term)))
                      (fn2-lower-predicate-names-list (cdr term) env tests-only (1- fuel))))))
 (defun fn2-lower-predicate-names-list (terms env tests-only fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (atom terms)) nil
   (union-eq (fn2-lower-predicate-names (car terms) env tests-only (1- fuel))
             (fn2-lower-predicate-names-list (cdr terms) env tests-only (1- fuel)))))
 (defun fn2-lower-name-bindings (formals args env fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (atom formals)) nil
   (cons (cons (car formals) (fn2-lower-predicate-names (car args) env nil (1- fuel)))
         (fn2-lower-name-bindings (cdr formals) (cdr args) env (1- fuel))))))
(defun fn2-lower-call-guard-names (fns world)
 (declare (xargs :verify-guards nil))
 (if (atom fns) nil
  (union-eq (all-fnnames (getpropc (car fns) 'guard nil world))
            (fn2-lower-call-guard-names (cdr fns) world))))
(defun fn2-lower-guard-openings (pending children seen world fuel)
 (declare (xargs :verify-guards nil :measure (nfix fuel)))
 (cond ((or (atom pending) (zp fuel)) seen)
       ((or (not (member-eq (car pending) children)) (member-eq (car pending) seen))
        (fn2-lower-guard-openings (cdr pending) children seen world (1- fuel)))
       (t (fn2-lower-guard-openings
           (append (all-fnnames (getpropc (car pending) 'unnormalized-body nil world))
                   (cdr pending))
           children (cons (car pending) seen) world (1- fuel)))))

; A multiple-result producer is a data boundary, even when one component
; feeds a branch test. Keep that producer opaque while opening scalar
; predicates on its outputs; expanding it would duplicate every data case.
(defun fn2-lower-predicate-children (rows world)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (let ((child (fn2-decl-get :child (cdar rows))))
   (append (and (equal (getpropc child 'stobjs-out nil world) '(nil)) (list child))
           (fn2-lower-predicate-children (cdr rows) world)))))
(defun fn2-lower-guard-theory (guard body world)
 (declare (xargs :verify-guards nil))
 (fn2-lower-guard-openings
  (union-eq (fn2-lower-call-names guard)
   (union-eq (fn2-lower-predicate-names body nil t 10000)
             (fn2-lower-call-guard-names (fn2-lower-call-names body) world)))
  (fn2-lower-predicate-children (table-alist 'fn2-core-lowered world) world)
  nil world 10000))
(defun fn2-lower-leaf-properties (rows calls property)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (let ((row (cdar rows)))
   (append (and (fn2-decl-get :reverse row)
                (member-eq (fn2-decl-get :child row) calls)
                (list (if (eq property :source) (caar rows) (fn2-decl-get property row))))
           (fn2-lower-leaf-properties (cdr rows) calls property)))))
(defun fn2-lower-readonly-events (fn child teeth world)
  (declare (xargs :verify-guards nil))
  (mv-let (expansion-problem body opened)
    (fn2-lower-expand (getpropc fn 'unnormalized-body nil world)
                      (strip-cars (fn2-core-child-registry world)) world (list fn) 10000 t)
  (mv-let (guard-problem expanded-guard guard-opened)
   (fn2-lower-expand (getpropc fn 'guard t world)
                    (strip-cars (fn2-core-child-registry world)) world (list fn) 10000 t)
   (declare (ignore guard-opened))
  (let* ((body body)
         (ins (getpropc fn 'stobjs-in nil world))
         (outs (getpropc fn 'stobjs-out nil world))
         (formals (getpropc fn 'formals nil world))
         (entries (and (pseudo-termp body)
                       (fn2-lower-used-entries (fn2-core-child-registry world)
                         (list 'if expanded-guard body ''nil))))
         (children (fn2-core-child-types entries))
         (replacement (fn2-lower-projections entries))
         (lowered (fn2-lower-substitute body replacement world))
         (guard (fn2-lower-substitute
                 expanded-guard
                 (acons '(fn2-core-wfp fn2-core) (cons 'and (fn2-lower-predicates children "-WFP"))
                        (acons '(fn2-corep fn2-core) (cons 'and (fn2-lower-predicates children "P")) replacement)) world))
         (args (append (remove-eq 'fn2-core formals) children))
         (problem
          (cond ((fn2-lower-teeth-problem teeth) :evidence-pair)
                (expansion-problem expansion-problem)
                (guard-problem guard-problem)
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
           (declare (ignorable ,@args)
                    (xargs :stobjs ,children :guard ,guard :verify-guards t
                     :guard-hints (("Goal" :in-theory
                        (enable ,@(fn2-lower-guard-theory guard lowered world))))))
           ,(fn2-lower-result-body (fn2-lower-source-form lowered) (len outs)))
         (assert-event
          (and (equal (getpropc ',child 'stobjs-out nil (w state)) ',outs)
               (equal (getpropc ',child 'stobjs-in nil (w state))
                      ',(append (remove-eq 'fn2-core ins) children))))
         (defthm ,(fn2-columns-sym child "-REFINES-CORE")
           (equal (,child ,@(fn2-lower-core-args args entries)) (,fn ,@formals))
           :hints (("Goal" :in-theory (e/d (,fn ,child ,@opened) (,@(strip-cars entries))))))
         (defthm ,(fn2-columns-sym child "-CORE-TO-CHILD")
           (equal (,fn ,@formals) (,child ,@(fn2-lower-core-args args entries)))
           :hints (("Goal" :use ((:instance ,(fn2-columns-sym child "-REFINES-CORE")))
                    :in-theory (disable ,fn ,child))))
         (in-theory (disable ,(fn2-columns-sym child "-CORE-TO-CHILD")))
         ,@(fn2-lower-shape-events fn child formals args entries (len outs))
         ,@(fn2-lower-obligation-events fn child child formals
             `(equal (,child ,@(fn2-lower-core-args args entries)) (,fn ,@formals))
             (fn2-columns-sym child "-REFINES-CORE") teeth)
         (in-theory (disable ,child))
         (table fn2-core-lowered ',fn
                '(:child ,child :refinement ,(fn2-columns-sym child "-REFINES-CORE")
                  :reverse ,(fn2-columns-sym child "-CORE-TO-CHILD")
                  :children ,children :obligation ,(fn2-columns-sym child "-REFINES-CORE")))))))))
(defmacro defcore-readonly-child (fn child &key teeth)
  `(make-event (value (fn2-lower-readonly-events ',fn ',child ',teeth (w state)))))

; Plan the nonrecursive dependency DAG before emitting any events. NIL is
; reader-only, T traverses writers for reader leaves, :ALL also emits writers.
; A refusal leaves no partially generated family in the world.
(mutual-recursion
 (defun fn2-lower-reader-plan (fn fields world seen stack fuel through-writes)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond
   ((zp fuel) (mv :expansion-budget nil seen))
   ((or (member-eq fn fields)
        (not (member-eq 'fn2-core (getpropc fn 'stobjs-in nil world)))
        (member-eq fn seen)
        (and (not (fn2-arms-stobjs-of (getpropc fn 'stobjs-out nil world)))
             (assoc-eq fn (table-alist 'fn2-core-lowered world)))
        (and (eq through-writes :all)
             (fn2-decl-get :shape-reverse
               (cdr (assoc-eq fn (table-alist 'fn2-core-lowered world))))))
    (mv nil nil seen))
   ((or (member-eq fn stack) (getpropc fn 'recursivep nil world))
    (mv :recursive-callee nil seen))
   ((member-eq fn '(fn2-corep fn2-core-wfp)) (mv :unlowered-core nil seen))
   ((and (not through-writes) (fn2-arms-stobjs-of (getpropc fn 'stobjs-out nil world)))
    (mv :callee-writes-state nil seen))
   (t
    (let ((body (getpropc fn 'unnormalized-body nil world)))
     (if (or (null body) (not (pseudo-termp body)))
         (mv :missing-body nil seen)
      (mv-let (problem order seen)
       (fn2-lower-reader-plan-list
        (union-eq (all-fnnames body)
          (set-difference-eq (all-fnnames (getpropc fn 'guard t world))
                            '(fn2-corep fn2-core-wfp))) fields world seen
                                   (cons fn stack) (1- fuel) through-writes)
       (mv problem (append order
                      (and (or (eq through-writes :all)
                               (not (fn2-arms-stobjs-of (getpropc fn 'stobjs-out nil world)))) (list fn)))
           (cons fn seen))))))))
 (defun fn2-lower-reader-plan-list (fns fields world seen stack fuel through-writes)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond ((atom fns) (mv nil nil seen))
        ((zp fuel) (mv :expansion-budget nil seen))
        (t
         (mv-let (problem first seen)
          (fn2-lower-reader-plan (car fns) fields world seen stack (1- fuel) through-writes)
          (if problem (mv problem nil seen)
           (mv-let (problem rest seen)
            (fn2-lower-reader-plan-list (cdr fns) fields world seen stack (1- fuel) through-writes)
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
                           (w state) nil nil 10000 nil)
    (declare (ignore seen))
    (if (or problem (not (member-eq ',fn order)))
        (er soft 'defcore-readonly-closure "Cannot plan ~x0: ~x1." ',fn
            (or problem :already-lowered-or-not-core))
      (value (cons 'progn (fn2-lower-reader-family-events order ',fn ',child ',teeth)))))))
