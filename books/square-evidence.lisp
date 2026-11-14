; Formula-bound witnesses share the obligation store.  They establish one
; concrete instance and one sensitivity control, never a universal proof.
(in-package "ACL2")
(include-book "owed")

(defun fn2-evidence-bindingsp (bindings vars)
 (declare (xargs :verify-guards nil))
 (and (true-list-listp bindings)
      (equal (strip-cars bindings) vars)
      (if (atom bindings) t
       (and (equal (len (car bindings)) 2)
            (quotep (cadar bindings)) (equal (len (cadar bindings)) 2)
            (fn2-evidence-bindingsp (cdr bindings) (cdr vars))))))

(defun fn2-evidence-callp (call world)
 (declare (xargs :verify-guards nil))
 (and (consp call) (symbolp (car call))
      (getpropc (car call) 'unnormalized-body nil world)
      (equal (len (cdr call)) (len (getpropc (car call) 'formals nil world)))
      (pseudo-term-listp (cdr call))))
(defun fn2-evidence-call-guard (call world)
 (declare (xargs :verify-guards nil))
 (sublis-var (pairlis$ (getpropc (car call) 'formals nil world) (cdr call))
             (getpropc (car call) 'guard t world)))
(defun fn2-evidence-abi (fn world)
 (declare (xargs :verify-guards nil))
 (list (len (getpropc fn 'formals nil world))
       (getpropc fn 'stobjs-in nil world) (getpropc fn 'stobjs-out nil world)))
(defun fn2-evidence-function-binding (fn world)
 (declare (xargs :verify-guards nil))
 (list fn (getpropc fn 'unnormalized-body nil world)
       (getpropc fn 'guard t world) (fn2-evidence-abi fn world)))
(defun fn2-evidence-name (name suffix)
 (declare (xargs :verify-guards nil))
 (intern-in-package-of-symbol (concatenate 'string (symbol-name name) suffix) name))

; Initial scope: literal equality of two admitted function calls, optionally
; under an explicit IMPLIES.  Unsupported formulas are refused, not guessed.
(defun fn2-evidence-parts (formula)
 (declare (xargs :verify-guards nil))
 (if (and (consp formula) (eq (car formula) 'implies) (equal (len formula) 3))
     (mv (cadr formula) (caddr formula))
   (mv t formula)))
(defun fn2-evidence-hypotheses (hyp)
 (declare (xargs :verify-guards nil))
 (if (eq hyp t) nil
  (if (and (consp hyp) (eq (car hyp) 'and)) (cdr hyp) (list hyp))))

(defun fn2-square-evidence-events (name positive negative recheck world)
 (declare (xargs :verify-guards nil))
 (let* ((row (fn2-decl-row (list :square name) world))
        (vars (fn2-decl-get :vars row)) (formula (fn2-decl-get :formula row))
        (pos-name (fn2-evidence-name name "$BOUND-POSITIVE"))
        (neg-name (fn2-evidence-name name "$BOUND-NEGATIVE"))
        (mode (fn2-decl-get :kind negative))
        (at (fn2-decl-get :at negative))
        (mutant (fn2-decl-get :replace negative))
        (removed (fn2-decl-get :remove negative))
        (neg-bindings (fn2-decl-get :bindings negative)))
  (mv-let (hyp conclusion) (fn2-evidence-parts formula)
   (let* ((lhs (cadr conclusion)) (rhs (caddr conclusion))
          (hypotheses (fn2-evidence-hypotheses hyp))
          (mut-call (cons mutant (cdr lhs)))
          (domain `(and ,(fn2-evidence-call-guard lhs world)
                        ,(fn2-evidence-call-guard rhs world)))
          (pos-body `(let ,positive (and ,domain ,hyp ,conclusion)))
          (neg-body
           (if (eq mode :mutation)
               `(let ,neg-bindings
                  (and ,domain ,(fn2-evidence-call-guard mut-call world)
                       ,hyp ,conclusion (not (equal ,mut-call ,rhs))))
             `(let ,neg-bindings
                (and ,domain ,@(remove-equal removed hypotheses)
                     (not ,removed) (not ,conclusion)))))
          (problem
           (cond
            ((not (and row (fn2-decl-get :statement row))) :unknown-statement)
            ((and (not recheck) (fn2-decl-get :evidence row)) :already-bound)
            ((not (and (symbol-listp vars) (no-duplicatesp-eq vars)
                       (fn2-evidence-bindingsp positive vars)
                       (fn2-evidence-bindingsp neg-bindings vars))) :bindings)
            ((not (and (consp conclusion) (eq (car conclusion) 'equal)
                       (equal (len conclusion) 3)
                       (fn2-evidence-callp lhs world) (fn2-evidence-callp rhs world))) :formula-shape)
            ((not (and (eq (car lhs) (fn2-decl-get :concrete (fn2-decl-get :sides row)))
                       (eq (car rhs) (fn2-decl-get :reference (fn2-decl-get :sides row))))) :endpoint-binding)
            ((and (not recheck)
                  (or (getpropc pos-name 'theorem nil world)
                      (getpropc neg-name 'theorem nil world))) :name-collision)
            ((eq mode :mutation)
             (cond ((not (eq at (car lhs))) :wrong-mutation-endpoint)
                   ((or (eq mutant at) (not (fn2-evidence-callp mut-call world))) :mutant)
                   ((not (equal (fn2-evidence-abi at world) (fn2-evidence-abi mutant world))) :mutant-abi)))
            ((eq mode :hypothesis-removal)
             (if (and (member-equal removed hypotheses)
                      (equal (len (remove-equal removed hypotheses)) (1- (len hypotheses))))
                 nil :removed-hypothesis))
            (t :negative-kind))))
     (if problem
         `(make-event (er soft 'defsquare-evidence "Cannot bind ~x0: ~x1." ',name ',problem))
       (if recheck
           `(progn (thm ,pos-body) (thm ,neg-body))
        `(progn
          (defthm ,pos-name ,pos-body :rule-classes nil)
          (defthm ,neg-name ,neg-body :rule-classes nil)
          (make-event
           (value
            (list 'table 'fn2-squares (list 'quote ',name)
             (list 'quote
              (fn2-decl-set :evidence
               (fn2-decl-set :positive-theorem
                (getpropc ',pos-name 'theorem nil (w state))
                (fn2-decl-set :negative-theorem
                 (getpropc ',neg-name 'theorem nil (w state))
                 '(:kind :formula-ground-proofs :formula ,formula
                 :translated ,(fn2-decl-get :translated row)
                 :positive ,pos-name :negative ,neg-name
                 :positive-body ,pos-body :negative-body ,neg-body
                 :positive-bindings ,positive :negative-control ,negative
                 :functions (,(fn2-evidence-function-binding (car lhs) world)
                             ,(fn2-evidence-function-binding (car rhs) world)
                             ,@(and (eq mode :mutation)
                                    (list (fn2-evidence-function-binding mutant world)))))))
               (fn2-decl-row '(:square ,name) (w state))))))))))))))

(defmacro defsquare-evidence (name &key positive negative)
 `(make-event (value (fn2-square-evidence-events ',name ',positive ',negative nil (w state)))))

(defun fn2-evidence-functions-currentp (bindings world)
 (declare (xargs :verify-guards nil))
 (if (atom bindings) (null bindings)
  (and (equal (car bindings) (fn2-evidence-function-binding (caar bindings) world))
       (fn2-evidence-functions-currentp (cdr bindings) world))))
(defmacro fn2-assert-square-evidence (name)
 `(make-event
   (let* ((row (fn2-decl-row '(:square ,name) (w state)))
          (e (fn2-decl-get :evidence row))
          (negative (fn2-decl-get :negative-control e))
          (sides (fn2-decl-get :sides row))
          (pos-name (fn2-evidence-name ',name "$BOUND-POSITIVE"))
          (neg-name (fn2-evidence-name ',name "$BOUND-NEGATIVE")))
    (if (not (and (eq (fn2-decl-get :kind e) :formula-ground-proofs)
                  (equal (fn2-decl-get :formula e) (fn2-decl-get :formula row))
                  (equal (fn2-decl-get :translated e) (fn2-decl-get :translated row))
                  (equal (fn2-decl-get :positive e) pos-name)
                  (equal (fn2-decl-get :negative e) neg-name)
                  (getpropc pos-name 'theorem nil (w state))
                  (getpropc neg-name 'theorem nil (w state))
                  (equal (fn2-decl-get :positive-theorem e) (getpropc pos-name 'theorem nil (w state)))
                  (equal (fn2-decl-get :negative-theorem e) (getpropc neg-name 'theorem nil (w state)))
                  (equal (strip-cars (fn2-decl-get :functions e))
                         (append (list (fn2-decl-get :concrete sides) (fn2-decl-get :reference sides))
                                 (and (eq (fn2-decl-get :kind negative) :mutation)
                                      (list (fn2-decl-get :replace negative)))))
                  (fn2-evidence-functions-currentp (fn2-decl-get :functions e) (w state))))
        (er soft 'fn2-assert-square-evidence "Missing or stale formula evidence: ~x0." ',name)
     ; Re-derive and prove both complete assertions.  Stored names, bodies or
     ; a claimed PASS flag are never evidence by themselves.
     (value (fn2-square-evidence-events ',name (fn2-decl-get :positive-bindings e)
                                       (fn2-decl-get :negative-control e) t (w state)))))))
