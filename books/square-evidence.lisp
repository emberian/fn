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

; Read only the live translated statement, never the author/display :formula.
; ACL2 retains the IMPLIES function and translates AND to IF(H,REST,'NIL).
; Explicit IF(H,C,'T) is also supported. These structural decompositions
; preserve the actual whole antecedent without logical rewriting.
(defun fn2-evidence-parts (formula)
 (declare (xargs :verify-guards nil))
 (cond ((and (consp formula) (eq (car formula) 'implies) (equal (len formula) 3))
        (mv (cadr formula) (caddr formula)))
       ((and (consp formula) (eq (car formula) 'if) (equal (len formula) 4)
             (equal (cadddr formula) ''t))
        (mv (cadr formula) (caddr formula)))
       (t (mv ''t formula))))
(defun fn2-evidence-hypotheses (hyp)
 (declare (xargs :verify-guards nil))
 (if (equal hyp ''t) nil
  (if (and (consp hyp) (eq (car hyp) 'if) (equal (len hyp) 4)
           (equal (cadddr hyp) ''nil))
      (cons (cadr hyp) (fn2-evidence-hypotheses (caddr hyp)))
    (list hyp))))

; A normalizer is an admitted equation about the EXACT original conclusion.
; Its right side supplies the endpoint calls: callers supply only its name.
; Conditional equations retain their domain, which must follow from the
; original H universally and hold at BOTH ground witnesses (including removal).
(defun fn2-evidence-normalization (conclusion correspondence world)
 (declare (xargs :verify-guards nil))
 (let ((theorem (and (symbolp correspondence)
                     (getpropc correspondence 'theorem nil world))))
  (if (not correspondence) (mv nil ''t conclusion nil)
   (mv-let (domain equation) (fn2-evidence-parts theorem)
    (if (and theorem (consp equation) (eq (car equation) 'equal)
             (equal (len equation) 3) (equal (cadr equation) conclusion))
        (mv nil domain (caddr equation) theorem)
      (mv :correspondence-conclusion ''t nil theorem))))))

(defun fn2-square-evidence-events-with-correspondence
 (name positive negative correspondence recheck world)
 (declare (xargs :verify-guards nil))
 (let* ((row (fn2-decl-row (list :square name) world))
        (vars (fn2-decl-get :vars row))
        (formula (fn2-decl-statement-body (fn2-decl-get :statement row) world))
        (pos-name (fn2-evidence-name name "$BOUND-POSITIVE"))
        (neg-name (fn2-evidence-name name "$BOUND-NEGATIVE"))
        (mode (fn2-decl-get :kind negative))
        (at (fn2-decl-get :at negative))
        (mutant (fn2-decl-get :replace negative))
        (removed (fn2-decl-get :remove negative))
        (neg-bindings (fn2-decl-get :bindings negative)))
  (mv-let (hyp conclusion) (fn2-evidence-parts formula)
   (mv-let (normalization-problem normalization-domain normalized correspondence-body)
    (fn2-evidence-normalization conclusion correspondence world)
   (let* ((lhs (cadr normalized)) (rhs (caddr normalized))
          (hypotheses (fn2-evidence-hypotheses hyp))
          (mut-call (cons mutant (cdr lhs)))
          (domain `(and ,(fn2-evidence-call-guard lhs world)
                        ,(fn2-evidence-call-guard rhs world)))
          (pos-body `(let ,positive (and ,domain ,normalization-domain ,hyp ,conclusion ,normalized)))
          (neg-body
           (if (eq mode :mutation)
               `(let ,neg-bindings
                  (and ,domain ,(fn2-evidence-call-guard mut-call world)
                       ,normalization-domain ,hyp ,conclusion ,normalized
                       (not (equal ,mut-call ,rhs))))
             `(let ,neg-bindings
                (and ,domain ,normalization-domain ,@(remove-equal removed hypotheses)
                     (not ,removed) (not ,conclusion) (not ,normalized)))))
          (domain-event `(thm (implies ,hyp ,normalization-domain)))
          (pos-hints (and correspondence
                         `(("Goal" :use ((:instance ,correspondence ,@positive))))))
          (neg-hints (and correspondence
                         `(("Goal" :use ((:instance ,correspondence ,@neg-bindings))))))
          (problem
           (cond
            ((not (and row (fn2-decl-get :statement row))) :unknown-statement)
            ((not (equal formula (fn2-decl-get :translated row))) :stale-statement)
            (normalization-problem normalization-problem)
            ((not (subsetp-eq (union-eq (all-vars normalization-domain)
                                       (all-vars normalized)) vars)) :correspondence-variables)
            ((and (not recheck) (fn2-decl-get :evidence row)) :already-bound)
            ((not (and (symbol-listp vars) (no-duplicatesp-eq vars)
                       (fn2-evidence-bindingsp positive vars)
                       (fn2-evidence-bindingsp neg-bindings vars))) :bindings)
            ((not (and (consp normalized) (eq (car normalized) 'equal)
                       (equal (len normalized) 3)
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
         `(make-event (er soft 'defsquare-evidence "Cannot bind ~x0: ~x1. Live statement: ~x2."
                          ',name ',problem ',formula))
       (if recheck
           `(progn ,domain-event
                   (thm ,pos-body :hints ,pos-hints)
                   (thm ,neg-body :hints ,neg-hints))
        `(progn
          ,domain-event
          (defthm ,pos-name ,pos-body :rule-classes nil :hints ,pos-hints)
          (defthm ,neg-name ,neg-body :rule-classes nil :hints ,neg-hints)
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
                 :correspondence ,correspondence :correspondence-body ,correspondence-body
                 :normalization-domain ,normalization-domain :normalized-conclusion ,normalized
                 :positive ,pos-name :negative ,neg-name
                 :positive-body ,pos-body :negative-body ,neg-body
                 :positive-bindings ,positive :negative-control ,negative
                 :functions (,(fn2-evidence-function-binding (car lhs) world)
                             ,(fn2-evidence-function-binding (car rhs) world)
                             ,@(and (eq mode :mutation)
                                    (list (fn2-evidence-function-binding mutant world)))))))
               (fn2-decl-row '(:square ,name) (w state)))))))))))))))

; Preserve the five-argument API used by constructor/snapshot consumers.
(defun fn2-square-evidence-events (name positive negative recheck world)
 (declare (xargs :verify-guards nil))
 (fn2-square-evidence-events-with-correspondence name positive negative nil recheck world))

(defmacro defsquare-evidence (name &key positive negative correspondence)
 `(make-event
   (value (fn2-square-evidence-events-with-correspondence
            ',name ',positive ',negative ',correspondence nil (w state)))))

(defun fn2-evidence-functions-currentp (bindings world)
 (declare (xargs :verify-guards nil))
 (if (atom bindings) (null bindings)
  (and (equal (car bindings) (fn2-evidence-function-binding (caar bindings) world))
       (fn2-evidence-functions-currentp (cdr bindings) world))))
(defun fn2-evidence-normalization-currentp (e conclusion world)
 (declare (xargs :verify-guards nil))
 (mv-let (problem domain normalized theorem)
   (fn2-evidence-normalization conclusion (fn2-decl-get :correspondence e) world)
  (and (not problem)
       (equal (fn2-decl-get :correspondence-body e) theorem)
       (equal (fn2-decl-get :normalization-domain e) domain)
       (equal (fn2-decl-get :normalized-conclusion e) normalized))))
(defmacro fn2-assert-square-evidence (name)
 `(make-event
   (let* ((row (fn2-decl-row '(:square ,name) (w state)))
          (e (fn2-decl-get :evidence row))
          (correspondence (fn2-decl-get :correspondence e))
          (negative (fn2-decl-get :negative-control e))
          (sides (fn2-decl-get :sides row))
          (pos-name (fn2-evidence-name ',name "$BOUND-POSITIVE"))
          (neg-name (fn2-evidence-name ',name "$BOUND-NEGATIVE")))
    (if (not (and (eq (fn2-decl-get :kind e) :formula-ground-proofs)
                  (equal (fn2-decl-get :formula e)
                         (fn2-decl-statement-body (fn2-decl-get :statement row) (w state)))
                  (equal (fn2-decl-get :translated e) (fn2-decl-get :translated row))
                  (equal (fn2-decl-get :correspondence-body e)
                         (and correspondence (getpropc correspondence 'theorem nil (w state))))
                  (mv-let (hyp conclusion)
                    (fn2-evidence-parts
                     (fn2-decl-statement-body (fn2-decl-get :statement row) (w state)))
                   (declare (ignore hyp))
                   (fn2-evidence-normalization-currentp e conclusion (w state)))
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
     (value (fn2-square-evidence-events-with-correspondence
              ',name (fn2-decl-get :positive-bindings e)
              (fn2-decl-get :negative-control e) correspondence t (w state)))))))
