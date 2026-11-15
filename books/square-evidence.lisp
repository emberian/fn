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

; Only beta-reduce translated first-order lambdas. No function definitions,
; tests or arithmetic are evaluated. Normalizing body and arguments before
; substitution cannot create a new lambda application in first-order ACL2.
(mutual-recursion
 (defun fn2-evidence-beta (term)
  (declare (xargs :verify-guards nil))
  (cond ((atom term) term) ((eq (car term) 'quote) term)
        ((consp (car term))
         (sublis-var (pairlis$ (cadar term) (fn2-evidence-beta-list (cdr term)))
                     (fn2-evidence-beta (caddar term))))
        (t (cons (car term) (fn2-evidence-beta-list (cdr term))))))
 (defun fn2-evidence-beta-list (terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
   (cons (fn2-evidence-beta (car terms)) (fn2-evidence-beta-list (cdr terms))))))
(mutual-recursion
 (defun fn2-evidence-occurs (subject term)
  (declare (xargs :verify-guards nil))
  (and (consp term) (not (eq (car term) 'quote))
       (or (equal subject term) (fn2-evidence-occurs-list subject (cdr term)))))
 (defun fn2-evidence-occurs-list (subject terms)
  (declare (xargs :verify-guards nil))
  (and (consp terms)
       (or (fn2-evidence-occurs subject (car terms))
           (fn2-evidence-occurs-list subject (cdr terms))))))
(mutual-recursion
 (defun fn2-evidence-replace (subject replacement term)
  (declare (xargs :verify-guards nil))
  (cond ((atom term) term) ((eq (car term) 'quote) term)
        ((equal subject term) replacement)
        (t (cons (car term) (fn2-evidence-replace-list subject replacement (cdr term))))))
 (defun fn2-evidence-replace-list (subject replacement terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
   (cons (fn2-evidence-replace subject replacement (car terms))
         (fn2-evidence-replace-list subject replacement (cdr terms))))))

; A wrapper may only return ALL outputs of one actual call, once each and
; in order. The subject and arguments must also occur in the original C.
(defun fn2-evidence-tuple-projection (term index subject)
 (declare (xargs :verify-guards nil))
 (if (equal term ''nil) (mv nil index subject)
  (let ((item (cadr term)))
   (if (and (consp term) (eq (car term) 'cons) (equal (len term) 3)
            (consp item) (eq (car item) 'mv-nth) (equal (len item) 3)
            (equal (cadr item) (list 'quote index))
            (or (not subject) (equal subject (caddr item))))
       (fn2-evidence-tuple-projection (caddr term) (+ 1 index) (caddr item))
     (mv :unsupported-result-projection index subject)))))
(defun fn2-evidence-projection-subject (lhs conclusion world)
 (declare (xargs :verify-guards nil))
 (let* ((original (fn2-evidence-beta conclusion))
        (body (fn2-decl-statement-body (car lhs) world))
        (body (sublis-var (pairlis$ (getpropc (car lhs) 'formals nil world) (cdr lhs)) body)))
  (if (fn2-evidence-occurs lhs original) (mv nil lhs)
   (mv-let (problem count subject)
     (fn2-evidence-tuple-projection (fn2-evidence-beta body) 0 nil)
    ; One output is an ordinary value, NOT a singleton MV tuple. Wrapping
    ; its CAR in a list would lose the rest of that value.
    (if (and (not problem) (< 1 count) (fn2-evidence-callp subject world)
             (equal count (len (getpropc (car subject) 'stobjs-out nil world)))
             (fn2-evidence-occurs subject original))
        (mv nil subject)
      (mv :unbound-result-projection nil))))))

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
   (mv-let (projection-problem subject)
    (if correspondence
        (fn2-evidence-projection-subject (cadr normalized) conclusion world)
      (mv nil (cadr normalized)))
   (let* ((lhs (cadr normalized)) (rhs (caddr normalized))
          (hypotheses (fn2-evidence-hypotheses hyp))
          (mut-call (cons mutant (cdr lhs)))
          (domain `(and ,(fn2-evidence-call-guard lhs world)
                        ,(fn2-evidence-call-guard rhs world)
                        ,(fn2-evidence-call-guard subject world)))
          (mutated-conclusion
           (if correspondence
               (fn2-evidence-replace subject mut-call (fn2-evidence-beta conclusion))
             `(equal ,mut-call ,rhs)))
          (pos-body `(let ,positive (and ,domain ,normalization-domain ,hyp ,conclusion ,normalized)))
          (neg-body
           (if (eq mode :mutation)
               `(let ,neg-bindings
                  (and ,domain ,(fn2-evidence-call-guard mut-call world)
                       ,normalization-domain ,hyp ,conclusion ,normalized
                       (not ,mutated-conclusion)
                       (not (equal ,mut-call ,rhs))))
             `(let ,neg-bindings
                (and ,domain ,normalization-domain ,@(remove-equal removed hypotheses)
                     (not ,removed) (not ,conclusion) (not ,normalized)))))
          (domain-event
           `(thm (implies ,hyp ,(if correspondence `(and ,normalization-domain ,domain)
                                  normalization-domain))))
          (pos-hints (and correspondence
                         `(("Goal" :use ((:instance ,correspondence ,@positive))))))
          (neg-hints (and correspondence
                         `(("Goal" :use ((:instance ,correspondence ,@neg-bindings))))))
          (problem
           (cond
            ((not (and row (fn2-decl-get :statement row))) :unknown-statement)
            ((not (equal formula (fn2-decl-get :translated row))) :stale-statement)
            (normalization-problem normalization-problem)
            (projection-problem projection-problem)
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
                 :subject-call ,subject
                 :positive ,pos-name :negative ,neg-name
                 :positive-body ,pos-body :negative-body ,neg-body
                 :positive-bindings ,positive :negative-control ,negative
                 :functions (,(fn2-evidence-function-binding (car lhs) world)
                             ,(fn2-evidence-function-binding (car rhs) world)
                             ,@(and correspondence
                                    (list (fn2-evidence-function-binding (car subject) world)))
                             ,@(and (eq mode :mutation)
                                    (list (fn2-evidence-function-binding mutant world)))))))
               (fn2-decl-row '(:square ,name) (w state))))))))))))))))

; Predicate evidence concerns the exact logical H/C, not endpoint equivalence.
; Closed constructor terms are permitted here: ACL2 must admit both complete
; ground assertions. They are never executed as malformed raw stobjs.
(defun fn2-evidence-closed-bindingsp (bindings vars)
 (declare (xargs :verify-guards nil))
 (and (true-list-listp bindings) (equal (strip-cars bindings) vars)
      (if (atom bindings) t
       (and (equal (len (car bindings)) 2)
            (pseudo-termp (cadar bindings))
            (null (all-vars (cadar bindings)))
            (fn2-evidence-closed-bindingsp (cdr bindings) (cdr vars))))))

 ; Remove exactly one structural conjunct, possibly a composite stored guard.
; No implication rewriting or logically equivalent selector is accepted.
(defun fn2-evidence-hypothesis-cut (hyp removed)
 (declare (xargs :verify-guards nil))
 (cond ((equal hyp removed) (mv 1 nil))
       ((and (consp hyp) (eq (car hyp) 'if) (equal (len hyp) 4)
             (equal (cadddr hyp) ''nil))
        (mv-let (left-count left) (fn2-evidence-hypothesis-cut (cadr hyp) removed)
         (mv-let (right-count right) (fn2-evidence-hypothesis-cut (caddr hyp) removed)
          (mv (+ left-count right-count) (append left right)))))
       (t (mv 0 (list hyp)))))

(defun fn2-square-predicate-evidence-events-with-hints
 (name positive negative positive-hints negative-hints recheck world)
 (declare (xargs :verify-guards nil))
 (let* ((row (fn2-decl-row (list :square name) world))
        (vars (fn2-decl-get :vars row))
        (formula (fn2-decl-statement-body (fn2-decl-get :statement row) world))
        (removed (fn2-decl-get :remove negative))
        (bindings (fn2-decl-get :bindings negative))
        (pos-name (fn2-evidence-name name "$BOUND-POSITIVE"))
        (neg-name (fn2-evidence-name name "$BOUND-NEGATIVE")))
  (mv-let (hyp conclusion) (fn2-evidence-parts formula)
   (mv-let (removed-count remaining) (fn2-evidence-hypothesis-cut hyp removed)
   (let* ((pos-body `(let ,positive (and ,hyp ,conclusion)))
          (neg-body `(let ,bindings
                      (and ,@remaining
                           (not ,removed) (not ,conclusion))))
          (problem
           (cond
            ((not (and row (fn2-decl-get :statement row))) :unknown-statement)
            ((not (equal formula (fn2-decl-get :translated row))) :stale-statement)
            ((and (not recheck) (fn2-decl-get :evidence row)) :already-bound)
            ((not (and (symbol-listp vars) (no-duplicatesp-eq vars)
                       (fn2-evidence-closed-bindingsp positive vars)
                       (fn2-evidence-closed-bindingsp bindings vars))) :bindings)
            ; An actual predicate call, not a constant, equality, IF or an
            ; author-supplied substitute formula. Its truth is proved below.
            ((not (and (fn2-evidence-callp conclusion world)
                       (not (member-eq (car conclusion) '(equal if implies quote)))))
             :predicate-shape)
            ((not (eq (fn2-decl-get :kind negative) :hypothesis-removal)) :negative-kind)
            ((not (equal removed-count 1)) :removed-hypothesis)
            ((and (not recheck)
                  (or (getpropc pos-name 'theorem nil world)
                      (getpropc neg-name 'theorem nil world))) :name-collision))))
    (if problem
        `(make-event (er soft 'defsquare-evidence "Cannot bind predicate ~x0: ~x1."
                         ',name ',problem))
     (if recheck `(progn (thm ,pos-body :hints ,positive-hints)
                       (thm ,neg-body :hints ,negative-hints))
      `(progn
        (defthm ,pos-name ,pos-body :rule-classes nil :hints ,positive-hints)
        (defthm ,neg-name ,neg-body :rule-classes nil :hints ,negative-hints)
        (make-event
         (value
          (list 'table 'fn2-squares (list 'quote ',name)
           (list 'quote
            (fn2-decl-set :evidence
             (fn2-decl-set :positive-theorem (getpropc ',pos-name 'theorem nil (w state))
              (fn2-decl-set :negative-theorem (getpropc ',neg-name 'theorem nil (w state))
               '(:kind :formula-ground-proofs :conclusion-kind :predicate
                 :formula ,formula :translated ,(fn2-decl-get :translated row)
                 :positive ,pos-name :negative ,neg-name
                 :positive-body ,pos-body :negative-body ,neg-body
                 :positive-bindings ,positive :negative-control ,negative
                 :positive-hints ,positive-hints :negative-hints ,negative-hints)))
             (fn2-decl-row '(:square ,name) (w state)))))))))))))))

; Existing programmatic consumers retain the five-argument entry point.
(defun fn2-square-predicate-evidence-events (name positive negative recheck world)
 (declare (xargs :verify-guards nil))
 (fn2-square-predicate-evidence-events-with-hints
  name positive negative nil nil recheck world))

; Preserve the five-argument API used by constructor/snapshot consumers.
(defun fn2-square-evidence-events (name positive negative recheck world)
 (declare (xargs :verify-guards nil))
 (fn2-square-evidence-events-with-correspondence name positive negative nil recheck world))

(defmacro defsquare-evidence
 (name &key positive negative correspondence conclusion-kind positive-hints negative-hints)
 `(make-event
   (value
    (if (and (eq ',conclusion-kind :predicate) (not ',correspondence))
        (fn2-square-predicate-evidence-events-with-hints
         ',name ',positive ',negative ',positive-hints ',negative-hints nil (w state))
      (if (or ',conclusion-kind ',positive-hints ',negative-hints)
          '(make-event (er soft 'defsquare-evidence "Unsupported conclusion mode."))
        (fn2-square-evidence-events-with-correspondence
         ',name ',positive ',negative ',correspondence nil (w state)))))))

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
       (equal (fn2-decl-get :normalized-conclusion e) normalized)
       (mv-let (projection-problem subject)
         (if (fn2-decl-get :correspondence e)
             (fn2-evidence-projection-subject (cadr normalized) conclusion world)
           (mv nil (cadr normalized)))
        (and (not projection-problem)
             (equal (fn2-decl-get :subject-call e) subject))))))
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
                   (if (eq (fn2-decl-get :conclusion-kind e) :predicate)
                       (and (not correspondence) (not (fn2-decl-get :functions e)))
                     (fn2-evidence-normalization-currentp e conclusion (w state))))
                  (equal (fn2-decl-get :positive e) pos-name)
                  (equal (fn2-decl-get :negative e) neg-name)
                  (getpropc pos-name 'theorem nil (w state))
                  (getpropc neg-name 'theorem nil (w state))
                  (equal (fn2-decl-get :positive-theorem e) (getpropc pos-name 'theorem nil (w state)))
                  (equal (fn2-decl-get :negative-theorem e) (getpropc neg-name 'theorem nil (w state)))
                  (equal (strip-cars (fn2-decl-get :functions e))
                         (if (eq (fn2-decl-get :conclusion-kind e) :predicate) nil
                          (append (list (fn2-decl-get :concrete sides) (fn2-decl-get :reference sides))
                                 (and correspondence (list (car (fn2-decl-get :subject-call e))))
                                 (and (eq (fn2-decl-get :kind negative) :mutation)
                                      (list (fn2-decl-get :replace negative))))))
                  (fn2-evidence-functions-currentp (fn2-decl-get :functions e) (w state))))
        (er soft 'fn2-assert-square-evidence "Missing or stale formula evidence: ~x0." ',name)
     ; Re-derive and prove both complete assertions.  Stored names, bodies or
     ; a claimed PASS flag are never evidence by themselves.
     (value (if (eq (fn2-decl-get :conclusion-kind e) :predicate)
                (fn2-square-predicate-evidence-events-with-hints
                 ',name (fn2-decl-get :positive-bindings e) negative
                 (fn2-decl-get :positive-hints e) (fn2-decl-get :negative-hints e) t (w state))
              (fn2-square-evidence-events-with-correspondence
              ',name (fn2-decl-get :positive-bindings e)
              (fn2-decl-get :negative-control e) correspondence t (w state))))))))
