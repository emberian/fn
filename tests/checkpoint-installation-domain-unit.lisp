; The actual emitted BT caller, not the quoted coordinator provider.
; This checks a call-domain connection, not activation or successful staging.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-bt")
(include-book "../books/square-evidence")

(local
 (mutual-recursion
  (defun fn2-member-domain-calls (fn term)
   (declare (xargs :verify-guards nil))
   (cond ((atom term) nil) ((eq (car term) 'quote) nil)
         ((eq (car term) fn) (list term))
         (t (fn2-member-domain-calls-list fn (cdr term)))))
  (defun fn2-member-domain-calls-list (fn terms)
   (declare (xargs :verify-guards nil))
   (if (atom terms) nil
    (append (fn2-member-domain-calls fn (car terms))
            (fn2-member-domain-calls-list fn (cdr terms)))))))

(local (defun fn2-member-domain-callsp (expected calls)
 (equal calls (list expected))))

(make-event
 (let* ((world (w state))
        (caller 'fn2-checkpoint-installation-step)
        (callee 'fn2-checkpoint-installation-pack-member)
        (theorem 'fn2-checkpoint-installation-pack-member-fields-type-under-guard)
        (guard (getpropc caller 'guard :missing world))
        (body (fn2-decl-statement-body caller world))
        (calls (remove-duplicates-equal
                (fn2-member-domain-calls callee (fn2-evidence-beta body))))
        (rc '(fn2-core-retirement-control fn2-core))
        ; These are the scalar bindings at the actual pack branch, not freely
        ; chosen values that happen to satisfy the callee's guard.
        (expected
         `(,callee
           (fn2-retirement-control-candidate '0 ,rc) '0
           (fn2-retirement-control-slot '0 ,rc)
           (fn2-retirement-control-gen '0 ,rc)
           (fn2-retirement-control-owner-kind '0 ,rc)
           (fn2-retirement-control-owner-slot '0 ,rc)
           (fn2-retirement-control-owner-gen '0 ,rc)
           (fn2-core-checkpoints fn2-core)
           (fn2-core-checkpoint-refs fn2-core)
           (fn2-core-checkpoint-bytes fn2-core)
           (fn2-core-fields fn2-core) (fn2-core-pool fn2-core)))
        (args (getpropc callee 'formals nil world))
        (formula (getpropc theorem 'theorem nil world))
        (bindings (pairlis$ args (cdr expected)))
        (core-h '(if (fn2-corep fn2-core) (fn2-core-wfp fn2-core) 'nil))
        (result '(mv-nth '1 (fn2-checkpoint-installation-step fn2-core))))
  (mv-let (h c) (fn2-evidence-parts formula)
   (if (not
        (and body formula (not (eq guard :missing))
             (eq (symbol-class caller world) :common-lisp-compliant)
             (eq (symbol-class callee world) :common-lisp-compliant)
             (equal (getpropc caller 'formals nil world) '(fn2-core))
             (equal (getpropc caller 'stobjs-in nil world) '(fn2-core))
             (equal (getpropc caller 'stobjs-out nil world) '(nil fn2-core))
             (equal args '(c base slot gen okind oslot ogen
                fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool))
             (fn2-member-domain-callsp expected calls)
             (equal c `(fn2-fieldsp (mv-nth '2 (,callee ,@args))))
             ; Actual emitted preservation facts must also exist with their
             ; complete original core-domain hypotheses and full core result.
             (equal (getpropc 'fn2-checkpoint-installation-step-preserves-type 'theorem nil world)
                    `(implies ,core-h (fn2-corep ,result)))
             (equal (getpropc 'fn2-checkpoint-installation-step-preserves-wfp 'theorem nil world)
                    `(implies ,core-h (fn2-core-wfp ,result)))))
       (er soft 'checkpoint-installation-domain
           "Actual emitted STEP, guard, call bindings or preservation facts changed.")
     (value
      `(progn
        ; Replacing only the scalar base or only the readonly child cannot
        ; qualify as the same actual call, even if a guard proof were easy.
        (assert-event
         (not (fn2-member-domain-callsp ',(update-nth 2 ''1 expected) ',calls)))
        (assert-event
         (not (fn2-member-domain-callsp
               ',(update-nth 8 '(fn2-core-fields fn2-core) expected) ',calls)))
        (defthm fn2-checkpoint-installation-step-supplies-member-domain
         (implies ,guard ,(sublis-var bindings h))
         :rule-classes nil
         :hints (("Goal" :in-theory
                  (disable fn2-corep fn2-core-wfp ,caller ,callee))))
        (defthm fn2-checkpoint-installation-step-member-fields-type
         (implies ,guard ,(sublis-var bindings c))
         :rule-classes nil
         :hints (("Goal"
                  :use (fn2-checkpoint-installation-step-supplies-member-domain
                        (:instance ,theorem ,@(pairlis$ args (pairlis$ (cdr expected) nil))))
                  :in-theory (disable fn2-corep fn2-core-wfp ,caller ,callee))))))))))
