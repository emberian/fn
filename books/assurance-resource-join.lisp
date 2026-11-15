; Independently required descriptor contracts, joined to ACTUAL served calls.
; These are specifications, not a second executable model or obligation table.
(in-package "ACL2")
(include-book "owed")

(defun fn2-assurance-required-residual-formula ()
 (declare (xargs :guard t))
 '(implies (and (fn2-corep core) (fn2-core-wfp core) (natp budget))
           (<= (mv-nth 2 (fn2-machine-run id budget core)) budget)))

(defun fn2-assurance-required-turn-formula ()
 (declare (xargs :guard t))
 '(implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
   (and (natp (mv-nth 3 (fn2-turn fn2-core)))
        (<= (mv-nth 3 (fn2-turn fn2-core)) (fn2-exec-aturn fn2-core)))))

(defun fn2-assurance-resource-abi-problems (fn formals inputs outputs world)
 (declare (xargs :verify-guards nil))
 (append
  (and (not (getpropc fn 'unnormalized-body nil world))
       (list (list fn :missing-actual-logical-body)))
  (and (not (equal (getpropc fn 'formals :missing world) formals))
       (list (list fn :wrong-actual-formals)))
  (and (not (equal (getpropc fn 'stobjs-in :missing world) inputs))
       (list (list fn :wrong-actual-input-abi)))
  (and (not (equal (getpropc fn 'stobjs-out :missing world) outputs))
       (list (list fn :wrong-actual-result-abi)))
  (and (not (equal (getpropc fn 'guard :missing world) '(fn2-core-wfp fn2-core)))
       (list (list fn :wrong-actual-guard)))
  (and (not (eq (getpropc fn 'symbol-class nil world) :common-lisp-compliant))
       (list (list fn :guard-verification-missing)))))

(defun fn2-assurance-resource-join-problems (world)
 (declare (xargs :verify-guards nil))
 (let* ((row (fn2-decl-row '(:square fn2-arm-residual-budget) world))
        (statement (fn2-decl-get :statement row))
        (proof (fn2-decl-get :proof row))
        (required-residual
         (fn2-decl-statement-body 'fn2-assurance-required-residual$spec world))
        (required-turn
         (fn2-decl-statement-body 'fn2-assurance-required-turn$spec world)))
  (append
   (and (not (and row (fn2-square-rowp 'fn2-arm-residual-budget row world)
                  (eq (car proof) :proved)))
        '((fn2-arm-residual-budget :missing-exact-admitted-claim)))
   (and (not (and required-residual
                  (equal (fn2-decl-get :vars row) '(id budget core))
                  (equal (fn2-decl-statement-body statement world) required-residual)))
        '((fn2-arm-residual-budget :required-descriptor-specification-mismatch)))
   ; Exact independently translated public contract, not function occurrence.
   (and (not (and required-turn
                  (equal (getpropc 'fn2-turn-actions-within-limit 'theorem nil world)
                         required-turn)))
        '((fn2-turn-actions-within-limit :required-public-turn-specification-mismatch)))
   (fn2-assurance-resource-abi-problems 'fn2-machine-run '(id budget fn2-core)
       '(nil nil fn2-core) '(nil nil nil nil fn2-core) world)
   (fn2-assurance-resource-abi-problems 'fn2-turn '(fn2-core)
       '(fn2-core) '(nil nil nil nil fn2-core) world)
   (fn2-assurance-resource-abi-problems 'fn2-exec-aturn '(fn2-core)
       '(fn2-core) '(nil) world))))

; Invoke after the real executor/dispatcher composition is admitted. ACL2
; translates the independently owned specifications in that same world.
; The following event checks exact live statements and REPROVES the required
; formulas using actual admitted theorems; a metadata flag supplies nothing.
(defmacro fn2-join-served-resource-contracts ()
 `(progn
   (defun-nx fn2-assurance-required-residual$spec (id budget core)
     ,(fn2-assurance-required-residual-formula))
   (defun-nx fn2-assurance-required-turn$spec (fn2-core)
     ,(fn2-assurance-required-turn-formula))
   (make-event
    (let* ((world (w state)) (problems (fn2-assurance-resource-join-problems world))
           (row (fn2-decl-row '(:square fn2-arm-residual-budget) world))
           (proof (cadr (fn2-decl-get :proof row))))
     (if problems
         (er soft 'fn2-join-served-resource-contracts "Required served contract mismatch: ~x0."
             problems)
      (value
       `(progn
         (defthm fn2-assurance-residual-descriptors-joined
           ,(fn2-assurance-required-residual-formula)
           :rule-classes nil
           :hints (("Goal" :use ,proof
                    :in-theory (e/d (fn2-arm-residual-budget$owed)
                                     (fn2-machine-run fn2-corep fn2-core-wfp)))))
         (defthm fn2-assurance-public-turn-descriptors-joined
           ,(fn2-assurance-required-turn-formula)
           :rule-classes nil
           :hints (("Goal" :use fn2-turn-actions-within-limit
                    :in-theory (disable fn2-turn fn2-exec-aturn fn2-corep fn2-core-wfp)))))))))))
