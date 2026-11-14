; Completion consumes the ONE live obligation store. This checker does not
; infer specification completeness or turn finite witnesses into a theorem.
(in-package "ACL2")
(include-book "square-evidence")

(defun fn2-assurance-row-problems (name entrypoints world)
 (declare (xargs :verify-guards nil))
 (let* ((row (fn2-decl-row (list :square name) world))
        (statement (fn2-decl-get :statement row))
        (body (fn2-decl-statement-body statement world)))
  (append
   (and (not row) (list (list name :missing-square)))
   (and row (not (fn2-square-rowp name row world))
        (list (list name :invalid-live-statement-or-proof)))
   (and row (not statement) (list (list name :unbound-requirement)))
   (and row (not (eq (car (fn2-decl-get :proof row)) :proved))
        (list (list name :unproved)))
   (and row (not (and (symbol-listp (fn2-decl-get :depends row))
                      (no-duplicatesp-eq (fn2-decl-get :depends row))))
        (list (list name :malformed-dependencies)))
   ; Marked dead branches cannot discharge a public guarantee, even if an
   ; admitted theorem and impressive ground checks exist for that branch.
   (and row (or (fn2-decl-get :unreachable-in-composition row)
                (eq (fn2-decl-get :reachability row) :unreachable-in-composition))
        (list (list name :unreachable-in-composition)))
   (and row (not (subsetp-eq entrypoints (all-fnnames body)))
        (list (list name :missing-served-binding entrypoints)))
   (and row (not (eq (fn2-decl-get :kind (fn2-decl-get :evidence row))
                     :formula-ground-proofs))
        (list (list name :missing-formula-bound-controls))))))

; Depth is bounded by the number of live rows. A repeated node on the active
; path is a cycle, not a proof. Dependencies must remain registry rows so
; missing required claims cannot be hidden behind arbitrary theorem names.
(defun fn2-assurance-walk (todo active fuel world)
 (declare (xargs :verify-guards nil :measure (nfix fuel)))
 (if (atom todo) nil
  (if (zp fuel) (list (list :dependency-depth-or-cycle todo))
   (let* ((name (car todo))
          (row (fn2-decl-row (list :square name) world)))
    (append
     (if (member-eq name active) (list (list name :dependency-cycle))
      (append (fn2-assurance-row-problems name nil world)
       (fn2-assurance-walk (fn2-decl-get :depends row)
                           (cons name active) (1- fuel) world)))
     (fn2-assurance-walk (cdr todo) active (1- fuel) world))))))

(defun fn2-assurance-required-problems (requirements world)
 (declare (xargs :verify-guards nil))
 (if (atom requirements) nil
  (let* ((r (car requirements)) (name (cadr r)) (entries (caddr r)))
   (append
    (and (not entries) (list (list (car r) :missing-required-entrypoint)))
    (fn2-assurance-row-problems name entries world)
    (fn2-assurance-walk (fn2-decl-get :depends (fn2-decl-row (list :square name) world))
                        (list name) (expt (+ 1 (len (fn2-decl-rows :square world))) 2) world)
    (fn2-assurance-required-problems (cdr requirements) world)))))

(defun fn2-assurance-evidence-events (todo seen fuel world)
 (declare (xargs :verify-guards nil :measure (nfix fuel)))
 (if (atom todo) nil
  (if (zp fuel)
      '((make-event (er soft 'fn2-assert-assurance-complete "Evidence traversal exhausted.")))
  (let* ((name (car todo)) (row (fn2-decl-row (list :square name) world)))
   (if (member-eq name seen)
       (fn2-assurance-evidence-events (cdr todo) seen (1- fuel) world)
    (cons `(fn2-assert-square-evidence ,name)
     (append
      (fn2-assurance-evidence-events (fn2-decl-get :depends row)
                                    (cons name seen) (1- fuel) world)
      (fn2-assurance-evidence-events (cdr todo) (cons name seen) (1- fuel) world))))))))

(defun fn2-assurance-root-names (requirements)
 (declare (xargs :verify-guards nil))
 (if (atom requirements) nil
  (cons (cadar requirements) (fn2-assurance-root-names (cdr requirements)))))

(defmacro fn2-assert-assurance-complete (requirements)
 `(make-event
   (let* ((requirements ,requirements)
          (problems (if (consp requirements)
                        (fn2-assurance-required-problems requirements (w state))
                      '((:missing-required-scope)))))
    (if problems
        (er soft 'fn2-assert-assurance-complete "Required assurance remains incomplete: ~x0."
            problems)
     ; Metadata is insufficient: regenerate and prove the ground assertions
     ; against these very bodies/guards/ABIs, after checking universal proofs.
     (value (cons 'progn
       (fn2-assurance-evidence-events (fn2-assurance-root-names requirements) nil
          (+ 1 (* (+ 1 (len requirements))
                  (expt (+ 1 (len (fn2-decl-rows :square (w state)))) 2))) (w state)))))))))
