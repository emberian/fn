; E2 Q1 consumes E1's case source and the existing owed composition formula.
(in-package "ACL2")
(include-book "defsquare")
(include-book "q1-contract")

(defun sq-q1-case-origin (case)
  (if (member-eq (car case) '(:run :observe)) (list :machine (cadr case))
    (if (eq (car case) :router) '(:router :dispatch) '(:executor :transition))))
(defun sq-q1-id (index)
  (packn-pos (list 'sq-q1-case- (nfix index)) 'sq-q1))
(defun sq-q1-bind-cases (cases index contract sides)
  (declare (xargs :verify-guards nil))
  (if (atom cases) nil
    (let* ((case (car cases)) (id (sq-q1-id index)))
      (cons
       (cons case
        (list :id id :schema :g1 :origin (sq-q1-case-origin case)
              :boundary :loop-iteration :vars '(ctx concrete reference lists)
              :formula (sq-q1-case-formula case contract sides) :proof '(:owed)
              :requires '(sq-q1-entry sq-q1-exit sq-q1-partition)
              :checker (list :function 'sq-q1-check-sample :case case)
              :teeth (list :positive (fn2-columns-sym id "-POSITIVE")
                           :negative (fn2-columns-sym id "-NEGATIVE"))
              :evidence '((:provider sq-q1-run-campaigns
                          :campaigns (:random :enumeration) :seed 1
                          :transition-budget 20000 :enumeration-depth 4
                          :wall-seconds 20))))
       (sq-q1-bind-cases (cdr cases) (+ 1 (nfix index)) contract sides)))))
(defun sq-q1-bindings (world contract sides)
  (declare (xargs :verify-guards nil))
  (let* ((entry (cdr (assoc-eq 'fn2-turn-refinement (table-alist 'fn2-owed world))))
         (formula (cadr (member-eq :formula entry)))
         (vars (cadr (member-eq :vars entry))))
    (append
     (sq-q1-bind-cases *fn2-e1-labels* 0 contract sides)
     (list
      (cons '(:composition fn2-turn-refinement)
            (list :id 'sq-q1-composition :schema :g1 :origin '(:owed fn2-turn-refinement)
                  :boundary :turn :vars vars :formula formula :proof '(:owed)
                  :template :q1-turn-composition
                  :contract '(:relation fn2-representation-relation)
                  :sides '(:concrete (fn2-turn) :reference (fn2-ref-turn))
                  :requires '(sq-q1-entry sq-q1-exit sq-q1-termination sq-q1-partition sq-q1-accounting)
                  :checker nil
                  :teeth '(:positive fn2-reference-teeth :negative sq-q1-composition-negative)
                  :evidence nil))))))

(make-event
 (value `(defsquare sq-q1
  :template :q1-loop-iteration
  :cases-from (append *fn2-e1-labels* '((:composition fn2-turn-refinement)))
  :bindings (sq-q1-bindings (w state) *sq-q1-contract* *sq-q1-sides*)
  :contract ,*sq-q1-contract* :sides ,*sq-q1-sides*)))

; The boundary links are named as unresolved requirements, not t-valued rows.
; Coverage here is 39 iteration labels + the unchanged composition statement;
; entry, exit, selector partition and accounting remain separate owed work.
