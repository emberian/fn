; The Q1 correspondence's check evidence (DSL-METATHEORY 3.4 item 1, DM3):
; every row the store binds with a :checker gets the record its own checker
; computes from the A4 driver's per-case tallies (tests/evidence/, written by
; q1-case-hook.lsp), and every arm's K-P-BOUND row gets the record of the
; run-time certificate the generated run entry asserted at each (:run K P)
; transition. Unreached cases and arms are recorded :unchecked with zero
; exercised. A checked row stays owed.
(in-package "ACL2")
(include-book "../sim/check-trace")
(include-book "evidence/q1-a4-tally")

(defun fn2-q1-evidence-case-events (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let* ((row (cdar rows)) (checker (fn2-decl-get :checker row)))
      (append (and (equal (fn2-decl-get :owner row) '(:correspondence fn2-q1))
                   (fn2-decl-get :statement row) checker
                   `((fn2-square-append-evidence
                      ,(caar rows)
                      (list (,(fn2-decl-get :function checker) ',(fn2-decl-get :case checker)
                             *fn2-q1-a4-cases* *fn2-q1-a4-run*)))))
              (fn2-q1-evidence-case-events (cdr rows))))))
(defun fn2-q1-evidence-arm-events (labels world)
  (declare (xargs :verify-guards nil))
  (if (atom labels) nil
    (let* ((label (car labels))
           (id (and (eq (car label) :run)
                    (fn2-columns-sym (fn2-columns-col-name (cadr label) (caddr label)) "-BOUND"))))
      (append (and id (fn2-decl-get :statement (fn2-decl-row (list :square id) world))
                   `((fn2-square-append-evidence
                      ,id (list (fn2-arm-certificate-check ',(cadr label) *fn2-q1-a4-certified*
                                                           ',label *fn2-q1-a4-run*)))))
              (fn2-q1-evidence-arm-events (cdr labels) world)))))
(make-event
 (value (cons 'progn
              (append (fn2-q1-evidence-case-events (fn2-decl-rows :square (w state)))
                      (fn2-q1-evidence-arm-events *fn2-q1-catalogue* (w state))))))

(defun fn2-q1-evidence-exercised (labels tally)
  (declare (xargs :verify-guards nil))
  (if (atom labels) nil
    (append (and (assoc-equal (car labels) tally) (list (car labels)))
            (fn2-q1-evidence-exercised (cdr labels) tally))))
(value-triple
 (cw "Q1 EVIDENCE ~x0: cases exercised ~x1/~x2, arms certified ~x3; turns ~x4 transitions ~x5~%"
     (fn2-decl-get :location *fn2-q1-a4-run*)
     (len (fn2-q1-evidence-exercised *fn2-q1-catalogue* *fn2-q1-a4-cases*))
     (len *fn2-q1-catalogue*)
     (len (fn2-q1-evidence-exercised *fn2-q1-catalogue* *fn2-q1-a4-certified*))
     (fn2-decl-get :turns *fn2-q1-a4-run*) (fn2-decl-get :transitions *fn2-q1-a4-run*)))
