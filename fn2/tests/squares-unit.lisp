; defsquare controls (ported from E2's defsquare-tests, onto fn2-squares):
; exact theorem identity, translation, ownership, missing bindings, role
; occurrence, evidence/proof separation. Every fixture is local: none of
; these rows reaches the owed export.
(in-package "ACL2")
(include-book "../books/squares")
(include-book "std/testing/must-fail" :dir :system)

(local
 (encapsulate ()
  (defun fn2-sqt-inc (x) (declare (xargs :guard t)) (+ 1 (nfix x)))
  (defun fn2-sqt-dec (x) (declare (xargs :guard t)) (nfix (- (nfix x) 1)))
  (defthm fn2-sqt-positive-result (posp (fn2-sqt-inc x)))
  (defun fn2-sqt-positive () (equal (fn2-sqt-inc 0) 1))
  (defun fn2-sqt-negative () (not (equal (fn2-sqt-inc 0) 0)))
  (defun fn2-sqt-binding (id formula proof)
    (list :id id :schema :invariant :vars '(x) :formula formula
          :proof proof :origin '(:fixture fn2-sqt-inc) :boundary :function
          :source '(:fixture fn2-sqt) :doc "Fixture row."
          :teeth '(:positive fn2-sqt-positive :negative fn2-sqt-negative)))

  ; Positive control: one bound case, one unmatched case reported by name,
  ; one requirement row with no statement, one unresolved dependency.
  (defsquare fn2-sqt-envelope
    :template :fixture
    :cases-from '(:increment :new-event)
    :bindings (list (cons :increment
                          (append (fn2-sqt-binding 'fn2-sqt-row '(posp (fn2-sqt-inc x))
                                                   '(:proved fn2-sqt-positive-result))
                                  '(:depends (fn2-sqt-need)))))
    :requirements ((fn2-sqt-need :schema :invariant :doc "Named, not stated."))
    :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
  (assert-event
   (equal (fn2-square-coverage 'fn2-sqt-envelope (w state))
          '(:required 2 :bound 1 :unmatched (:new-event) :unresolved-depends (fn2-sqt-need))))
  (assert-event
   (let ((row (fn2-decl-row '(:square fn2-sqt-row) (w state))))
     (and (equal (fn2-decl-get :proof row) '(:proved fn2-sqt-positive-result))
          (equal (fn2-decl-get :owner row) '(:correspondence fn2-sqt-envelope))
          (equal (fn2-decl-get :case row) :increment)
          (equal (fn2-decl-get :translated row)
                 (getpropc 'fn2-sqt-positive-result 'theorem nil (w state))))))
  (assert-event
   (let ((row (fn2-decl-row '(:square fn2-sqt-need) (w state))))
     (and row (not (fn2-decl-get :statement row)))))

  ; Another true formula may not borrow this theorem's name.
  (must-fail
   (defsquare fn2-sqt-wrong-proof
     :template :fixture :cases-from '(:increment)
     :bindings (list (cons :increment
                           (fn2-sqt-binding 'fn2-sqt-wrong-row '(natp (fn2-sqt-inc x))
                                            '(:proved fn2-sqt-positive-result))))
     :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  (must-fail
   (defsquare fn2-sqt-unresolved
     :template :fixture :cases-from '(:increment)
     :bindings (list (cons :increment
                           (fn2-sqt-binding 'fn2-sqt-unresolved-row '(posp (fn2-sqt-inc x)) '(:owed))))
     :contract (:operation fn2-sqt-no-such-function) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  (must-fail
   (defsquare fn2-sqt-signature
     :template :fixture :cases-from '(:increment)
     :bindings (list (cons :increment
                           (fn2-sqt-binding 'fn2-sqt-signature-row '(posp (fn2-sqt-inc x x)) '(:owed))))
     :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  (must-fail
   (defsquare fn2-sqt-duplicate
     :template :fixture :cases-from '(:increment :increment)
     :bindings (list (cons :increment
                           (fn2-sqt-binding 'fn2-sqt-duplicate-row '(posp (fn2-sqt-inc x)) '(:owed))))
     :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  (must-fail
   (defsquare fn2-sqt-envelope
     :template :fixture :cases-from '(:another)
     :bindings (list (cons :another
                           (fn2-sqt-binding 'fn2-sqt-reowned-row '(posp (fn2-sqt-inc x)) '(:owed))))
     :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  (must-fail
   (defsquare fn2-sqt-placeholder
     :template :fixture :cases-from '(:increment)
     :bindings (list (cons :increment
                           (fn2-sqt-binding 'fn2-sqt-placeholder-row 't '(:owed))))
     :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  (must-fail
   (defsquare fn2-sqt-trivial
     :template :fixture :cases-from '(:increment)
     :bindings (list (cons :increment
                           (fn2-sqt-binding 'fn2-sqt-trivial-row '(equal x x) '(:owed))))
     :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  (must-fail
   (defsquare fn2-sqt-extra
     :template :fixture :cases-from '(:increment)
     :bindings (list (cons :uncatalogued
                           (fn2-sqt-binding 'fn2-sqt-extra-row '(posp (fn2-sqt-inc x)) '(:owed))))
     :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)

  ; Role divergence (ruling 3, E2's control): the statement calls inc, the
  ; declaration names dec as the contract role. Refused unless listed exactly.
  (must-fail
   (defsquare fn2-sqt-role-divergence
     :template :fixture :cases-from '(:increment)
     :bindings (list (cons :increment
                           (fn2-sqt-binding 'fn2-sqt-divergent-row '(posp (fn2-sqt-inc x)) '(:owed))))
     :contract (:operation fn2-sqt-dec) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  ; A redundant exception (a role that does occur) is refused too.
  (must-fail
   (defsquare fn2-sqt-redundant-exception
     :template :fixture :cases-from '(:increment)
     :bindings (list (cons :increment
                           (append (fn2-sqt-binding 'fn2-sqt-redundant-row '(posp (fn2-sqt-inc x)) '(:owed))
                                   '(:unused-roles ((:sides :operation))))))
     :contract (:operation fn2-sqt-inc) :sides (:operation fn2-sqt-inc))
   :with-output-off nil)
  ; The exact exception admits the divergent declaration, and is recorded.
  (defsquare fn2-sqt-role-excepted
    :template :fixture :cases-from '(:increment)
    :bindings (list (cons :increment
                          (append (fn2-sqt-binding 'fn2-sqt-excepted-row '(posp (fn2-sqt-inc x)) '(:owed))
                                  '(:unused-roles ((:contract :operation))))))
    :contract (:operation fn2-sqt-dec) :sides (:operation fn2-sqt-inc))
  (assert-event
   (equal (fn2-decl-get :unused-roles (fn2-decl-row '(:square fn2-sqt-excepted-row) (w state)))
          '((:contract :operation))))
  (assert-event (not (fn2-decl-row '(:correspondence fn2-sqt-role-divergence) (w state))))
  (assert-event (not (fn2-decl-row '(:square fn2-sqt-divergent-row) (w state))))

  ; Evidence appends replace :checks only; a checked owed row stays owed.
  (defconst *fn2-sqt-check*
    '(:contract fn2-sqt-envelope :revision "fixture" :profile :fixture
      :domain (:x 0) :horizon 1 :unit :call :reached 1 :exercised 1
      :verdict :pass :location "fn2/tests/squares-unit.lisp"))
  (fn2-square-append-evidence fn2-sqt-excepted-row (list *fn2-sqt-check*))
  (fn2-square-append-evidence fn2-sqt-row (list *fn2-sqt-check*))
  (must-fail
   (fn2-square-append-evidence fn2-sqt-row
    '((:contract fn2-sqt-envelope :revision "fixture" :profile :fixture
      :domain (:x 0) :horizon 1 :unit :call :reached 0 :exercised 1
      :verdict :pass :location "fn2/tests/squares-unit.lisp")))
   :with-output-off nil)
  (must-fail (fn2-square-append-evidence fn2-sqt-need (list *fn2-sqt-check*))
   :with-output-off nil)
  (assert-event
   (let ((row (fn2-decl-row '(:square fn2-sqt-excepted-row) (w state))))
     (and (equal (fn2-decl-get :proof row) '(:owed))
          (equal (len (fn2-decl-get :checks row)) 1))))))
(value-triple (cw "SQUARES UNIT: coverage, proof identity, role occurrence, evidence PASS~%"))
