; Narrow envelope controls: exact theorem identity, translation, ownership,
; missing registry bindings, and evidence/proof separation.
(in-package "ACL2")
(include-book "defsquare")
(include-book "std/testing/must-fail" :dir :system)

(defun sq-test-inc (x) (+ 1 (nfix x)))
(defthm sq-test-positive-result (posp (sq-test-inc x)))
(defun sq-test-positive () (equal (sq-test-inc 0) 1))
(defun sq-test-negative () (not (equal (sq-test-inc 0) 0)))
(defun sq-test-binding (id formula proof)
  (list :id id :schema :invariant :vars '(x) :formula formula
        :proof proof :origin '(:fixture sq-test-inc) :boundary :function
        :teeth '(:positive sq-test-positive :negative sq-test-negative)))

(defsquare sq-test-envelope
  :template :fixture
  :cases-from '(:increment :new-event)
  :bindings (list (cons :increment
                       (sq-test-binding 'sq-test-row '(posp (sq-test-inc x))
                                        '(:proved sq-test-positive-result))))
  :contract (:operation sq-test-inc) :sides (:operation sq-test-inc))
(assert-event
 (equal (sq-get :unmatched
                (cdr (assoc-eq 'sq-test-envelope (table-alist 'sq-coverage (w state)))))
        '(:new-event)))
(assert-event
 (equal (strip-cars (table-alist 'sq-squares (w state))) '(sq-test-row)))
(assert-event
 (let ((row (cdr (assoc-eq 'sq-test-row (table-alist 'sq-squares (w state))))))
   (and (equal (sq-get :proof row) '(:proved sq-test-positive-result))
        (equal (sq-get :translated row)
               (getpropc 'sq-test-positive-result 'theorem nil (w state))))))

; Another true formula may not borrow this theorem's name.
(must-fail
 (defsquare sq-test-wrong-proof
   :template :fixture :cases-from '(:increment)
   :bindings (list (cons :increment
                        (sq-test-binding 'sq-test-wrong-row '(natp (sq-test-inc x))
                                         '(:proved sq-test-positive-result))))
   :contract (:operation sq-test-inc) :sides (:operation sq-test-inc)))
(must-fail
 (defsquare sq-test-unresolved
   :template :fixture :cases-from '(:increment)
   :bindings (list (cons :increment
                        (sq-test-binding 'sq-test-unresolved-row '(posp (sq-test-inc x))
                                         '(:owed))))
   :contract (:operation sq-test-no-such-function) :sides (:operation sq-test-inc)))
(must-fail
 (defsquare sq-test-signature
   :template :fixture :cases-from '(:increment)
   :bindings (list (cons :increment
                        (sq-test-binding 'sq-test-signature-row '(posp (sq-test-inc x x))
                                         '(:owed))))
   :contract (:operation sq-test-inc) :sides (:operation sq-test-inc)))
(must-fail
 (defsquare sq-test-duplicate
   :template :fixture :cases-from '(:increment :increment)
   :bindings (list (cons :increment
                        (sq-test-binding 'sq-test-duplicate-row '(posp (sq-test-inc x))
                                         '(:owed))))
   :contract (:operation sq-test-inc) :sides (:operation sq-test-inc)))
(must-fail
 (defsquare sq-test-envelope
   :template :fixture :cases-from '(:another)
   :bindings (list (cons :another
                        (sq-test-binding 'sq-test-reowned-row '(posp (sq-test-inc x))
                                         '(:owed))))
   :contract (:operation sq-test-inc) :sides (:operation sq-test-inc)))
(must-fail
 (defsquare sq-test-placeholder
   :template :fixture :cases-from '(:increment)
   :bindings (list (cons :increment
                        (sq-test-binding 'sq-test-placeholder-row 't '(:owed))))
   :contract (:operation sq-test-inc) :sides (:operation sq-test-inc)))

(sq-append-evidence sq-test-row
 ((:contract sq-test-envelope :revision "fixture" :profile :fixture
   :domain (:x 0) :horizon 1 :unit :call :location "defsquare-tests.lisp"
   :reached 1 :exercised 1 :verdict :pass)))
(assert-event
 (let ((row (cdr (assoc-eq 'sq-test-row (table-alist 'sq-squares (w state))))))
   (and (equal (sq-get :proof row) '(:proved sq-test-positive-result))
        (equal (len (sq-get :checks row)) 1))))
(defsquare sq-test-owed
  :template :fixture :cases-from '(:increment)
  :bindings (list (cons :increment
                       (sq-test-binding 'sq-test-owed-row '(posp (sq-test-inc x)) '(:owed))))
  :contract (:operation sq-test-inc) :sides (:operation sq-test-inc))
(sq-append-evidence sq-test-owed-row
 ((:contract sq-test-owed :revision "fixture" :profile :fixture
   :domain (:x 0) :horizon 1 :unit :call :location "defsquare-tests.lisp"
   :reached 1 :exercised 1 :verdict :pass)))
(assert-event
 (equal (sq-get :proof
                (cdr (assoc-eq 'sq-test-owed-row (table-alist 'sq-squares (w state)))))
        '(:owed)))
(must-fail
 (sq-append-evidence sq-test-owed-row
  ((:contract sq-test-owed :revision "fixture" :profile :fixture
    :domain (:x 0) :horizon 1 :unit :call :location "defsquare-tests.lisp"
    :reached 0 :exercised 0 :verdict :pass))))
