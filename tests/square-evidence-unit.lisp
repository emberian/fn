(in-package "ACL2")
(include-book "../books/square-evidence")
(include-book "../books/owed-report")
(include-book "core-update-lowering-unit")
(defun fn2-evidence-wrong-abi (i value core)
 (declare (ignore i value core)) nil)

; The pilot uses the actual admitted source, generated core face, and sibling
; clobber mutant.  The compared result includes every child, not just the answer.
(defthm-owed fn2-evidence-product (i value core)
 (equal (fn2-update-child-core-face i value core) (fn2-update-source i value core))
 :schema :g1 :claim :compiler
 :sides (:concrete fn2-update-child-core-face :reference fn2-update-source)
 :teeth (fn2-update-runtime-witness))

(must-fail
 (defsquare-evidence fn2-evidence-product :positive t
  :negative (:kind :mutation :at fn2-update-child-core-face
             :replace fn2-update-mutant-core-face :bindings nil)))
(must-fail
 (defsquare-evidence fn2-evidence-product
  :positive ((i '0) (value '42))
  :negative (:kind :mutation :at fn2-update-child-core-face
             :replace fn2-update-mutant-core-face :bindings nil)))
(must-fail
 (defsquare-evidence fn2-evidence-product
  :positive ((i '0) (value '42) (core '(((37) 1) ((91) 1))))
  :negative (:kind :mutation :at fn2-update-source
             :replace fn2-update-mutant-core-face
             :bindings ((i '0) (value '42) (core '(((37) 1) ((91) 1)))))))
; An unchanged implementation is not a sensitivity control.
(must-fail
 (defsquare-evidence fn2-evidence-product
  :positive ((i '0) (value '42) (core '(((37) 1) ((91) 1))))
  :negative (:kind :mutation :at fn2-update-child-core-face
             :replace fn2-evidence-wrong-abi
             :bindings ((i '0) (value '42) (core '(((37) 1) ((91) 1)))))))
(must-fail
 (defsquare-evidence fn2-evidence-product
  :positive ((i '0) (value '42) (core '(((37) 1) ((91) 1))))
  :negative (:kind :mutation :at fn2-update-child-core-face
             :replace fn2-update-source
             :bindings ((i '0) (value '42) (core '(((37) 1) ((91) 1)))))))
; Both executions' actual guard instances are checked.
(must-fail
 (defsquare-evidence fn2-evidence-product
  :positive ((i '-1) (value '42) (core '(((37) 1) ((91) 1))))
  :negative (:kind :mutation :at fn2-update-child-core-face
             :replace fn2-update-mutant-core-face
             :bindings ((i '0) (value '42) (core '(((37) 1) ((91) 1)))))))
(defsquare-evidence fn2-evidence-product
 :positive ((i '0) (value '42) (core '(((37) 1) ((91) 1))))
 :negative (:kind :mutation :at fn2-update-child-core-face
            :replace fn2-update-mutant-core-face
            :bindings ((i '0) (value '42) (core '(((37) 1) ((91) 1))))))
(fn2-assert-square-evidence fn2-evidence-product)
(assert-event (equal (fn2-decl-get :proof
                       (fn2-decl-row '(:square fn2-evidence-product) (w state)))
                     '(:owed)))
; Evidence from another formula cannot become current merely by a table write.
(encapsulate ()
 (local
  (make-event
   (value (list 'table 'fn2-squares ''fn2-evidence-product
    (list 'quote
     (let* ((row (fn2-decl-row '(:square fn2-evidence-product) (w state)))
            (e (fn2-decl-get :evidence row)))
      (fn2-decl-set :evidence (fn2-decl-set :formula t e) row)))))))
 (local (must-fail (fn2-assert-square-evidence fn2-evidence-product))))
(encapsulate ()
 (local
  (make-event
   (value (list 'table 'fn2-squares ''fn2-evidence-product
    (list 'quote
     (let* ((row (fn2-decl-row '(:square fn2-evidence-product) (w state)))
            (e (fn2-decl-get :evidence row)))
      (fn2-decl-set :evidence (fn2-decl-set :functions nil e) row)))))))
 (local (must-fail (fn2-assert-square-evidence fn2-evidence-product))))
; Existing table guard binds an admitted theorem to this exact statement.
(must-fail
 (make-event
  (value (list 'table 'fn2-squares ''fn2-evidence-product
   (list 'quote
    (fn2-decl-set :proof '(:proved fn2-update-positive-witness)
      (fn2-decl-row '(:square fn2-evidence-product) (w state))))))))

(defun fn2-evidence-identity (x) (declare (xargs :guard t)) x)
(defun fn2-evidence-clamp (x) (declare (xargs :guard t)) (if (natp x) x 0))
(defun fn2-evidence-conditional-control ()
 (and (natp 3) (equal (fn2-evidence-clamp 3) (fn2-evidence-identity 3))
      (not (natp -1)) (not (equal (fn2-evidence-clamp -1) (fn2-evidence-identity -1)))))
(defthm-owed fn2-evidence-conditional (x)
 (implies (natp x) (equal (fn2-evidence-clamp x) (fn2-evidence-identity x)))
 :sides (:concrete fn2-evidence-clamp :reference fn2-evidence-identity)
 :teeth (fn2-evidence-conditional-control))
; An implication true only because its premise is false is not a witness.
(must-fail
 (defsquare-evidence fn2-evidence-conditional :positive ((x '-1))
  :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1)))))
; Removing a clause not in the statement, or not actually falsifying it, fails.
(must-fail
 (defsquare-evidence fn2-evidence-conditional :positive ((x '3))
  :negative (:kind :hypothesis-removal :remove (integerp x) :bindings ((x '-1)))))
(must-fail
 (defsquare-evidence fn2-evidence-conditional :positive ((x '3))
  :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '3)))))
(defsquare-evidence fn2-evidence-conditional :positive ((x '3))
 :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1))))
(fn2-assert-square-evidence fn2-evidence-conditional)
(fn2-assert-owed-teeth fn2-evidence-conditional)

; Independent review's redirect: the table guard binds :translated, but the
; author :formula is freely mutable.  Its altered H/C must never drive evidence.
(defthm-owed fn2-evidence-source-binding-probe (x)
 (implies (natp x) (equal (fn2-evidence-clamp x) (fn2-evidence-identity x)))
 :sides (:concrete fn2-evidence-clamp :reference fn2-evidence-identity)
 :teeth (fn2-evidence-conditional-control))
(make-event
 (value (list 'table 'fn2-squares ''fn2-evidence-source-binding-probe
  (list 'quote
   (fn2-decl-set :formula
    '(implies (integerp x)
              (equal (fn2-evidence-clamp x) (fn2-evidence-identity (+ 1 x))))
    (fn2-decl-row '(:square fn2-evidence-source-binding-probe) (w state)))))))
(must-fail
 (defsquare-evidence fn2-evidence-source-binding-probe :positive ((x '-1))
  :negative (:kind :hypothesis-removal :remove (integerp x) :bindings ((x '1/2)))))
; Genuine original witnesses still bind even if optional display text lies.
(defsquare-evidence fn2-evidence-source-binding-probe :positive ((x '3))
 :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1))))
(fn2-assert-square-evidence fn2-evidence-source-binding-probe)
(assert-event
 (equal (fn2-decl-get :formula
          (fn2-decl-get :evidence (fn2-decl-row '(:square fn2-evidence-source-binding-probe) (w state))))
        (fn2-decl-statement-body 'fn2-evidence-source-binding-probe$owed (w state))))
(assert-event
 (let ((row (fn2-decl-row '(:square fn2-evidence-source-binding-probe) (w state))))
  (and (equal (fn2-owed-claim-term row (w state))
              (fn2-decl-statement-body 'fn2-evidence-source-binding-probe$owed (w state)))
       (not (equal (fn2-owed-claim-term row (w state)) (fn2-decl-get :formula row))))))
; Canonical conjunction decomposition retains every actual antecedent clause.
(defthm-owed fn2-evidence-conjunction (x)
 (implies (and (integerp x) (<= 0 x))
          (equal (fn2-evidence-clamp x) (fn2-evidence-identity x)))
 :sides (:concrete fn2-evidence-clamp :reference fn2-evidence-identity)
 :teeth (fn2-evidence-conditional-control))
(must-fail
 (defsquare-evidence fn2-evidence-conjunction :positive ((x '3))
  :negative (:kind :hypothesis-removal :remove (integerp x) :bindings ((x '-1)))))
(defsquare-evidence fn2-evidence-conjunction :positive ((x '3))
 :negative (:kind :hypothesis-removal :remove (integerp x) :bindings ((x '1/2))))
(fn2-assert-square-evidence fn2-evidence-conjunction)

(defthm-owed fn2-evidence-placeholder (x) (equal x x)
 :teeth (fn2-evidence-conditional-control))
(must-fail
 (defsquare-evidence fn2-evidence-placeholder :positive ((x '3))
  :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1)))))
