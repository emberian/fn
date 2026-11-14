(in-package "ACL2")
(include-book "../books/square-evidence")
(include-book "core-update-lowering-unit")

; The pilot uses the actual admitted source, generated core face, and sibling
; clobber mutant.  The compared result includes every child, not just the answer.
(defthm-owed fn2-evidence-product (i value core)
 (equal (fn2-update-child-core-face i value core) (fn2-update-source i value core))
 :schema :g1 :claim :compiler
 :sides (:concrete fn2-update-child-core-face :reference fn2-update-source)
 :teeth (fn2-evidence-product$bound-positive fn2-evidence-product$bound-negative))

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
(defsquare-evidence fn2-evidence-product
 :positive ((i '0) (value '42) (core '(((37) 1) ((91) 1))))
 :negative (:kind :mutation :at fn2-update-child-core-face
            :replace fn2-update-mutant-core-face
            :bindings ((i '0) (value '42) (core '(((37) 1) ((91) 1))))))
(fn2-assert-square-evidence fn2-evidence-product)
(fn2-assert-owed-teeth fn2-evidence-product)

(defun fn2-evidence-identity (x) (declare (xargs :guard t)) x)
(defun fn2-evidence-clamp (x) (declare (xargs :guard t)) (if (natp x) x 0))
(defthm-owed fn2-evidence-conditional (x)
 (implies (natp x) (equal (fn2-evidence-clamp x) (fn2-evidence-identity x)))
 :sides (:concrete fn2-evidence-clamp :reference fn2-evidence-identity)
 :teeth (fn2-evidence-conditional$bound-positive fn2-evidence-conditional$bound-negative))
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

(defthm-owed fn2-evidence-placeholder (x) (equal x x)
 :teeth (fn2-evidence-placeholder$bound-positive fn2-evidence-placeholder$bound-negative))
(must-fail
 (defsquare-evidence fn2-evidence-placeholder :positive ((x '3))
  :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1)))))
