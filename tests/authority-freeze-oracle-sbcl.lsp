; Common Lisp concrete evaluation only: not ACL2 admission/certification.
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defun member-equal (x xs) (member x xs :test #'equal))
(defun assoc-equal (x xs) (assoc x xs :test #'equal))
(defun len (xs) (length xs))
(defmacro assert-event (form) `(assert ,form))
(load "tests/authority-freeze-oracle.lisp")
(format t "Nine independent temporal controls passed (SBCL evaluation only).~%")
