; Execute actual shared generator functions; no ACL2 or proof process.
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(declaim (declaration xargs))
(defun len (x) (length x))
(defun member-eq (x xs) (member x xs))
(defun intern-in-package-of-symbol (name symbol) (intern name (symbol-package symbol)))
(defun fn2-decl-get (key xs) (getf xs key))
(defun load-columns-functions (path)
 (with-open-file (in path)
  (loop for form = (read in nil :eof) until (eq form :eof) do
   (case (car form)
    (defun (eval form))
    (mutual-recursion (mapc #'eval (cdr form)))))))
(defun fact-hints (fact) (getf (cdddr fact) :hints))
(defun formulas (facts) (mapcar (lambda (fact) (subseq fact 0 3)) facts))
(defparameter *outer-hints* '(("Goal" :use outer-fact)))
(defparameter *type-hints* '(("Goal" :use type-fact)))
(defparameter *wfp-hints* '(("Goal" :use wfp-fact)))
(defparameter *legacy-cases*
 '(((left 0) (right 2 :prefix "-R"))
   ((left nil :hints nil :invariant left-shape :suffix "-SHAPE"))
   ((left 1 :hints (("Goal" :use wfp-fact))) (right 3 :prefix "-R"))))

; The original source is passed by the Python runner, not reimplemented here.
(load-columns-functions (or (sb-ext:posix-getenv "FN_COLUMNS_BASELINE") "books/columns.lisp"))
(defparameter *legacy-output*
 (mapcar (lambda (carriers)
           (let ((specs (fn2-columns-carrier-specs carriers)))
            (list specs (fn2-columns-preservation-facts
                         'subject '(subject x left right) specs '(hypothesis) *outer-hints*))))
         *legacy-cases*))
(load-columns-functions "books/columns.lisp")
(loop for carriers in *legacy-cases* for old in *legacy-output* do
 (let ((specs (fn2-columns-carrier-specs carriers)))
  (let ((facts (fn2-columns-preservation-facts
                'subject '(subject x left right) specs '(hypothesis) *outer-hints*)))
   ; This repair intentionally changes absent WFP hint routing, not claims.
   (assert (equal (formulas facts) (formulas (cadr old))))
   (loop for carrier in carriers for index from 0 do
    (let* ((at (* 2 index)) (options (cddr carrier))
           (old-type (nth at (cadr old))) (old-wfp (nth (1+ at) (cadr old)))
           (old-spec (nth (1+ at) (car old))))
     (assert (equal (nth at facts) old-type))
     (if (member-eq :hints options)
         (progn (assert (equal (nth (1+ at) facts) old-wfp))
                (assert (equal (nth (1+ at) specs) old-spec)))
       (progn
        (assert (not (member-eq :hints (cdddr (nth (1+ at) specs)))))
        (assert (equal (nth (1+ at) facts)
                       (append old-wfp (list :hints *outer-hints*)))))))))))

(let* ((plain '((left 1 :prefix "-L") (right 2 :prefix "-R")))
       (carriers `((left 1 :prefix "-L" :type-hints ,*type-hints* :hints ,*wfp-hints*)
                   (right 2 :prefix "-R" :type-hints nil :hints ,*wfp-hints*)))
       (specs (fn2-columns-carrier-specs carriers))
       (facts (fn2-columns-preservation-facts
                'subject '(subject x left right) specs '(hypothesis) *outer-hints*))
       (plain-facts (fn2-columns-preservation-facts
                      'subject '(subject x left right) (fn2-columns-carrier-specs plain)
                      '(hypothesis) *outer-hints*)))
 (assert (equal (fact-hints (first facts)) *type-hints*))
 (assert (equal (fact-hints (second facts)) *wfp-hints*))
 ; Explicit NIL is an opt-out, distinct from absent TYPE fallback.
 (assert (null (fact-hints (third facts))))
 (assert (not (member-eq :hints (cdddr (third facts)))))
 (assert (equal (fact-hints (fourth facts)) *wfp-hints*))
 (assert (equal (fact-hints (first plain-facts)) *outer-hints*))
 (assert (equal (fact-hints (second plain-facts)) *outer-hints*))
 (assert (equal (fact-hints (fourth plain-facts)) *outer-hints*))
 ; Names, whole antecedents, output predicates and MV projections unchanged.
 (assert (equal (formulas facts) (formulas plain-facts))))
; Explicit WFP NIL must still suppress a nonempty common hint.
(let* ((specs (fn2-columns-carrier-specs '((left 0 :hints nil))))
       (facts (fn2-columns-preservation-facts 'subject '(subject left) specs
                '((full-input-hyp left)) *outer-hints*)))
 (assert (member-eq :hints (cdddr (second specs))))
 (assert (equal (fact-hints (first facts)) *outer-hints*))
 (assert (not (member-eq :hints (cdddr (second facts)))))
 (assert (equal (caddr (second facts))
                '(implies (and (full-input-hyp left)) (left-wfp (car (subject left)))))))
(format t "COLUMNS CARRIER HINT CONTROLS PASS~%")
