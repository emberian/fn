; Source-executed generator controls: no ACL2, proof, or cache process.
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(declaim (declaration xargs))
(defun len (x) (length x))
(defun nfix (x) (if (and (integerp x) (<= 0 x)) x 0))
(defun posp (x) (and (integerp x) (< 0 x)))
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun zp (x) (<= (nfix x) 0))
(defun member-equal (x xs) (member x xs :test #'equal))
(defun member-eq (x xs) (member x xs))
(defun no-duplicatesp-eq (xs) (= (length xs) (length (remove-duplicates xs))))
(defun strip-cars (xs) (mapcar #'car xs))
(defun strip-cdrs (xs) (mapcar #'cdr xs))
(defun take (n xs) (subseq xs 0 n))
(defun intern-in-package-of-symbol (name symbol) (intern name (symbol-package symbol)))
(defconstant *fn2-none* 4294967295)
(defmacro er (severity context message &rest args)
  (declare (ignore severity context message))
  `(error "Generator refusal: ~S" (list ,@args)))
; The declaration registry is the boundary under test: retain its exact inputs.
(defun fn2-declare (&rest args) args)
(defun fn2-decl-get (key xs) (getf xs key))
(with-open-file (in "books/columns.lisp")
 (loop for form = (read in nil :eof) until (eq form :eof) do
  (case (car form)
   (defun (eval form))
   (mutual-recursion (mapc #'eval (cdr form))))))

(defun emit (cols extras &optional init)
 (fn2-columns-events 'fn2-p cols 8 extras init nil))
(defun refused (thunk expected)
 (let ((caught nil))
  (handler-case (funcall thunk)
   (error (e) (setf caught t) (assert (search expected (princ-to-string e)))))
  (assert caught)))

; Exact production collision family, using actual generated theorem events.
(dolist (column '((credit-nonce :u60) (credit-owner-kind :u8)
                  (credit-owner-slot :u32) (credit-owner-gen :u60)))
 (let* ((field (fn2-columns-col-name 'fn2-p (car column)))
        (extra `((,field :type (array (unsigned-byte 60) (0))
                        :initially 0 :resizable t :why "Control group storage."))))
  (refused (lambda () (emit (list column) extra))
           (symbol-name (fn2-columns-sym field "-RAW-NTH-NATP")))))
; A second namespace route: explicitly selected initializer aliases a reader.
(refused (lambda () (emit '((value :u8)) nil 'fn2-p-value)) "FN2-P-VALUE")
; Enum names are emitted too; distinct row fields can share an enum namespace.
(refused (lambda () (emit '((a (:enum shared (:x :y)))
                            (b (:enum shared (:x :z)))) nil)) "SHARED-CODE->KEYWORD")
; Wrapper traversal checks local definitions without scanning quoted terms.
(assert (eq (fn2-columns-event-list-conflict
 '((local (defthm a '(defun ignored)))
   (progn (defthm a '(defun changed))))) 'a))
; Redundant identical emitted definitions and disjoint local scopes are valid.
(assert (not (fn2-columns-event-list-conflict
 '((defconst *same* 2) (defconst *same* 2)))))
(assert (not (fn2-columns-event-list-conflict
 '((encapsulate () (local (defun shared-local (x) x)))
   (encapsulate () (local (defun shared-local (x) (cons x x))))))))
(assert (eq (fn2-columns-event-list-conflict
 '((encapsulate () (local (defun shared-local (x) x))
                    (local (defun shared-local (x) (cons x x))))))
 'shared-local))
(assert (eq (fn2-columns-event-list-conflict
 '((encapsulate () (defun exported (x) x))
   (encapsulate () (defun exported (x) (cons x x))))) 'exported))
; This was a valid unchecked-generator output, including repeated enum events.
(assert (emit '((a (:enum shared (:x :y)))
                (b (:enum shared (:x :y)))) nil))
; Valid output is exactly the previous registry invocation, not rewritten.
(let* ((cols '((credit-nonce :u60)))
       (extras '((fn2-p-credit-group-nonce :type (array (unsigned-byte 60) (0))
                   :initially 0 :resizable t :why "Control group storage.")))
       (checked (emit cols extras))
       (original (symbol-function 'fn2-columns-declare)))
 (unwind-protect
  (progn (setf (symbol-function 'fn2-columns-declare) #'fn2-declare)
         ; SBCL represents nested backquote commas as fresh internal objects.
         (assert (string= (prin1-to-string checked)
                          (prin1-to-string (emit cols extras)))))
  (setf (symbol-function 'fn2-columns-declare) original)))
(format t "COLUMNS NAME CONTROLS PASS~%")
