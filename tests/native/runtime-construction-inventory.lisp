;;; Run from repository root with SBCL --script. This executes the literal
;;; core defun bodies and real native shallow-size primitive. It is not a
;;; qualified image or an assertion that the complete boot recipe is present.
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun posp (x) (and (integerp x) (< 0 x)))
(defun fnn-core (name &rest args) (apply (symbol-function name) args))

; Only trusted checked-in test source is read, never protocol data. Remove
; ACL2's xargs declaration for this native execution of the identical bodies.
(with-open-file (input "books/runtime-construction-inventory.lisp")
  (loop for form = (read input nil :eof) until (eq form :eof)
        when (and (consp form) (eq (car form) 'defun)) do
          (eval (append (subseq form 0 3)
                        (remove-if (lambda (x) (and (consp x)
                                                    (eq (car x) 'declare)))
                                   (nthcdr 3 form))))))
(load "host/native/runtime-construction-inventory.lisp")

(defun expect-error (thunk)
  (assert (handler-case (progn (funcall thunk) nil) (error () t))))

(let* ((pool (make-array 10 :initial-element nil))
       (buffer (make-array 1 :initial-element nil))
       (backing (make-array 643 :element-type '(unsigned-byte 8)
                               :initial-element 0))
       (prototype (list :prototype))
       (final (list :final))
       (recipe (compile nil '(lambda () :test-recipe)))
       (inventory nil))
  (setf (svref buffer 0) backing)
  (setq inventory (fnn-runtime-construction-inventory-prepare
                   pool :test-image recipe
                   (vector pool buffer backing prototype backing) 80 64))
  (let* ((objects (fnn-runtime-construction-inventory-objects inventory))
         (sizes (fnn-runtime-construction-inventory-sizes inventory))
         (actual (loop for object across objects
                       sum (sb-ext:primitive-object-size object))))
    (assert (= (length objects) 7)) ; 4 distinct roots + observer and 2 arrays.
    (assert (eq (svref objects 0) inventory))
    (assert (eq (svref objects 1) objects))
    (assert (eq (svref objects 2) sizes))
    (assert (= (count backing objects :test #'eq) 1))
    (assert (= actual (fnn-runtime-construction-inventory-primary inventory)))
    (assert (= (+ (* 2 (+ actual 80)) 64)
               (fnn-runtime-construction-inventory-resident inventory)))
    (expect-error (lambda ()
                    (fnn-runtime-construction-inventory-replace
                     inventory prototype (vector 1 2))))
    (fnn-runtime-construction-inventory-replace inventory prototype final)
    (assert (find final objects :test #'eq))
    (assert (not (find prototype objects :test #'eq)))
    ; A changed actual backing must be detected before sealing.
    (let ((i (position backing objects :test #'eq)))
      (setf (svref objects i) (make-array 1024 :element-type '(unsigned-byte 8)))
      (expect-error (lambda () (fnn-runtime-construction-inventory-seal inventory)))
      (setf (svref objects i) backing))
    (fnn-runtime-construction-inventory-seal inventory)
    (assert (fnn-runtime-construction-inventory-sealed inventory))
    (expect-error (lambda () (fnn-runtime-construction-inventory-seal inventory)))
    (expect-error (lambda ()
                    (fnn-runtime-construction-inventory-replace inventory final
                                                               (list :late)))))
  (expect-error (lambda () (fnn-runtime-construction-inventory-prepare
                            pool :test-image recipe (vector nil) 0 0)))
  (expect-error (lambda () (fnn-runtime-construction-inventory-prepare
                            pool :test-image recipe (vector pool)
                            most-positive-fixnum 0))))
(format t "runtime-construction-inventory: native source checks passed~%")
