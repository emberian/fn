; Construct an immutable product with shared constant NIL suffixes. Values are
; evaluated once in order. The head is always new; only constant trailing NIL
; fields share storage. Never use this macro for a destructively modified list.
(in-package "ACL2")

(defun fn-iml-nil-tests (values)
  (declare (xargs :mode :program))
  (if (consp values)
      (cons (list 'not (car values)) (fn-iml-nil-tests (cdr values))) nil))

(defun fn-iml-cons-form (prefix tail)
  (declare (xargs :mode :program))
  (if (consp prefix)
      (list 'cons (car prefix) (fn-iml-cons-form (cdr prefix) tail)) tail))

(defun fn-iml-clauses (prefix suffix)
  (declare (xargs :mode :program))
  (if (consp suffix)
      (cons (list (cons 'and (fn-iml-nil-tests suffix))
                  (fn-iml-cons-form prefix (list 'quote (make-list-ac (len suffix) nil nil))))
            (fn-iml-clauses (append prefix (list (car suffix))) (cdr suffix)))
    (list (list t (cons 'list prefix)))))

(defun fn-iml-bindings (values index)
  (declare (xargs :mode :program))
  (if (consp values)
      (cons (list (intern-in-package-of-symbol
                   (concatenate 'string "FN-IML-ARG-"
                     (coerce (explode-nonnegative-integer index 10 nil) 'string))
                   'fn-list/immutable)
                  (car values))
            (fn-iml-bindings (cdr values) (1+ index))) nil))

(defmacro fn-list/immutable (&rest values)
  ; Parallel LET initializers see the outer environment, even if one happens
  ; to use a generated name. No user body appears in the generated scope.
  (let* ((bindings (fn-iml-bindings values 0)) (variables (strip-cars bindings)))
    (if (consp variables)
        (list 'let bindings
              (cons 'cond (fn-iml-clauses (list (car variables)) (cdr variables))))
      nil)))

; Compare a fixed product without constructing another product. Every operand
; is evaluated once, in order, including operands after a mismatching field.
; The final NULL check rejects both excess fields and improper tails.
(defun fn-iml-equal-form (product values)
  (declare (xargs :mode :program))
  (if (consp values)
      (list 'and (list 'consp product)
            (list 'equal (list 'car product) (car values))
            (fn-iml-equal-form (list 'cdr product) (cdr values)))
    (list 'null product)))

(defmacro fn-list/fields= (product &rest values)
  (let* ((bindings (fn-iml-bindings (cons product values) 0))
         (variables (strip-cars bindings)))
    (list 'let bindings
          (list 'mbe :logic (list 'equal (car variables) (cons 'list (cdr variables)))
                :exec (fn-iml-equal-form (car variables) (cdr variables))))))

(defthm fn-iml-equal-cons
  (equal (equal product (cons head tail))
         (and (consp product) (equal (car product) head)
              (equal (cdr product) tail)))
  :hints (("Goal" :cases ((consp product))
           :use (:instance car-cdr-elim (x product))
           :in-theory (union-theories '(car-cons cdr-cons)
                                     (theory 'minimal-theory)))))

(in-theory (disable fn-iml-equal-cons))
