(in-package "ACL2")
(include-book "../books/columns")
(include-book "std/testing/must-fail" :dir :system)

; The production-shaped collision is refused by the generator before emitting
; a defstobj or trying either of the incompatible raw-NTH facts.
(must-fail
 (defcolumns fn2-name-control ((credit-nonce :u60)) :rows-bound 8
  :extra-fields
  ((fn2-name-control-credit-nonce
    :type (array (unsigned-byte 60) (0)) :initially 0 :resizable t
    :why "Control-only group storage.")))
 :expected :hard :with-output-off nil :check-expansion t)
(must-fail
 (defcolumns fn2-name-control-init ((value :u8)) :rows-bound 8
  :init-name fn2-name-control-init-value)
 :expected :hard :with-output-off nil :check-expansion t)

(defcolumns fn2-name-control-valid ((credit-nonce :u60)) :rows-bound 8
 :extra-fields
 ((fn2-name-control-valid-credit-group-nonce
   :type (array (unsigned-byte 60) (0)) :initially 0 :resizable t
   :why "Control-only group storage with a distinct emitted namespace.")))
(assert-event (fn2-decl-row '(:columns fn2-name-control-valid) (w state)))

(assert-event
 (equal (fn2-columns-event-list-names
          '((local (defthm a '(defun ignored)))
            (encapsulate () (progn (defun b (x) x)))
            (in-theory (disable a))))
        '(a b)))
; A declaration with distinct emitted names is handed to the same registry
; without any modification of its payload, requirements, or event forms.
(assert-event
 (let ((id '(:columns fn2-name-control-valid))
       (payload '(:columns ((value :u8))))
       (events '((defun fn2-name-control-valid-value (x) x))))
  (equal (fn2-columns-declare id payload nil events)
         (fn2-declare id payload nil events))))
