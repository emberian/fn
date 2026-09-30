; Exact existing defrecord accessor generator at original layout indexes.
; Original constructor/recognizer record events remain in their books.
(in-package "ACL2")
(include-book "acceptance-alloc")
(include-book "defrecord")
(make-event
 (cons 'progn
       (append (fn-defrecord-accessor-events '((fn-node-retention t)) 1 'fn-ag-car 'fn-ag-cdr)
               (fn-defrecord-accessor-events '((fn-retain-reserved t) (fn-retain-pins t)) 1 'fn-ag-car 'fn-ag-cdr)
               (fn-defrecord-accessor-events '((fn-retain-obligation-id t) (fn-retain-obligation-subject t) (fn-retain-obligation-kind t)) 0 'fn-ag-car 'fn-ag-cdr)
               (fn-defrecord-accessor-events '((fn-retain-obligation-charge t)) 4 'fn-ag-car 'fn-ag-cdr))))
