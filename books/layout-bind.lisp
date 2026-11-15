; Bind concrete field rows from the actual DEFLAYOUT declaration. This emits
; no parser/encoder and grants no source authority: the existing codec still
; decides field-kind validity and framing. No served logical record list exists.
(in-package "ACL2")
(include-book "layout")
(fn2-book-layer :b)
(defun fn2-layout-bind-ref-p (kind)
 (declare (xargs :verify-guards nil))
 (or (eq kind :digest) (and (consp kind) (member-eq (car kind) '(:octets :octets16 :octets32)))))
(defun fn2-layout-bind-arg (field suffix)
 (declare (xargs :verify-guards nil))
 (fn2-codec-symbol field (concatenate 'string "-" suffix)))
(defun fn2-layout-bind-formals (layout)
 (declare (xargs :verify-guards nil))
 (if (atom layout) nil
  (let ((field (caar layout)) (kind (cadar layout)))
   (append (cond ((and (consp kind) (eq (car kind) :zero)) nil)
                 ((fn2-layout-bind-ref-p kind)
                  (append (list (fn2-layout-bind-arg field "SLOT") (fn2-layout-bind-arg field "GEN") (fn2-layout-bind-arg field "OFF"))
                          (and (not (eq kind :digest)) (list (fn2-layout-bind-arg field "LEN")))))
                 (t (list (fn2-layout-bind-arg field "VALUE"))))
           (fn2-layout-bind-formals (cdr layout))))))
(defun fn2-layout-bind-guards (layout)
 (declare (xargs :verify-guards nil))
 (if (atom layout) nil
  (let ((field (caar layout)) (kind (cadar layout)))
   (append (cond ((and (consp kind) (eq (car kind) :zero)) nil)
                 ((fn2-layout-bind-ref-p kind)
                  (append (list `(unsigned-byte-p 32 ,(fn2-layout-bind-arg field "SLOT"))
                                `(unsigned-byte-p 60 ,(fn2-layout-bind-arg field "GEN"))
                                `(unsigned-byte-p 32 ,(fn2-layout-bind-arg field "OFF")))
                          (and (not (eq kind :digest)) (list `(unsigned-byte-p 32 ,(fn2-layout-bind-arg field "LEN"))))))
                 ; The concrete value column is u60. Wide wire values remain
                 ; explicit codec refusals, never truncated by this binder.
                 (t (list `(unsigned-byte-p 60 ,(fn2-layout-bind-arg field "VALUE")))))
           (fn2-layout-bind-guards (cdr layout))))))
(defun fn2-layout-bind-bindings (name layout)
 (declare (xargs :verify-guards nil))
 (if (atom layout) nil
  (let* ((field (caar layout)) (kind (cadar layout)) (at `(+ base ,(fn2-codec-field name field)))
         (binding
          (cond ((and (consp kind) (eq (car kind) :zero)) `(fn2-fields (fn2-fields-put ,at (value 0) (ref-len 0))))
                ((fn2-layout-bind-ref-p kind)
                 `(fn2-fields (fn2-fields-put ,at (value 1)
                   (ref-slot ,(fn2-layout-bind-arg field "SLOT")) (ref-gen ,(fn2-layout-bind-arg field "GEN"))
                   (ref-off ,(fn2-layout-bind-arg field "OFF"))
                   (ref-len ,(if (eq kind :digest) 32 (fn2-layout-bind-arg field "LEN"))))))
                (t `(fn2-fields (fn2-fields-set-value ,at ,(fn2-layout-bind-arg field "VALUE") fn2-fields))))))
   (cons binding (fn2-layout-bind-bindings name (cdr layout))))))
(defun fn2-layout-bind-events (fn name layout)
 (declare (xargs :verify-guards nil))
 (let* ((args (append '(base) (fn2-layout-bind-formals layout) '(fn2-fields)))
        (guards (append '((fn2-fields-wfp fn2-fields) (natp base))
                        (list `(<= (+ base ,(fn2-codec-constant name "-NUM-FIELDS")) (fn2-fields-rows fn2-fields)))
                        (fn2-layout-bind-guards layout))))
 `(progn
   (defun ,fn ,args
    (declare (xargs :stobjs fn2-fields :guard (and ,@guards)))
    (b* ,(fn2-layout-bind-bindings name layout) fn2-fields))
   (fn2-fields-preserves ,fn ,args :position nil :raw-rows t
    :hyps ((fn2-fieldsp fn2-fields) ,@guards)))))
(defmacro deflayout-binder (fn name)
 `(make-event
   (let* ((row (cdr (assoc-eq ',name (table-alist 'fn2-layouts (w state)))))
          (layout (cadr (member-eq :layout row))))
    (if (and (consp layout) (fn2-layoutp layout))
        (value (fn2-layout-bind-events ',fn ',name layout))
      (er soft 'deflayout-binder "No actual layout declaration for ~x0." ',name)))))
