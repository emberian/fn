(in-package "ACL2")
(include-book "../../books/definterface")
(include-book "must-fail-checked")
(include-book "../../books/octets-stobj")
(defstobj rg-test (rg-value :initially 0))
(defun rg-step (x rg-test)
 (declare (xargs :stobjs rg-test))
 (let ((rg-test (update-rg-value x rg-test))) (mv x rg-test)))
(defun rg-scalar (x) (declare (xargs :guard t)) x)
(defun rg-kind (x)
 (declare (xargs :guard (natp x))) x)
(defun rg-relation (x y)
 (declare (ignore y) (xargs :guard (equal x y))) x)
(defun rg-invariant (rg-test)
 (declare (xargs :stobjs rg-test :guard (natp (rg-value rg-test))))
 (rg-value rg-test))
(defun rg-field-guard (rg-test)
 (declare (xargs :stobjs rg-test :guard (rg-value rg-test)))
 (rg-value rg-test))
(defun rg-program (x) (declare (xargs :mode :program)) x)
(definterface create-rg-test :class :common-lisp-compliant
 :raw-guarded (0 () (rg-test)))
(definterface rg-step :class :common-lisp-compliant
 :raw-guarded (2 (nil rg-test) (nil rg-test)))
(definterface rg-scalar :class :common-lisp-compliant
 :raw-guarded (1 (nil) (nil)))
(must-fail-checked (definterface rg-kind :class :common-lisp-compliant :raw-guarded (1 (nil) (nil))))
(must-fail-checked (definterface rg-relation :class :common-lisp-compliant :raw-guarded (2 (nil nil) (nil))))
(must-fail-checked (definterface rg-invariant :class :common-lisp-compliant :raw-guarded (1 (rg-test) (nil))))
(must-fail-checked (definterface rg-field-guard :class :common-lisp-compliant :raw-guarded (1 (rg-test) (nil))))
(must-fail-checked (definterface rg-program :class :program :raw-guarded (1 (nil) (nil))))
(must-fail-checked (definterface rg-step :class :common-lisp-compliant :raw-guarded (1 (rg-test) (nil rg-test))))
(must-fail-checked (definterface rg-step :class :common-lisp-compliant :raw-guarded (2 (nil nil) (nil rg-test))))
(must-fail-checked (definterface rg-step :class :common-lisp-compliant :raw-guarded (2 (nil rg-test) (nil nil))))
(must-fail-checked (definterface rg-scalar :class :common-lisp-compliant :raw-guarded (1 (nil) (nil)) :raw-with (unrelated)))
(must-fail-checked (definterface rg-scalar :class :common-lisp-compliant :raw-guarded nil))
(must-fail-checked (definterface rg-scalar :class :common-lisp-compliant :raw-guarded (1 (nil) ("nil"))))
; Existing raw-with continues to reject a guard-t annotation that skips none.
(must-fail-checked (definterface rg-scalar :class :common-lisp-compliant :raw-with (unrelated)))

; Actual abstract creator role/EXEC metadata, followed by corrupted metadata.
(make-event
 (mv-let (problem target)
  (fn-di-raw-guarded-target 'create-fn-octets
   '(:class :common-lisp-compliant :raw-guarded (0 () (fn-octets))) (w state))
  (if (and (not problem) (eq target 'create-fn-octets$c))
      (value '(value-triple :actual-creator-exec))
    (value '(assert-event nil)))))
(make-event
 (let* ((w (w state))
        (spec '(:class :common-lisp-compliant :raw-guarded (0 () (fn-octets))))
        (malformed (putprop 'fn-octets 'absstobj-info :malformed w))
        (foreign (putprop 'fn-octets 'absstobj-info
                   '(fn-octets$c (create-fn-octets create-fn-octets$a create-rg-test)) w))
        (wrong-role (putprop 'fn-octets 'absstobj-info
                    '(fn-octets$c (create-fn-octets create-fn-octets$a fn-octets$c-fill)) w)))
  (mv-let (p1 t1) (fn-di-raw-guarded-target 'create-fn-octets spec malformed)
   (declare (ignore t1))
   (mv-let (p2 t2) (fn-di-raw-guarded-target 'create-fn-octets spec foreign)
    (declare (ignore t2))
    (mv-let (p3 t3) (fn-di-raw-guarded-target 'create-fn-octets spec wrong-role)
     (declare (ignore t3))
     (mv-let (p4 t4)
      (fn-di-raw-guarded-target 'create-fn-octets spec
        (putprop 'fn-octets 'stobj nil w))
      (declare (ignore t4))
      (value (if (and p1 p2 p3 p4)
                 '(value-triple :corrupted-creator-metadata-refused)
               '(assert-event nil)))))))))

; Absence must be refused even when an extracted abstract alias is callable.
(make-event
 (mv-let (problem target)
  (fn-di-raw-guarded-target 'create-fn-octets
   '(:class :common-lisp-compliant :raw-guarded (0 () (fn-octets)))
   (putprop 'fn-octets 'absstobj-info nil (w state)))
  (declare (ignore target))
  (value (if problem '(value-triple :missing-abstract-metadata-refused)
           '(assert-event nil)))))
