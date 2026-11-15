; Name the operationally selected dispatcher without asserting equality of
; a constrained logical stub and its attachment. The source seal is checked
; again by the final reference consumer after all attachments are installed.
(in-package "ACL2")
(include-book "assembly-attach")
(include-book "reference-effect-leaves")
(include-book "reference-selected-source")

; This source reifier intentionally supports the actual dispatcher's tail
; IF/CASE shape only. It is not a second general multiple-value compiler.
(mutual-recursion
 (defun fn2-ref-selected-tailp (term outs world)
  (declare (xargs :verify-guards nil :measure (acl2-count term)))
  (cond ((or (atom term) (eq (car term) 'quote)) nil)
        ((consp (car term))
         (and (fn2-ref-selected-scalars-p (cdr term) world)
              (fn2-ref-selected-tailp (caddar term) outs world)))
        ((eq (car term) 'if)
         (and (equal (len term) 4)
              (fn2-ref-selected-scalarp (cadr term) world)
              (fn2-ref-selected-tailp (caddr term) outs world)
              (fn2-ref-selected-tailp (cadddr term) outs world)))
        (t (and (equal (getpropc (car term) 'stobjs-out :missing world) outs)
                (pseudo-term-listp (cdr term))))))
 (defun fn2-ref-selected-scalarp (term world)
  (declare (xargs :verify-guards nil :measure (acl2-count term)))
  (cond ((or (atom term) (eq (car term) 'quote)) t)
        ((consp (car term))
         (and (fn2-ref-selected-scalars-p (cdr term) world)
              (fn2-ref-selected-scalarp (caddar term) world)))
        ((eq (car term) 'if)
         (and (equal (len term) 4)
              (fn2-ref-selected-scalars-p (cdr term) world)))
        (t (and (equal (getpropc (car term) 'stobjs-out :missing world) '(nil))
                (fn2-ref-selected-scalars-p (cdr term) world)))))
 (defun fn2-ref-selected-scalars-p (terms world)
  (declare (xargs :verify-guards nil :measure (acl2-count terms)))
  (if (atom terms) (null terms)
    (and (fn2-ref-selected-scalarp (car terms) world)
         (fn2-ref-selected-scalars-p (cdr terms) world)))))

(defun fn2-ref-selected-dispatcher-events (world)
  (declare (xargs :verify-guards nil))
  (let* ((source 'fn2-machine-run) (selected 'fn2-selected-machine-run)
         (body (getpropc source 'unnormalized-body nil world))
         (formals (getpropc source 'formals nil world))
         (guard (getpropc source 'guard t world))
         (stubs (fn2-selected-direct-stubs (fn2-tv-calls body) world)))
    (mv-let (problem pairs) (fn2-selected-pairs stubs world)
      (let* ((resolved (and body (fn2-selected-body body pairs)))
             (formula (and resolved
                        (fn2-reference-selected-body-formula source selected stubs world))))
        (if (not (and (not problem) formula
                      (equal formals '(id budget fn2-core))
                      (equal (getpropc source 'stobjs-in nil world) '(nil nil fn2-core))
                      (equal (getpropc source 'stobjs-out nil world) '(nil nil nil nil fn2-core))
                      (eq (symbol-class source world) :common-lisp-compliant)
                      (fn2-ref-selected-tailp resolved '(nil nil nil nil fn2-core) world)))
            (er hard 'fn2-ref-selected-dispatcher-events
                "Actual dispatcher source/ABI or selected tail form changed: ~x0." problem)
          `((defconst *fn2-selected-machine-run-stubs* ',stubs)
            (defun fn2-selected-machine-run ,formals
              (declare (xargs :stobjs fn2-core :verify-guards nil
                              :guard ,(fn2-lower-source-form guard)))
              ,(fn2-lower-source-form resolved))
            (defthm fn2-selected-machine-run-by-source
              ,formula :rule-classes nil
              :hints (("Goal" :in-theory
                       (union-theories '(fn2-selected-machine-run) (theory 'minimal-theory)))))
            (verify-guards fn2-selected-machine-run)
            (fn2-reference-selected-bind fn2-selected-machine-run-binding
              fn2-machine-run fn2-selected-machine-run ,stubs fn2-selected-machine-run-by-source)
            (fn2-reference-selected-check fn2-selected-machine-run-binding)))))))
(make-event (value (cons 'progn (fn2-ref-selected-dispatcher-events (w state)))))
