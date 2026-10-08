; Teeth for tools/owner_carrier/writers.lisp (lane carrier2): one synthetic
; function per writer route, a reader and an unrelated put that must stay
; clear, a cycle and an attachment.  Load after world.lisp and writers.lisp.
(in-package "ACL2")
(logic)
(defun ocwt-direct (state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner 1 state))
(defun ocwt-other (state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'ocwt-unrelated 1 state))
(defun ocwt-reader (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner state) (f-get-global 'fn-owner state) nil))
(defun ocwt-caller (state)
  (declare (xargs :stobjs state :guard t))
  (ocwt-direct state))
(encapsulate (((ocwt-hook state) => state :formals (state) :guard t))
  (local (defun ocwt-hook (state) (declare (xargs :stobjs state)) state)))
(defun ocwt-uses-hook (state)
  (declare (xargs :stobjs state :guard t))
  (ocwt-hook state))
(defattach ocwt-hook ocwt-direct)
(program)
(set-state-ok t)
(defun ocwt-unbind (state) (makunbound-global 'fn-owner-retain-carry state))
; A non-literal key is refused by translate ("The first arg of put-global
; must be a quoted symbol"), so route (1)'s non-literal arm has no ACL2
; witness; it stays in the scanner as a guard against a ttag'd translation.
(defun ocwt-eval (state) (trans-eval '(f-put-global 'fn-owner 1 state) 'ocwt state nil))
(mutual-recursion
 (defun ocwt-a (n state) (if (zp n) (ocwt-direct state) (ocwt-b (1- n) state)))
 (defun ocwt-b (n state) (ocwt-a n state)))
(defun ocwt-c (n state) (ocwt-b n state))

(defconst *ocwt-expect*
  '((ocwt-direct . :writer) (ocwt-other . :clear) (ocwt-reader . :clear)
    (ocwt-caller . :writer) (ocwt-uses-hook . :writer) (ocwt-unbind . :writer)
    (ocwt-eval . :writer) (ocwt-c . :writer)))
(defun ocwt-verdicts (rows)
  (if (endp rows) nil
    (cons (cons (car (car rows)) (cadr (car rows))) (ocwt-verdicts (cdr rows)))))
(make-event
 (let ((got (ocwt-verdicts (fn-ocw-writer-census (strip-cars *ocwt-expect*) state))))
   (if (equal got *ocwt-expect*)
       (value '(value-triple :ocwt-ok))
     (er soft 'ocwt "writer census teeth: got ~x0" got))))
