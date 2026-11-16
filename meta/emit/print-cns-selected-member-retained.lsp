; Diagnostic export in the sole retained admitted application world. Requires
; assembly-attach and translation-validation already loaded. Never includes a
; book, exits LP, or starts another world. PROGN! restores raw-mode on return.
(in-package "ACL2")
(progn!
 (set-raw-mode t)
 (load "meta/emit/print-world.lisp")
 (let ((*meta-w* (w *the-live-state*)) (*meta-errors* nil))
   (declare (special *meta-w* *meta-errors*))
   (unless (and (fboundp 'fn2-tv-function)
                (fboundp 'fn2-tv-attachment)
                (equal (fn2-tv-attachment 'fn2-cns-run-stub *meta-w*)
                       '(fn2-cns-run-stub . fn2-cns-run))
                (every (lambda (fn) (getpropc fn 'formals nil *meta-w*))
                       '(fn2-cns-run-stub fn2-cns-run fn2-cns-put-item fn2-cns-put-answer)))
     (error "Current attached CNS/translation-validation world is not available."))
   (meta-print-certificate "meta/emit/cns-selected-member.sexp"
                           '(fn2-cns-run-stub) 'fn2-cns nil nil)
   (when *meta-errors* (error "Canonical printer reported errors: ~s" *meta-errors*))
   (unless (eq *meta-w* (w *the-live-state*))
     (error "World changed during canonical diagnostic export."))))
(value-triple :cns-selected-member-returned-to-acl2)
