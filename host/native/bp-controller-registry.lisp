;;; Dormant registered BP dispatcher boundary. Caller holds extent mutex;
;;; native I/O/effects run after it releases the mutex. No interpreter fallback.
(in-package "ACL2")
(defvar *fnn-bp-controller-registry* nil)
(defvar *fnn-bp-controller-step-callback* nil)

(defun fnn-live-bp-controller-registry ()
  (or *fnn-bp-controller-registry*
      (setq *fnn-bp-controller-registry*
            (or (cdr (assoc 'fn-bp-controller-registry
                            (user-stobj-alist *the-live-state*)))
                (fnn-fault "the registered BP controller stobj is not in this image")))))

; The qualified startup installer must establish the exact guarded compiled
; callback/world and constructor/call baseline before publishing CALLBACK.
; There is deliberately no callback setter or initializer in this component.
(defmacro fnn-core-bp-controller-values (name &rest arguments)
  (unless (eq name 'fn-owner-bp-controller-step)
    (error "registered BP dispatcher requires its literal core step subject"))
  (unless (= (length arguments) 3)
    (error "registered BP dispatcher expects controller, event and fuel"))
  `(let ((callback *fnn-bp-controller-step-callback*))
     (unless callback
       (fnn-fault "registered BP guarded callback is not installed"))
     (funcall callback ,@arguments (fnn-live-bp-controller-registry))))
