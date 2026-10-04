;;; tools/runtime_floor/host-shim.lisp -- the ACL2 runtime names that
;;; host/native's raw Lisp itself uses (not the exported core's), for the
;;; plain-SBCL node prototype (lane runtime-floor), from the compiler's
;;; undefined-name report on host/native: each is ACL2's raw behaviour on the
;;; live state, over the export's own objects.
(in-package "ACL2")

;; state: the live stobjs by name (ACL2's user-stobj-alist of the live state)
(defun user-stobj-alist (state) (declare (ignore state)) *rf-user-stobj-alist*)
;; state globals: ACL2's global symbols (global-symbol, exported)
(defun f-get-global (key state) (declare (ignore state)) (symbol-value (global-symbol key)))
(defun f-put-global (key value state)
  (declare (ignore state))
  (setf (symbol-value (global-symbol key)) value)
  *the-live-state*)
(defun f-boundp-global (key state) (declare (ignore state)) (boundp (global-symbol key)))
;; the only world read the host makes: an entry's STOBJS-IN (exported table)
(defun w (state) (declare (ignore state)) nil)
(defun stobjs-in (fn wrld)
  (declare (ignore wrld))
  (let ((hit (assoc fn *rf-stobjs-in*)))
    (if hit (cdr hit) (error 'rf-acl2-error :what (list :no-stobjs-in fn)))))
;; ACL2's defaults the host checks at start (fnn-main: guard-checking-on is t)
(setf (symbol-value (global-symbol 'guard-checking-on)) t)
