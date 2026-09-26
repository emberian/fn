; tools/image_anatomy/cut.lisp -- an EXPERIMENT (lane image-anatomy): cut
; ACL2's error-reporting path, through which every ACL2 function statically
; reaches the whole system (hard-error -> error-fms -> fmt -> wormhole ->
; set-w -> initialize-acl2 -> ld -> the prover).  Each replacement signals a
; Lisp error carrying the same context, message and arguments unformatted;
; fnn-call's serious-condition handler turns it into a fault, as it does
; ACL2's own abort.  A raw-Lisp obligation, not an ACL2 decision: the message
; text changes, the outcome class does not.  Never a release.
(in-package "ACL2")
(define-condition ia-acl2-error (error)
  ((ctx :initarg :ctx) (str :initarg :str) (alist :initarg :alist))
  (:report (lambda (c s)
             (let ((*print-length* 8) (*print-level* 4))
               (format s "ACL2 error in ~s: ~s ~s" (slot-value c 'ctx)
                       (slot-value c 'str) (slot-value c 'alist))))))
(defun hard-error (ctx str alist)
  (error 'ia-acl2-error :ctx ctx :str str :alist alist))
(defun illegal (ctx str alist)
  (error 'ia-acl2-error :ctx ctx :str str :alist alist))
(defun error-fms (hardp ctx summary str alist state)
  (declare (ignore hardp summary state))
  (error 'ia-acl2-error :ctx ctx :str str :alist alist))
(defun wormhole-er (fn args)
  (error 'ia-acl2-error :ctx fn :str "wormhole" :alist args))
