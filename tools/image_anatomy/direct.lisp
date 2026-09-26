; tools/image_anatomy/direct.lisp -- an EXPERIMENT for the *1* question (lane
; image-anatomy): the host's fnn-call applies the raw (compiled) function
; instead of its executable counterpart, so no guard is checked and no world
; is read at the boundary.  Timing only; never a release.
(in-package "ACL2")
(defun fnn-counterpart (name)
  (let ((symbol (find-symbol (symbol-name name) "ACL2")))
    (unless (and symbol (fboundp symbol) (not (macro-function symbol)))
      (fnn-fault "ACL2 raw function missing: ~a" name))
    symbol))
