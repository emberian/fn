;;; Additional runtime-only entry probe. Do not infer caller reachability,
;;; external-entry/frame bounds or reclamation from the warm heap counter.
(in-package "ACL2")
(let ((entry (symbol-function '%make-fnn-owner-admission-job)))
 (unless (compiled-function-p entry)
  (error "Exact frozen job constructor callback is not compiled"))
 (fnn-srt-observe :admission-job-twenty-callback
  (lambda () (funcall entry))))
(require 'sb-introspect)
(format t "~&DISASSEMBLE-API ~s~%"
 (sb-introspect:function-lambda-list #'disassemble))
(let ((entry (find-symbol "DISASSEMBLE-CODE-COMPONENT" "SB-DISASSEM")))
 (when (and entry (fboundp entry))
  (format t "~&CODE-DISASSEMBLE-API ~s~%"
   (sb-introspect:function-lambda-list (symbol-function entry)))))
