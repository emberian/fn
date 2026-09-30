;;; Runtime-only diagnostics of unchanged scalar source forms in the frozen
;;; attachment closure, plus the exact new allowance form copied separately.
;;; Whole current deflate-policy compilation differs.
(in-package "ACL2")
(with-open-file
 (stream "/home/ember/fn-gates/runtime-selected-attached-077b/build/selected-scale-disassembly.txt"
  :direction :output :if-exists :supersede)
 (dolist (name '(fn-zin-bomb-limit fn-pzd-budget fn-zin-stored-allowance))
  (unless (and (fboundp name)
               (compiled-function-p (symbol-function name))
               (eq (symbol-class name (w *the-live-state*))
                   :common-lisp-compliant))
   (error "Exact scalar compiled subject ~s is unavailable" name))
  (format stream "~&SELECTED-SCALE ~s~%" name)
  (sb-disassem:disassemble-code-component (symbol-function name)
                                        :stream stream)))
