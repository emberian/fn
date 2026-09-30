;;; Per-function runtime diagnostic: normalization and unchanged shift-in.
(in-package "ACL2")
(with-open-file
 (stream "/home/ember/fn-gates/runtime-selected-attached-077b/build/selected-normalization-disassembly.txt"
  :direction :output :if-exists :supersede)
 (let ((*standard-output* stream))
  (dolist (entry '(("SB-BIGNUM" "%NORMALIZE-BIGNUM")
                  ("SB-BIGNUM" "%NORMALIZE-BIGNUM-BUFFER")
                  ("SB-BIGNUM" "BIGNUM-ASHIFT-LEFT")
                  ("ACL2" "FN-ZIN-SHIFT-IN")))
   (let ((name (find-symbol (second entry) (first entry))))
    (unless (and name (fboundp name)
                 (compiled-function-p (symbol-function name)))
     (error "Actual compiled normalization subject unavailable"))
    (format t "~&SELECTED-NORMALIZATION ~s~%" name)
    (disassemble (symbol-function name))))))
