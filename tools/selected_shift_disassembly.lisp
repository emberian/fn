;;; Runtime-only positive ASH lowering review. Actual source-site factor
;;; counts 1/4 do not by themselves bound internal boxing or allocator frames.
(in-package "ACL2")
(with-open-file
 (stream "/home/ember/fn-gates/runtime-selected-attached-077b/build/selected-shift-disassembly.txt"
  :direction :output :if-exists :supersede)
 (dolist (entry '(("COMMON-LISP" "ASH")
                  ("SB-BIGNUM" "BIGNUM-ASHIFT-LEFT-FIXNUM")
                  ("SB-BIGNUM" "BIGNUM-ASHIFT-LEFT")))
  (let ((name (find-symbol (second entry) (first entry))))
   (unless (and name (fboundp name)
                (compiled-function-p (symbol-function name)))
    (error "Selected runtime shift implementation ~s is unavailable" entry))
   (format stream "~&SELECTED-SHIFT ~s ARGS ~s~%" name
    (sb-introspect:function-lambda-list (symbol-function name)))
   (sb-disassem:disassemble-code-component (symbol-function name)
                                         :stream stream))))
