;;; Saved-core diagnostic only. These exact routine addresses are literal
;;; targets in this world's FN-ZIN-SHIFT-IN disassembly, not portable ABI.
(in-package "ACL2")
(with-open-file (stream "/home/ember/fn-gates/runtime-selected-attached-077b/build/selected-fixnum-arithmetic-disassembly.txt"
 :direction :output :if-exists :supersede)
 (format stream "GENERIC-+ exact FN-ZIN-SHIFT-IN target, 112byte routine window~%")
 (sb-disassem:disassemble-memory #xB8000010F0 112 :stream stream)
 (format stream "GENERIC-* exact FN-ZIN-SHIFT-IN target, 192byte routine window~%")
 (sb-disassem:disassemble-memory #xB8000011D0 192 :stream stream))
