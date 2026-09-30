;;; Raw, measurement-only actual generated constructor inspection.
;;; Load only after the exact current pool and congruent RX declarations.
(in-package "ACL2")
(format t "~&~s~%" (fn-runtime-constructor-inspection))
(fnn-srt-observe :pool-three
 (lambda () (create-fn-page-read-pool)))
(fnn-srt-observe :rx-foundation
 (lambda () (create-fn-octets$c)))
(fnn-srt-observe :rx-congruent
 (lambda () (create-fn-octets-rx)))
(with-open-file
 (stream "/home/ember/fn-gates/runtime-selected-attached-077b/build/runtime-constructor/constructor-disassembly.txt"
  :direction :output :if-exists :supersede)
 (let ((*standard-output* stream))
  (dolist (name '(create-fn-page-read-pool create-fn-octets$c))
   (format t "~&SELECTED-CONSTRUCTOR ~s~%" name)
   (disassemble (symbol-function name)))
  (format t "~&SELECTED-CONSTRUCTOR RX-CONGRUENT-CALLER~%")
  (disassemble (compile nil '(lambda () (create-fn-octets-rx))))))
