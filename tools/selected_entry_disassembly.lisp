;;; Complete code components, including entry/prologue code omitted by a
;;; single internal function disassembly. Runtime-only inspection.
(in-package "ACL2")
(with-open-file
 (stream "/home/ember/fn-gates/runtime-selected-attached-077b/build/runtime-constructor/entry-disassembly.txt"
  :direction :output :if-exists :supersede)
 (dolist (name '(create-fn-page-read-pool create-fn-octets$c
                %make-fnn-owner-admission-job
                fnn-selected-lpc-begin fnn-selected-lpc-tick
                fn-lpc-begin fn-lpc-tick))
  (format stream "~&SELECTED-ENTRY-COMPONENT ~s~%" name)
  (sb-disassem:disassemble-code-component (symbol-function name)
                                        :stream stream)))
