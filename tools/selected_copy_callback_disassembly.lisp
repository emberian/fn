;;; Actual supported installed callback components, including XEP/prologue.
;;; Measurement only; no frame, allocator, exception or GC theorem follows.
(in-package "ACL2")
(with-open-file
 (stream "/home/ember/fn-gates/incoming-guarded-startup/build/selected-copy-callback-disassembly.txt"
  :direction :output :if-exists :supersede)
 (format stream "~&SELECTED-COPY-POLICY ~s~%" sb-c::*policy*)
 (dolist (name '(create-fn-input-copy create-fn-page-read-pool
                fn-owner-incoming-copy-start fn-owner-incoming-copy-next
                fn-owner-incoming-copy-ack fn-owner-incoming-copy-stop
                fn-owner-incoming-mutation-allowedp))
  (let ((callback (fnn-fixed-raw-callback name)))
   (format stream "~&SELECTED-INSTALLED-COMPONENT ~s COMPILED ~s~%"
           name (compiled-function-p callback))
   (sb-disassem:disassemble-code-component callback :stream stream)))
 (dolist (name '(fnn-owner-incoming-copy-step fn-icc$c-open fn-icc$c-next
                fn-icc$c-ack fn-icc$c-close))
  (format stream "~&SELECTED-TRANSITIVE-COMPONENT ~s~%" name)
  (sb-disassem:disassemble-code-component (symbol-function name) :stream stream)))
