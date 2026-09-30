;;; Per-function diagnostics in exact original saved-core callback world.
(in-package "ACL2")
(with-open-file
 (stream "/home/ember/fn-gates/incoming-guarded-startup/build/selected-codec-field-disassembly.txt"
  :direction :output :if-exists :supersede)
 (let ((*standard-output* stream))
  (format t "~&SELECTED-CODEC-POLICY ~s~%" sb-c::*policy*)
  (dolist (text '("FN-ZIN-FLD$INLINE" "FN-ZIN-SET$INLINE"
                 "FN-ZIN-TGET$INLINE" "FN-OCTETS$C-GET" "FN-ZIN-REGSI" "UPDATE-FN-ZIN-REGSI"))
   (let ((name (find-symbol text "ACL2")))
    (format t "~&SELECTED-CODEC-SYMBOL ~s COMPILED ~s CLASS ~s~%"
     name (and name (fboundp name) (compiled-function-p (symbol-function name)))
     (and name (symbol-class name (w *the-live-state*))))
    (when (and name (fboundp name) (compiled-function-p (symbol-function name)))
     (disassemble (symbol-function name)))))
  (format t "~&SELECTED-ACTUAL-NATIVE-COPY-CALLER~%")
  (disassemble (symbol-function 'fnn-owner-incoming-copy-step))))
