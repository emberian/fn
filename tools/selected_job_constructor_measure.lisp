;;; Raw diagnostic for the frozen actual native job20 declaration. Loading
;;; this exact form does not activate its source-demand-blocked caller.
(in-package "ACL2")
(when (fboundp '%make-fnn-owner-admission-job)
 (error "Refuse a previously loaded admission-job constructor"))
(load "/home/ember/fn-gates/runtime-selected-attached-077b/build/runtime-constructor/fnn-owner-admission-job.lisp")
(unless (compiled-function-p (symbol-function '%make-fnn-owner-admission-job))
 (error "Frozen actual admission-job constructor is not compiled"))
(fnn-srt-observe :admission-job-twenty
 (lambda () (%make-fnn-owner-admission-job)))
(with-open-file
 (stream "/home/ember/fn-gates/runtime-selected-attached-077b/build/runtime-constructor/job-disassembly.txt"
  :direction :output :if-exists :supersede)
 (let ((*standard-output* stream))
  (disassemble (symbol-function '%make-fnn-owner-admission-job))))
