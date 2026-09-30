;;; Runtime observation only, loaded inside a protected raw-mode form after
;;; the two actual source subjects are admitted and guard verified.
(in-package "ACL2")
(defvar *fnn-srt-observed*)
(defun fnn-srt-observe (label thunk)
 (dotimes (i 1024) (setf *fnn-srt-observed* (funcall thunk)))
 (sb-ext:gc :full t)
 (let ((before (sb-ext:get-bytes-consed)))
  (dotimes (i 65536) (setf *fnn-srt-observed* (funcall thunk)))
  (format t "~&SELECTED-WRAPPER ~s calls=65536 allocated=~d result=~s~%"
   label (- (sb-ext:get-bytes-consed) before) *fnn-srt-observed*)))
(dolist (name '(fn-srt-status fn-lpc-begin fn-lpc-tick))
 (unless (eq (symbol-class name (w *the-live-state*)) :common-lisp-compliant)
  (error "Selected runtime fixture requires actual guard verification")))
(setf *fnn-srt-status* (symbol-function 'fn-srt-status)
      *fnn-srt-lpc-begin* (symbol-function 'fn-lpc-begin)
      *fnn-srt-lpc-tick* (symbol-function 'fn-lpc-tick))
(let ((arena (fn-arena-seal-list '(83 58 32 120 13 10 13 10)
                                (create-fn-arena)))
      (cursor (fn-lpc-begin 0 8 :pin)))
 (unless (fn-lpc-ready-p cursor arena)
  (error "Selected runtime fixture requires the actual entry invariant"))
 (fnn-srt-observe :begin (lambda () (fnn-selected-lpc-begin :ready 0 8 :pin)))
 (fnn-srt-observe :tick-one (lambda () (fnn-selected-lpc-tick :ready cursor 1 arena)))
 (fnn-srt-observe :invalid-carry (lambda () (fnn-selected-lpc-tick :refused cursor 1 arena)))
 (let ((*fnn-srt-lpc-tick* nil))
  (fnn-srt-observe :missing-callback
   (lambda () (fnn-selected-lpc-tick :ready cursor 1 arena)))))
(format t "~&SELECTED-RUNTIME ~a ~a~%" (lisp-implementation-version) (machine-type))
(with-open-file (stream "/home/ember/fn-gates/runtime-selected-attached-077b/build/selected-runtime-disassembly.txt"
 :direction :output :if-exists :supersede)
 (let ((*standard-output* stream))
  (dolist (name '(fn-srt-status fnn-selected-lpc-begin fnn-selected-lpc-tick
   fn-lpc-begin fn-lpc-header-begin fn-lpc-header-bad fn-lpc-tick fn-lpc-byte
   fn-lpc-at fn-lpc-put fn-lpc-span fn-lpc-header-byte fn-lpc-value-byte
   fn-lpc-close-fields fn-lpc-name-byte fn-lpc-name-step fn-lpc-name-key
   fn-lpc-split-byte fn-lpc-body-byte fn-lpc-verdict
   fn-arena-get fn-arena$x-get))
   (format t "~&SELECTED-FUNCTION ~s~%" name)
   (disassemble (symbol-function name)))))
