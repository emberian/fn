; Execute against the qualified parser-boundary-unit fixture. Raw mutation is
; a falsification control, not a logical theorem or a production attachment.
(in-package "ACL2")
(include-book "tests/parser-boundary-unit")
(set-guard-checking nil)
:q
(handler-case
 (let ((eof-original (symbol-function 'fn2-cw-post-eof))
       (after-original (symbol-function 'fn2-conn-after-code))
       (eof-count 0) (closing-count 0))
   (labels ((check (index)
              (let ((fixture (nth index *fn2-pb-fixtures*)))
                (fn2-pb-check fixture (fn2-pb-coalesced fixture)))))
     (assert (and (check 1) (check 3)))
     (unwind-protect
       (progn
         ; Reproduce the former blind spot: a peer EOF remains pending forever.
         (setf (symbol-function 'fn2-cw-post-eof)
               (lambda (op gen len core)
                 (declare (ignore op gen len)) (incf eof-count) core))
         (assert (not (check 1)))
         (assert (plusp eof-count))
         (setf (symbol-function 'fn2-cw-post-eof) eof-original)
         (assert (check 1))
         ; Actually change the served answer's continuation, allowing bytes
         ; after QUIT to be parsed. The independent wire oracle must reject it.
         (setf (symbol-function 'fn2-conn-after-code)
               (lambda (after)
                 (if (eq after :closing)
                     (progn (incf closing-count) *fn2-conn-after-command*)
                   (funcall after-original after))))
         (assert (not (check 3)))
         (assert (plusp closing-count)))
       (setf (symbol-function 'fn2-cw-post-eof) eof-original
             (symbol-function 'fn2-conn-after-code) after-original))
     (assert (and (check 1) (check 3)))
     (format t "PARSER-BOUNDARY-CONTROLS PASS eof-mutations=~d closing-mutations=~d~%"
             eof-count closing-count)))
 (error (condition)
   (format t "PARSER-BOUNDARY-CONTROLS ERROR ~a~%" condition)
   (sb-ext:exit :code 1)))
(sb-ext:exit :code 0)
