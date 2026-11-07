; The measure's recorder for core-form kinds (Fn2.Arms.Core): include the certified D3
; connection evidence (tests/conn-unit: fn2-conn through the assembled core at the adapter
; boundary) and the F6 consumer stack (books/cns, tests/fnct-client), wrap every arm, handler and
; sub-arm function of every kind, core form included (record-arms.lisp, *meta-record-core*), run
; conn-unit's fragmentation scenarios and sim-layer-e's end-to-end turn tests (fn2-ctl and
; fn2-cns through fn2-turn; their definitions are local to an encapsulate there, so they are read
; from the file and submitted here), writing build/lean-meta/core-record.sexp. Test-only I/O.
; Run from the worktree root after
;   tools/certify.sh tests/conn-unit.lisp books/cns.lisp tests/fnct-client.lisp books/owed-cursor.lisp books/assembly-attach.lisp
;   tools/acl2 --timeout 3600 < meta/emit/record-core.lsp
(in-package "ACL2")
(include-book "tests/conn-unit")
(include-book "books/owed-cursor")
(include-book "books/assembly-attach")
(include-book "books/cns")
(include-book "tests/fnct-client")
:q
(handler-case
    (progn
      (load "meta/emit/record-arms.lisp")
      (setq *meta-record-core* t)
      (ensure-directories-exist "build/lean-meta/")
      (meta-record-install "build/lean-meta/core-record.sexp")
      (format t "~&META CONN fragmentation ~s~%" (fn2-conn-test-fragmentation))
      (format t "~&META CONN served-safety ~s~%" (fn2-conn-test-served-safety))
      ;; sim-layer-e's first encapsulate: its local definitions, unwrapped, without the includes
      (let* ((forms (with-open-file (in "tests/sim-layer-e.lisp")
                      (let ((*package* (find-package "ACL2")))
                        (loop for f = (read in nil :eof) until (eq f :eof) collect f))))
             (enc (find-if (lambda (f) (and (consp f) (eq (car f) 'encapsulate)
                                            (search "FN2-SLE-TURN-E2E-WITNESS" (format nil "~s" f))))
                           forms))
             (inner (loop for f in (cddr enc)
                          for g = (if (and (consp f) (eq (car f) 'local)) (cadr f) f)
                          unless (and (consp g) (member (car g) '(include-book assert-event)))
                          collect g)))
        (multiple-value-bind (erp value state)
            (let ((*features* (adjoin :acl2-loop-only *features*)))
              (ld (append '((set-guard-checking nil)) inner) :ld-error-action :error))
          (declare (ignore value state))
          (assert (not erp))))
      (dolist (test '(fn2-sle-test-turn-append fn2-sle-test-turn-read-and-stop
                      fn2-sle-test-turn-wait-wake fn2-sle-test-turn-full-verbs))
        (format t "~&META CNS ~s ~s~%" test (funcall test)))
      (meta-record-finish)
      (format t "~&FN2-META-RECORD PASS~%")
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "FN2-META-RECORD FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
