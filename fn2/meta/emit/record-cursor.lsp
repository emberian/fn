; The measure's recorder for the query cursor (fn2/books/cursor.lisp, D6 1/n): include the
; certified cursor-unit book and run its served scenarios (the D6 transcript whole and chunked
; 7/3/1, the pinned view served, the seeded store, the range cost, the pinned reference) with
; every child-form arm, handler and sub-arm function wrapped by record-arms.lisp, writing
; build/lean-meta/cursor-record.sexp. Test-only I/O.
; Run from the worktree root after `fn2/tools/certify.sh tests/cursor-unit.lisp`:
;   tools/acl2 --timeout 3600 < fn2/meta/emit/record-cursor.lsp
(in-package "ACL2")
(include-book "fn2/tests/cursor-unit")
:q
(handler-case
    (progn
      (load "fn2/meta/emit/record-arms.lisp")
      (ensure-directories-exist "build/lean-meta/")
      (meta-record-install "build/lean-meta/cursor-record.sexp")
      (dolist (test '((fn2-cursor-test-served nil) (fn2-cursor-test-served (7 3 1))
                      (fn2-cursor-test-pinned-served) (fn2-cursor-test-seeded)
                      (fn2-cursor-test-range-cost) (fn2-cursor-test-pinned)))
        (format t "~&META CURSOR ~s ~s~%" test
                (apply (car test) (mapcar (lambda (a) a) (cdr test)))))
      (meta-record-finish)
      (format t "~&FN2-META-RECORD PASS~%")
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "FN2-META-RECORD FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
