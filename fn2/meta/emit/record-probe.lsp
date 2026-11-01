; The measure's recorder for the probe scenario: include the certified probe book (reference,
; machine-arms-unit and fn2-meta-probe), wrap every child-form arm, handler and sub-arm function
; (record-arms.lisp), run probe-driver.lisp's scenario, write build/lean-meta/probe-record.sexp.
; Run from the worktree root after `fn2/tools/certify.sh meta/emit/meta-probe.lisp`:
;   tools/acl2 --timeout 3600 < fn2/meta/emit/record-probe.lsp
(in-package "ACL2")
(include-book "fn2/meta/emit/meta-probe")
(include-book "fn2/books/reference")
:q
(handler-case
    (progn
      (load "fn2/meta/emit/record-arms.lisp")
      (load "fn2/meta/emit/probe-driver.lisp")
      (ensure-directories-exist "build/lean-meta/")
      (meta-record-install "build/lean-meta/probe-record.sexp")
      (meta-probe-run)
      (meta-record-finish)
      (format t "~&FN2-META-RECORD PASS~%")
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "FN2-META-RECORD FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
