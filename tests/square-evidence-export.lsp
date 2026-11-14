; Run after square-evidence-unit is certified:
; tools/acl2 --timeout 60 < tests/square-evidence-export.lsp
; Ordinary output is outside book events; no trust tag or raw evaluator.
(in-package "ACL2")
(set-ld-error-action '(:exit 2) state)
(set-cbd "tests/")
(include-book "square-evidence-unit" :uncertified-okp nil)
(include-book "std/io/read-file-bytes" :dir :system)
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(fn2-owed-export
 "../build/square-evidence-export.md"
 (list (cons 'fn2-evidence-source-binding-probe
             (fn2-decl-row '(:square fn2-evidence-source-binding-probe) (w state))))
 state)
(defun fn2-evidence-octet-characters (bytes)
 (declare (xargs :verify-guards nil))
 (if (atom bytes) nil
  (cons (code-char (car bytes)) (fn2-evidence-octet-characters (cdr bytes)))))
(make-event
 (mv-let (bytes state) (read-file-bytes "../build/square-evidence-export.md" state)
  (if (stringp bytes) (er soft 'square-evidence-export "~s0" bytes)
   (let ((text (coerce (fn2-evidence-octet-characters bytes) 'string)))
    (if (and (search "NATP" text) (not (search "INTEGERP" text)))
        (value '(value-triple :live-statement-exported))
      (er soft 'square-evidence-export "Export followed redirected author metadata."))))))
(value-triple (cw "SQUARE-EVIDENCE-EXPORT PASS~%"))
(good-bye)
