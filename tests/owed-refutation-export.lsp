; Run after owed-refutation-unit is certified:
; tools/acl2 --timeout 60 < tests/owed-refutation-export.lsp
; Ordinary output is outside book events; no trust tag or raw evaluator.
(in-package "ACL2")
(set-ld-error-action '(:exit 2) state)
(set-cbd "tests/")
(include-book "owed-refutation-unit" :uncertified-okp nil)
(include-book "std/io/read-file-bytes" :dir :system)
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(fn2-owed-export
 "../build/owed-refutation-export.md"
 (list (cons 'fn2-refutation-original
             (fn2-decl-row '(:square fn2-refutation-original) (w state))))
 state)
(defun fn2-refutation-octet-characters (bytes)
 (declare (xargs :verify-guards nil))
 (if (atom bytes) nil
  (cons (code-char (car bytes)) (fn2-refutation-octet-characters (cdr bytes)))))
(make-event
 (mv-let (bytes state) (read-file-bytes "../build/owed-refutation-export.md" state)
  (if (stringp bytes) (er soft 'owed-refutation-export "~s0" bytes)
   (let ((text (coerce (fn2-refutation-octet-characters bytes) 'string)))
    (if (and (search "| `FN2-REFUTATION-ORIGINAL` | :REFUTED" text)
             (search "FN2-REFUTATION-GROUND" text)
             (search "FN2-REFUTATION-GUARDED" text)
             (search "NATP" text)
             (search "unfinished original" text)
             (search "link unverified" text)
             (search "admitted proofs: 0" text)
             (not (search "| `FN2-REFUTATION-ORIGINAL` | :PROVED" text)))
        (value '(value-triple :refuted-original-exported))
      (er soft 'owed-refutation-export "Refutation status, exact claim or unfinished/proof counts were lost."))))))
(value-triple (cw "OWED-REFUTATION-EXPORT PASS~%"))
(good-bye)
