; Run after checkpoint-member-refutation-unit is certified:
; tools/acl2 --timeout 60 < tests/checkpoint-member-refutation-export.lsp
; Ordinary output is outside book events; no trust tag or raw evaluator.
(in-package "ACL2")
(set-ld-error-action '(:exit 2) state)
(set-cbd "tests/")
(include-book "checkpoint-member-refutation-unit" :uncertified-okp nil)
(include-book "../books/owed-report" :uncertified-okp nil)
(include-book "std/io/read-file-bytes" :dir :system)
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(fn2-owed-export
 "../build/checkpoint-member-refutation-export.md"
 (list (cons 'fn2-checkpoint-installation-pack-member-fields-type
             (fn2-decl-row '(:square fn2-checkpoint-installation-pack-member-fields-type) (w state))))
 state)
(defun fn2-refutation-octet-characters (bytes)
 (declare (xargs :verify-guards nil))
 (if (atom bytes) nil
  (cons (code-char (car bytes)) (fn2-refutation-octet-characters (cdr bytes)))))
(make-event
 (mv-let (bytes state) (read-file-bytes "../build/checkpoint-member-refutation-export.md" state)
  (if (stringp bytes) (er soft 'checkpoint-member-refutation-export "~s0" bytes)
   (let ((text (coerce (fn2-refutation-octet-characters bytes) 'string)))
    (if (and (search "| `FN2-CHECKPOINT-INSTALLATION-PACK-MEMBER-FIELDS-TYPE` | :REFUTED" text)
             (search "FN2-CHECKPOINT-MEMBER-ORIGINAL-REFUTED-INSTANCE" text)
             (search "FN2-CHECKPOINT-INSTALLATION-PACK-MEMBER-FIELDS-TYPE-UNDER-GUARD" text)
             (search "FN2-FIELDSP" text)
             (search "unfinished original" text)
             (search "link unverified" text)
             (search "admitted proofs: 0" text)
             (not (search "| `FN2-CHECKPOINT-INSTALLATION-PACK-MEMBER-FIELDS-TYPE` | :PROVED" text)))
        (value '(value-triple :refuted-original-exported))
      (er soft 'checkpoint-member-refutation-export "Refutation status, exact claim or unfinished/proof counts were lost."))))))
(value-triple (cw "MEMBER-REFUTATION-EXPORT PASS~%"))
(good-bye)
