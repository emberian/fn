; Run after checkpoint-member-guarded-evidence-unit is certified:
; tools/acl2 --timeout 60 < tests/checkpoint-member-guarded-evidence-export.lsp
; Ordinary output is outside book events; no trust tag or raw evaluator.
(in-package "ACL2")
(set-ld-error-action '(:exit 2) state)
(set-cbd "tests/")
(include-book "checkpoint-member-guarded-evidence-unit" :uncertified-okp nil)
(include-book "../books/owed-report" :uncertified-okp nil)
(include-book "std/io/read-file-bytes" :dir :system)
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(fn2-assert-square-evidence fn2-checkpoint-installation-pack-member-fields-type-under-guard-claim)
(fn2-owed-export
 "../build/checkpoint-member-guarded-evidence-export.md"
 (list (cons 'fn2-checkpoint-installation-pack-member-fields-type
             (fn2-decl-row '(:square fn2-checkpoint-installation-pack-member-fields-type) (w state)))
       (cons 'fn2-checkpoint-installation-pack-member-fields-type-under-guard-claim
             (fn2-decl-row '(:square fn2-checkpoint-installation-pack-member-fields-type-under-guard-claim) (w state))))
 state)
(defun fn2-refutation-octet-characters (bytes)
 (declare (xargs :verify-guards nil))
 (if (atom bytes) nil
  (cons (code-char (car bytes)) (fn2-refutation-octet-characters (cdr bytes)))))
(make-event
 (mv-let (bytes state) (read-file-bytes "../build/checkpoint-member-guarded-evidence-export.md" state)
  (if (stringp bytes) (er soft 'checkpoint-member-guarded-evidence-export "~s0" bytes)
   (let ((text (coerce (fn2-refutation-octet-characters bytes) 'string)))
    (if (and (search "| `FN2-CHECKPOINT-INSTALLATION-PACK-MEMBER-FIELDS-TYPE` | :REFUTED" text)
             (search "FN2-CHECKPOINT-MEMBER-ORIGINAL-REFUTED-INSTANCE" text)
             (search "FN2-CHECKPOINT-INSTALLATION-PACK-MEMBER-FIELDS-TYPE-UNDER-GUARD" text)
             (search "FN2-FIELDSP" text)
             (search "unfinished original" text)
             (search "link unverified" text)
             (search "admitted proofs: 1" text)
             (search "| `FN2-CHECKPOINT-INSTALLATION-PACK-MEMBER-FIELDS-TYPE-UNDER-GUARD-CLAIM` | :PROVED" text)
             (search "DOMAIN-RESTRICTION-OF" text)
             (not (search "| `FN2-CHECKPOINT-INSTALLATION-PACK-MEMBER-FIELDS-TYPE` | :PROVED" text)))
        (value '(value-triple :refuted-original-exported))
      (er soft 'checkpoint-member-guarded-evidence-export "Refutation status, exact claim or unfinished/proof counts were lost."))))))
(value-triple (cw "MEMBER-GUARDED-EVIDENCE-EXPORT PASS~%"))
(good-bye)
