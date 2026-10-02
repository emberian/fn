; Current record schema subjects: schemas 1 and 2 (the stage-0 revert of the
; acceptance-binding field, planning/design-store-representation-2026-10-01.md
; section 5).  The golden vectors are the encoder's, the schema-1 vector
; decodes to its record, and a schema-3 header (the reverted mandatory-binding
; schema) is refused by name.
(in-package "ACL2")
(include-book "../../books/records")
(assert-event
 (equal (fn-record-encode-impl
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 5))
        *fn-record-schema1-golden-octets*))
(assert-event
 (equal (fn-record-encode-impl
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4294967296 5))
        *fn-record-schema2-golden-octets*))
(assert-event
 (equal (fn-record-decode-exact-impl *fn-record-schema1-golden-octets*)
        (fn-record-result-ok
         (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 5))))
(assert-event
 (equal (fn-record-decode-exact-impl '(68 102 110 45 114 3))
        (fn-record-parse-error :unknown-version)))
