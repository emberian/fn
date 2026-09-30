; Current mandatory-binding schema subjects; no legacy evidence transfer.
(in-package "ACL2")
(include-book "../../books/records")
(assert-event
 (equal (fn-record-encode-impl
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e"
                          4 5 *fn-record-golden-binding*))
        *fn-record-schema3-golden-octets*))
(assert-event
 (equal (fn-record-encode-impl
          (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e"
                          4294967296 5 *fn-record-golden-binding*))
        *fn-record-schema4-golden-octets*))
(assert-event
 (equal (fn-record-decode-exact-impl '(68 102 110 45 114 1))
        (fn-record-parse-error :unknown-version)))
(assert-event
 (and (fn-record-shapep
        (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 5 nil))
      (not (fn-record-p
        (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 5 nil)))))
