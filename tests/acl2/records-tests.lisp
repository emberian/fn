; Golden vectors for the exact schema-0 and schema-1 transaction grammars.
(in-package "ACL2")
(include-book "../../books/records-attach")

(defconst *fn-record-test-record*
  (fn-record-make 1 2 3 "<a>" '(9 8) '("g") "o" "s" "e" 4 :legacy))

; The fixed primitive sequence is independently written out here.
(defconst *fn-record-test-octets*
  '(68 102 110 45 114 0 1 2 3 67 60 97 62 66 9 8 1 65 103 65 111 65 115 65 101 4))

(assert-event (fn-record-p *fn-record-test-record*))
(assert-event (equal (fn-record-encode *fn-record-test-record*)
                     *fn-record-test-octets*))
(assert-event (equal (fn-record-decode-exact *fn-record-test-octets*)
                     (list :ok *fn-record-test-record*)))
(assert-event (fn-record-result-okp
               (fn-record-decode-exact *fn-record-test-octets*)))
(assert-event (equal (fn-record-result-record
                      (fn-record-decode-exact *fn-record-test-octets*))
                     *fn-record-test-record*))

(defconst *fn-record-test-stamped*
  (fn-record-with-stamp *fn-record-test-record* 5))
(defconst *fn-record-test-stamped-octets*
  '(68 102 110 45 114 1 1 2 3 67 60 97 62 66 9 8 1 65 103
    65 111 65 115 65 101 4 5))
(assert-event (fn-record-p *fn-record-test-stamped*))
(assert-event (equal (fn-record-encode *fn-record-test-stamped*)
                     *fn-record-test-stamped-octets*))
(assert-event (equal (fn-record-decode-exact *fn-record-test-stamped-octets*)
                     (list :ok *fn-record-test-stamped*)))
(assert-event (equal (fn-record-encode
                      (fn-record-result-record
                       (fn-record-decode-exact *fn-record-test-stamped-octets*)))
                     *fn-record-test-stamped-octets*))

; Exact byte/string conversion has no host reader path or textual alias.
(assert-event (equal (fn-record-string-octets "<a>") '(60 97 62)))
(assert-event (equal (fn-record-octets-string '(60 97 62)) "<a>"))
(assert-event (not (fn-record-ascii-stringp
                    (coerce (list (code-char 128)) 'string))))

; The decoder rejects a non-shortest CBOR magic length before record parsing.
(assert-event (equal (fn-record-decode-exact
                      '(88 4 102 110 45 114 0))
                     '(:error :noncanonical)))

; Header/version/count/type/trailing errors each have an explicit vector.
(assert-event (equal (fn-record-decode-exact '(68 102 110 45 115 0))
                     '(:error :magic)))
(assert-event (equal (fn-record-decode-exact '(68 102 110 45 114 2))
                     '(:error :unknown-version)))
(assert-event (equal (fn-record-decode-exact
                      '(68 102 110 45 114 0 1 2 3 65 97 64 17))
                     '(:error :groups-limit)))
(assert-event (equal (fn-record-decode-exact
                      '(68 102 110 45 114 0 65 97))
                     '(:error :field-type)))
(assert-event (equal (fn-record-decode-exact
                      '(68 102 110 45 114 0 1 2 3 67 60 97 62 66 9 8 1
                        65 103 65 111 65 115 65 101 4 0))
                     '(:error :trailing)))
(assert-event (equal (fn-record-decode-exact
                      '(68 102 110 45 114 0 1 2 3 67 60 97 62 66 9))
                     '(:error :truncated)))

; Invalid local domain records never receive an encoding.
(assert-event (equal (fn-record-encode
                      (fn-record-make 1 2 3 "<a>" nil '("g" "g")
                                      "o" "s" "e" 4 :legacy))
                     nil))
(assert-event (equal (fn-record-encode
                      (fn-record-make 1 2 3 "<a>" nil '("g")
                                      "" "s" "e" 4 :legacy))
                     nil))
