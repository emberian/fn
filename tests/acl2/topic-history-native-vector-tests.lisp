(in-package "ACL2")
(include-book "../../books/topic-history-metadata")
(include-book "../../books/codec-attach")

; The native test's fixed fields are outputs of this ACL2 encoder.  The
; fixture's exact authored source is separately pinned by SHA-256 in Python
; (a file fingerprint).  The IDs are BLAKE3 identities (store format 10).
(defconst *thnv-keyset* '(102 110 47 115 117 98 106 101 99 116 47 118 49 0 1 2 187 188 110 101 219 149 184 49 80 41 81 154 160 238 195 139 245 14 44 145 36 129 83 74 45 127 161 2 161 151 87 73))
(defconst *thnv-root-id* '(102 110 47 115 117 98 106 101 99 116 47 118 49 0 1 2 11 233 16 14 39 77 235 181 169 249 158 10 218 84 106 128 65 205 10 18 0 121 35 77 197 171 230 149 228 189 110 39))
(defconst *thnv-root*
  (list :root (make-list 32 :initial-element 1)
        (make-list 32 :initial-element 85) *thnv-keyset*
        '(102 110 46 116 101 115 116)
        (list (list (make-list 32 :initial-element 85) *thnv-keyset*))))
(defconst *thnv-report*
  (list :report *thnv-root-id* *thnv-root-id* nil))
(defconst *thnv-second-root*
  (list :root (make-list 32 :initial-element 2)
        (make-list 32 :initial-element 85) *thnv-keyset*
        '(102 110 46 116 101 115 116)
        (list (list (make-list 32 :initial-element 85) *thnv-keyset*))))
(assert-event (fn-th-value-p *thnv-root*))
(assert-event (fn-th-value-p *thnv-report*))
(assert-event (fn-th-value-p *thnv-second-root*))
(assert-event
 (equal (fn-th-field-encode *thnv-second-root*)
        (fn-record-string-octets "v1 AQBYIAICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICWCBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVgwZm4vc3ViamVjdC92MQABAru8bmXblbgxUClRmqDuw4v1DiyRJIFTSi1/oQKhl1dJR2ZuLnRlc3QBWCBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVgwZm4vc3ViamVjdC92MQABAru8bmXblbgxUClRmqDuw4v1DiyRJIFTSi1/oQKhl1dJ")))
(assert-event
 (equal (fn-th-field-encode *thnv-root*)
        (fn-record-string-octets "v1 AQBYIAEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBWCBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVgwZm4vc3ViamVjdC92MQABAru8bmXblbgxUClRmqDuw4v1DiyRJIFTSi1/oQKhl1dJR2ZuLnRlc3QBWCBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVgwZm4vc3ViamVjdC92MQABAru8bmXblbgxUClRmqDuw4v1DiyRJIFTSi1/oQKhl1dJ")))
(assert-event
 (equal (fn-th-field-encode *thnv-report*)
        (fn-record-string-octets "v1 AQJYMGZuL3N1YmplY3QvdjEAAQIL6RAOJ03rtan5ngraVGqAQc0KEgB5I03Fq+aV5L1uJ1gwZm4vc3ViamVjdC92MQABAgvpEA4nTeu1qfmeCtpUaoBBzQoSAHkjTcWr5pXkvW4nAA==")))
