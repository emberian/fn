(in-package "ACL2")
(include-book "../../books/topic-history-metadata")
(include-book "../../books/codec-attach")

; The native test's fixed fields are outputs of this ACL2 encoder.  The
; fixture's exact authored source is separately pinned by SHA-256 in Python.
(defconst *thnv-keyset* '(102 110 47 115 117 98 106 101 99 116 47 118 49 0 1 1 201 163 178 8 54 101 94 26 207 198 244 149 153 143 90 52 250 129 34 209 2 84 199 74 200 147 6 176 68 96 196 120))
(defconst *thnv-root-id* '(102 110 47 115 117 98 106 101 99 116 47 118 49 0 1 1 137 34 216 149 235 11 126 12 78 222 55 10 125 196 129 54 9 196 57 145 229 70 3 57 80 246 1 78 164 198 125 10))
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
        (fn-record-string-octets "v1 AQBYIAICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICWCBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVgwZm4vc3ViamVjdC92MQABAcmjsgg2ZV4az8b0lZmPWjT6gSLRAlTHSsiTBrBEYMR4R2ZuLnRlc3QBWCBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVgwZm4vc3ViamVjdC92MQABAcmjsgg2ZV4az8b0lZmPWjT6gSLRAlTHSsiTBrBEYMR4")))
(assert-event
 (equal (fn-th-field-encode *thnv-root*)
        (fn-record-string-octets "v1 AQBYIAEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBWCBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVgwZm4vc3ViamVjdC92MQABAcmjsgg2ZV4az8b0lZmPWjT6gSLRAlTHSsiTBrBEYMR4R2ZuLnRlc3QBWCBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVgwZm4vc3ViamVjdC92MQABAcmjsgg2ZV4az8b0lZmPWjT6gSLRAlTHSsiTBrBEYMR4")))
(assert-event
 (equal (fn-th-field-encode *thnv-report*)
        (fn-record-string-octets "v1 AQJYMGZuL3N1YmplY3QvdjEAAQGJItiV6wt+DE7eNwp9xIE2CcQ5keVGAzlQ9gFOpMZ9ClgwZm4vc3ViamVjdC92MQABAYki2JXrC34MTt43Cn3EgTYJxDmR5UYDOVD2AU6kxn0KAA==")))
