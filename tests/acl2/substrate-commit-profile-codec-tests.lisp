(in-package "ACL2")
(include-book "../../books/substrate-commit-profile-codec")
(include-book "../../books/statement-attach")
(defconst *stcpt-profile* (fn-stcp-profile 586 513 17))
(defconst *stcpt-commit*
 (fn-me-commit (make-list 513 :initial-element 1) 0
               (make-list 32 :initial-element 2) :remove
               (make-list 32 :initial-element 3)))
(defun stcpt-encode (p commit)
 (declare (xargs :guard t))
 (mv-let (cursor used) (fn-stcp-enc-drive p (fn-stcp-encode-start p commit) 10000)
  (declare (ignore used)) (fn-stcp-enc-result cursor)))
(defun stcpt-decode (p wire)
 (declare (xargs :guard t))
 (mv-let (cursor used) (fn-stcp-dec-drive p (fn-stcp-decode-start p wire) 10000)
  (declare (ignore used)) (fn-stcp-dec-result cursor)))
(make-event (list 'defconst '*stcpt-wire* (list 'quote (fn-stmt-value (stcpt-encode *stcpt-profile* *stcpt-commit*)))))
(assert-event
 (and (equal (len *stcpt-wire*) 586)
      (equal *stcpt-wire* (fn-stx-commit-encode *stcpt-commit*))
      (equal (stcpt-decode *stcpt-profile* *stcpt-wire*) (fn-stmt-ok *stcpt-commit*))
      (equal (stcpt-decode *stcpt-profile* (fn-record-octets-string *stcpt-wire*))
             (fn-stmt-ok *stcpt-commit*))
      (equal (fn-stx-commit-decode-exact *stcpt-wire*) (fn-stmt-error :limit))))
(assert-event
 (let* ((start (fn-stcp-decode-start *stcpt-profile* *stcpt-wire*))
         )
  (mv-let (cursor used) (fn-stcp-decode-resume *stcpt-profile* start)
   (and (equal used 17)
       (not (fn-stcp-terminalp cursor))
       (null (fn-stcp-dec-result cursor))
       (equal (stcpt-decode (fn-stcp-profile 585 513 17) *stcpt-wire*)
              (fn-stmt-error :profile-limit))
       (equal (stcpt-decode (fn-stcp-profile 586 512 17) *stcpt-wire*)
              (fn-stmt-error :profile-limit))
       (equal (fn-stcp-profile-check (fn-stcp-profile 586 513 0)) :invalid-quantum)))))
(assert-event
 (let ((c (fn-stcp-encode-start *stcpt-profile*
          (fn-me-commit '(1) (+ 1 *fn-cbor-max-uint64*) '(2) :remove '(3)))))
  (and (equal (fn-stcp-enc-result c) (fn-stmt-error :unsupported-format))
       (null (fn-stcp-at 1 c)) (null (fn-stcp-at 6 c))
       (equal (fn-stcp-profile-check (fn-stcp-profile 586 (+ 1 *fn-cbor-max-uint*) 17))
              :unsupported-format))))
(defun stcpt-wide-roundtrip (base)
 (declare (xargs :guard t))
 (let* ((p (fn-stcp-profile 100 10 1))
        (commit (fn-me-commit '(1) base '(2) :remove '(3)))
        (wire (fn-stmt-value (stcpt-encode p commit))))
  (equal (stcpt-decode p wire) (fn-stmt-ok commit))))
(assert-event (and (stcpt-wide-roundtrip 4294967295)
                   (stcpt-wide-roundtrip 4294967296)
                   (stcpt-wide-roundtrip 18446744073709551615)))
(assert-event
 (and (equal (stcpt-decode (fn-stcp-profile 100 10 1)
                          '(65 1 27 0 0 0 0 0 0 0 1 65 2 1 65 3))
              (fn-stmt-error :noncanonical))
      (equal (stcpt-decode *stcpt-profile* (append *stcpt-wire* '(0)))
              (fn-stmt-error :trailing))
      (equal (stcpt-decode *stcpt-profile* '(89 2)) (fn-stmt-error :truncated))))
; Literal unconditional work-bound teeth: complete statement and conclusion.
(assert-event
 (mv-let (cursor used) (fn-stcp-enc-drive *stcpt-profile*
                       (fn-stcp-encode-start *stcpt-profile* *stcpt-commit*) 17)
  (declare (ignore cursor)) (<= used (nfix 17))))
(assert-event
 (mv-let (cursor used) (fn-stcp-dec-drive *stcpt-profile*
                       (fn-stcp-decode-start *stcpt-profile* *stcpt-wire*) 17)
  (declare (ignore cursor)) (<= used (nfix 17))))
(assert-event
 (mv-let (cursor used) (fn-stcp-dec-drive *stcpt-profile*
                       (fn-stcp-decode-start *stcpt-profile* *stcpt-wire*) 0)
  (and (equal used 0) (equal cursor (fn-stcp-decode-start *stcpt-profile* *stcpt-wire*)))))
; Matched fixture work coordinates; these are literal costs, not a general cost theorem.
(assert-event
 (mv-let (cursor used) (fn-stcp-enc-drive *stcpt-profile*
                       (fn-stcp-encode-start *stcpt-profile* *stcpt-commit*) 10000)
  (and (equal used 1767) (equal (fn-stcp-enc-result cursor) (fn-stmt-ok *stcpt-wire*)))))
(assert-event
 (mv-let (cursor used) (fn-stcp-dec-drive *stcpt-profile*
                       (fn-stcp-decode-start *stcpt-profile* *stcpt-wire*) 10000)
  (and (equal used 1170) (equal (fn-stcp-dec-result cursor) (fn-stmt-ok *stcpt-commit*)))))
