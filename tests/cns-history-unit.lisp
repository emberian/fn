; Served pool cursor history/incarnation boundaries; no caller assertion
; substitutes for decoding the cursor bytes against the live identity.
(in-package "ACL2")
(include-book "cns-decode-unit")

(defun fn2-chu-cursor (history incarnation)
 (declare (xargs :verify-guards nil))
 (fn2-fncu-encode (list :cursor 0 history incarnation '(1) '(2) '(1) 1 1 1 5)))

(defun fn2-chu-decode (history incarnation bytes)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (answer fn2-fields)
   (with-local-stobj fn2-pool
    (mv-let (answer fn2-fields fn2-pool)
     (b* (((mv fn2-fields fn2-pool) (fn2-layout-test-init fn2-fields fn2-pool))
          (fn2-fields (fn2-fields-init 128 fn2-fields))
          (fn2-pool (fn2-layout-test-write bytes 0 0 fn2-pool))
          ((mv reason cid epoch position fn2-fields)
           (fn2-cns-decode-cursor history incarnation 0 0 (len bytes) 2 0 1 1 0 1 fn2-fields fn2-pool)))
       (mv (list reason cid epoch position) fn2-fields fn2-pool))
     (mv answer fn2-fields)))
   answer)))

(defun fn2-chu-roundtrip (history incarnation)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (answer fn2-fields)
   (with-local-stobj fn2-pool
    (mv-let (answer fn2-fields fn2-pool)
     (b* (((mv fn2-fields fn2-pool) (fn2-layout-test-init fn2-fields fn2-pool))
          (fn2-fields (fn2-fields-init 128 fn2-fields))
          ((mv code off len fn2-fields fn2-pool)
           (fn2-cns-put-cursor history incarnation 0 1 2 1 1 5 0 1 1 0 1 fn2-fields fn2-pool))
          (bytes (fn2-layout-test-read len 0 off fn2-pool))
          ((mv reason cid epoch position fn2-fields)
           (fn2-cns-decode-cursor history incarnation 16 off len 2 0 1 1 0 1 fn2-fields fn2-pool)))
       (mv (list code reason cid epoch position bytes) fn2-fields fn2-pool))
     (mv answer fn2-fields)))
   answer)))

; Multi-octet ids must survive the actual served encoder and pool decoder,
; with the exact shortest bytes independently encoded by the list codec.
(assert-event
 (and (equal (fn2-chu-decode 257 65537 (fn2-chu-cursor '(1 1) '(1 0 1))) '(0 1 1 5))
      (equal (fn2-chu-roundtrip 257 65537)
             (list :ok 0 1 1 5 (fn2-chu-cursor '(1 1) '(1 0 1))))
      (equal (fn2-chu-roundtrip 1152921504606846975 1152921504606846975)
             (list :ok 0 1 1 5
                   (fn2-chu-cursor '(15 255 255 255 255 255 255 255)
                                   '(15 255 255 255 255 255 255 255))))))

; Neither a different physical history nor its incarnation is interchangeable.
(assert-event
 (and (equal (fn2-chu-decode 258 65537 (fn2-chu-cursor '(1 1) '(1 0 1)))
             (list *fn2-cns-reason-scope* 0 0 0))
      (equal (fn2-chu-decode 257 65538 (fn2-chu-cursor '(1 1) '(1 0 1)))
             (list *fn2-cns-reason-scope* 0 0 0))))

; Malformed integer spellings do not alias the same live identity. In
; particular a leading zero is rejected even when its numeric value matches.
(assert-event
 (and (equal (fn2-chu-decode 257 65537 (fn2-chu-cursor '(0 1 1) '(1 0 1)))
             (list *fn2-cns-reason-scope* 0 0 0))
      (equal (fn2-chu-decode 257 65537 (fn2-chu-cursor '(1 1) '(0 1 0 1)))
             (list *fn2-cns-reason-scope* 0 0 0))
      (equal (fn2-chu-decode 257 65537 (fn2-chu-cursor '(0) '(1 0 1)))
             (list *fn2-cns-reason-scope* 0 0 0))
      (equal (fn2-chu-decode 257 65537 (fn2-chu-cursor '(1 1) '(0)))
             (list *fn2-cns-reason-scope* 0 0 0))
      (equal (fn2-chu-decode 257 65537 (fn2-chu-cursor nil '(1 0 1)))
             (list *fn2-cns-reason-scope* 0 0 0))
      (equal (fn2-chu-decode 257 65537 (fn2-chu-cursor '(0 0 0 0 0 0 0 1 1) '(1 0 1)))
             (list *fn2-cns-reason-scope* 0 0 0))
      (equal (fn2-chu-decode 257 65537 (fn2-chu-cursor '(16 0 0 0 0 0 0 0) '(1 0 1)))
             (list *fn2-cns-reason-scope* 0 0 0))
      (equal (fn2-chu-decode 257 65537 (append (fn2-chu-cursor '(1 1) '(1 0 1)) '(0)))
             (list *fn2-cns-reason-frame* 0 0 0))))
