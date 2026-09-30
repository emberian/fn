(in-package "ACL2")
(include-book "../../books/consumer-account-config-marker-invariants")

(defconst *fn-cacm-test-record*
 (fn-cfg-record-make 3 17 4
  (fn-cacm-marker '(97) 3 8 12 16 2 (make-list 32 :initial-element 7))
  (fn-clock-observation 1000 2000 5 t)))
(defconst *fn-cacm-test-wide*
 (fn-cfg-record-make *fn-cbor-max-uint64* *fn-cbor-max-uint64* *fn-cbor-max-uint64*
  (fn-cacm-marker (make-list 64 :initial-element 255)
   *fn-cbor-max-uint64* *fn-cbor-max-uint64* *fn-cbor-max-uint64*
   *fn-cbor-max-uint64* *fn-cbor-max-uint64* (make-list 32 :initial-element 255))
  (fn-clock-observation *fn-cbor-max-uint64* *fn-cbor-max-uint64*
                        *fn-cbor-max-uint64* t)))
(assert-event (equal (fn-cacm-octet-ceiling) 210))
(assert-event (and (fn-cacm-recordp *fn-cacm-test-record*)
                  (not (fn-cfg-recordp *fn-cacm-test-record*))
                  (equal (fn-cacm-decode-exact (fn-cacm-encode *fn-cacm-test-record*))
                         (list :ok *fn-cacm-test-record*))))
(assert-event (and (equal (len (fn-cacm-encode *fn-cacm-test-wide*)) 210)
                  (equal (fn-cacm-decode-exact (fn-cacm-encode *fn-cacm-test-wide*))
                         (list :ok *fn-cacm-test-wide*))))
; Wide codec representability above is not actual allocator admission.
(assert-event (not (fn-cacm-recordp *fn-cfg-default-record*)))
(assert-event (equal (fn-cacm-encode *fn-cfg-default-record*) nil))
(assert-event (equal (car (fn-cacm-decode-exact (fn-cfg-encode *fn-cfg-default-record*))) :error))
(assert-event
 (let ((r (fn-cfg-record-make 0 0 0
           (fn-cacm-marker '(0) 0 0 0 0 0 (make-list 32 :initial-element 0))
           (fn-clock-observation 0 0 0 nil))))
  (equal (fn-cacm-decode-exact (fn-cacm-encode r)) (list :ok r))))

(defun fn-cacm-test-prefixes (n bytes)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (equal (car (fn-cacm-decode-exact nil)) :error)
   (and (equal (car (fn-cacm-decode-exact (ec-call (take (- n 1) bytes)))) :error)
        (fn-cacm-test-prefixes (- n 1) bytes))))
(assert-event (fn-cacm-test-prefixes (len (fn-cacm-encode *fn-cacm-test-record*))
                                    (fn-cacm-encode *fn-cacm-test-record*)))
(assert-event (equal (car (fn-cacm-decode-exact
                           (append (fn-cacm-encode *fn-cacm-test-record*) '(0)))) :error))
(assert-event (equal (car (fn-cacm-decode-exact
                           (update-nth 7 0 (fn-cacm-encode *fn-cacm-test-record*)))) :error))
(assert-event (equal (car (fn-cacm-decode-exact
                           (update-nth 8 14 (fn-cacm-encode *fn-cacm-test-record*)))) :error))
(assert-event (equal (car (fn-cacm-decode-exact
                           (update-nth 9 0 (fn-cacm-encode *fn-cacm-test-record*)))) :error))
(assert-event (equal (car (fn-cacm-decode-exact (make-list 211 :initial-element 0))) :error))
(assert-event (equal (car (fn-cacm-decode-exact (cons 300 nil))) :error))
(assert-event (equal (car (fn-cacm-decode-exact '(70 . 1))) :error))

; Complete literal keystone antecedent/conclusion witnesses. The maximum
; vector asserts the recognizer too: an encoder result alone is insufficient.
(assert-event
 (and (fn-cacm-recordp *fn-cacm-test-wide*)
      (equal (fn-cacm-decode-exact (fn-cacm-encode *fn-cacm-test-wide*))
             (list :ok *fn-cacm-test-wide*))
      (fn-cbor-octet-listp (fn-cacm-encode *fn-cacm-test-wide*))
      (<= (len (fn-cacm-encode *fn-cacm-test-wide*)) (fn-cacm-octet-ceiling))))
; Hypothesis-removal witness for the sole recordp premise of decode-encode.
; There are no retained hypotheses. Ordinary C records are valid inputs to
; their own codec, but are outside this explicitly typed adoption variant.
(assert-event
 (and (not (fn-cacm-recordp *fn-cfg-default-record*))
      (not (equal (fn-cacm-decode-exact (fn-cacm-encode *fn-cfg-default-record*))
                  (list :ok *fn-cfg-default-record*)))))
; The octet and length theorems are unconditional, including refused input.
(assert-event
 (and (fn-cbor-octet-listp (fn-cacm-encode *fn-cfg-default-record*))
      (<= (len (fn-cacm-encode *fn-cfg-default-record*)) (fn-cacm-octet-ceiling))))
