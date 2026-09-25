; fn: teeth for books/records-stobj.lisp and books/frame-stobj.lisp (the
; megaspike, D28).
;
; What this book is evidence FOR.  The correspondence theorems of the two
; books are deferred on the spike (`;; SPIKE:' marks), so what this book
; gives is the witness the dev lane's proofs will subsume: on a real record
; the buffer path writes exactly the octets the list model writes
; (`fn-frame-store-protected' of `fn-record-encode-impl' under the SHA-256
; trailer, the bytes host/native/io.lisp wrote before the buffer), and reads
; back exactly the record, through a local instance of the stobj.  A pass
; here is agreement by evaluation on these inputs; it is not the proof.

(in-package "ACL2")
(include-book "../../books/records-stobj")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Every entry the host calls is guard-verified.

(assert-event
 (equal (list (symbol-class 'fn-rcs-store-seal-record (w state))
              (symbol-class 'fn-rcs-unframe-record (w state))
              (symbol-class 'fn-rcs-encode-into (w state))
              (symbol-class 'fn-rcs-decode-exact (w state))
              (symbol-class 'fn-frs-store-seal (w state))
              (symbol-class 'fn-frs-store-decode (w state))
              (symbol-class 'fn-octets-from-list (w state))
              (symbol-class 'fn-octets-list (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The buffer path run in a local stobj.

(defun fn-rcs-test-seal (record)
  ; (okp . octets): the sealed frame of RECORD as the buffer path writes it.
  (declare (xargs :guard t))
  (with-local-stobj fn-octets
    (mv-let (okp octets fn-octets)
      (mv-let (okp fn-octets)
        (fn-rcs-store-seal-record record fn-octets)
        (mv okp (fn-octets-list fn-octets) fn-octets))
      (cons okp octets))))

(defun fn-rcs-test-unframe (frame)
  ; (kind . value): what the recovery entry reads from FRAME.
  (declare (xargs :guard (fn-cbor-octet-listp frame)))
  (with-local-stobj fn-octets
    (mv-let (kind value fn-octets)
      (let ((fn-octets (fn-octets-from-list frame fn-octets)))
        (mv-let (kind value)
          (fn-rcs-unframe-record fn-octets)
          (mv kind value fn-octets)))
      (cons kind value))))

(defun fn-rcs-test-model-frame (record)
  ; The list model's frame: the protected prefix, then SHA-256 over it (what
  ; `fn-frame-digest' is in the host image, books/crypto-attach).
  (declare (xargs :guard t :verify-guards nil))
  (let ((prefix (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                                    *fn-frame-store-kind* (fn-record-encode-impl record))))
    (append prefix (fn-sha256 prefix))))

(defun fn-rcs-test-payload (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (fn-rcs-test-payload (1- n) (cons (mod (* 7 n) 256) acc))))

; -----------------------------------------------------------------------------
; Witnesses.

; A schema-1 record with a short payload.
(defconst *fn-rcs-test-record*
  (fn-record-make 1 1 1 "<t1@example.invalid>" '(72 105 13 10 66 111 100 121 13 10)
                  '("fn.test") "obligation" "subject" "evidence" 4 1700000000))

(assert-event (fn-record-p *fn-rcs-test-record*))
(assert-event (fn-rcon-record-p *fn-rcs-test-record*))

(assert-event
 (equal (fn-rcs-test-seal *fn-rcs-test-record*)
        (cons t (fn-rcs-test-model-frame *fn-rcs-test-record*))))

(assert-event
 (equal (fn-rcs-test-unframe (fn-rcs-test-model-frame *fn-rcs-test-record*))
        (cons :record *fn-rcs-test-record*)))

; A legacy (schema 0) record, two groups, a payload long enough for the
; three-octet CBOR head (256 <= n < 65536) and the two-octet head on the
; metadata.
(defconst *fn-rcs-test-record-legacy*
  (fn-record-make 77 77 3 "<legacy@example.invalid>" (fn-rcs-test-payload 3000 nil)
                  '("fn.test" "fn.other") "an-obligation-id-of-some-length-xx"
                  "a subject" "e" 12 :legacy))

(assert-event (fn-record-p *fn-rcs-test-record-legacy*))

(assert-event
 (equal (fn-rcs-test-seal *fn-rcs-test-record-legacy*)
        (cons t (fn-rcs-test-model-frame *fn-rcs-test-record-legacy*))))

(assert-event
 (equal (fn-rcs-test-unframe (fn-rcs-test-model-frame *fn-rcs-test-record-legacy*))
        (cons :record *fn-rcs-test-record-legacy*)))

; The encoder alone equals the list encoder on both records.
(defun fn-rcs-test-encode (record)
  (declare (xargs :guard t))
  (with-local-stobj fn-octets
    (mv-let (okp octets fn-octets)
      (mv-let (okp fn-octets)
        (fn-rcs-encode-into record fn-octets)
        (mv okp (fn-octets-list fn-octets) fn-octets))
      (cons okp octets))))

(assert-event
 (and (equal (fn-rcs-test-encode *fn-rcs-test-record*)
             (cons t (fn-record-encode-impl *fn-rcs-test-record*)))
      (equal (fn-rcs-test-encode *fn-rcs-test-record-legacy*)
             (cons t (fn-record-encode-impl *fn-rcs-test-record-legacy*)))))

; Not a record: the encoder writes nothing and says so.
(assert-event (equal (fn-rcs-test-encode '(:not-a-record)) (cons nil nil)))

; -----------------------------------------------------------------------------
; Refusals, in the reference's words.

; A frame with its last trailer octet flipped is refused for integrity.
(defun fn-rcs-test-flip-last (xs)
  (declare (xargs :guard (fn-cbor-octet-listp xs)))
  (if (atom xs) nil
    (if (atom (cdr xs)) (list (logxor (car xs) 1))
      (cons (car xs) (fn-rcs-test-flip-last (cdr xs))))))

(assert-event
 (equal (fn-rcs-test-unframe
         (fn-rcs-test-flip-last (fn-rcs-test-model-frame *fn-rcs-test-record*)))
        (cons :frame-error :integrity)))

; A frame cut short is truncated.
(assert-event
 (equal (fn-rcs-test-unframe (take 20 (fn-rcs-test-model-frame *fn-rcs-test-record*)))
        (cons :frame-error :truncated)))

; A well-formed frame carrying octets that are not a record hands them back
; for the list codec (a retention or configuration event on the real path).
(assert-event
 (let ((prefix (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                                   *fn-frame-store-kind* '(1 2 3))))
   (equal (fn-rcs-test-unframe (append prefix (fn-sha256 prefix)))
          (cons :octets '(1 2 3)))))

; The decoder alone agrees with the reference on a record's octets and on
; octets that are not one.
(defun fn-rcs-test-decode (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (let ((fn-octets (fn-octets-from-list octets fn-octets)))
        (mv (fn-rcs-decode-exact 0 (fn-octets-len fn-octets) fn-octets) fn-octets))
      result)))

(assert-event
 (and (equal (fn-rcs-test-decode (fn-record-encode-impl *fn-rcs-test-record*))
             (fn-record-decode-exact-impl (fn-record-encode-impl *fn-rcs-test-record*)))
      (equal (fn-rcs-test-decode (fn-record-encode-impl *fn-rcs-test-record-legacy*))
             (fn-record-decode-exact-impl (fn-record-encode-impl *fn-rcs-test-record-legacy*)))
      (equal (fn-rcs-test-decode '(1 2 3)) (fn-record-decode-exact-impl '(1 2 3)))
      (equal (fn-rcs-test-decode nil) (fn-record-decode-exact-impl nil))
      (equal (fn-rcs-test-decode (take 30 (fn-record-encode-impl *fn-rcs-test-record*)))
             (fn-record-decode-exact-impl (take 30 (fn-record-encode-impl *fn-rcs-test-record*))))))
