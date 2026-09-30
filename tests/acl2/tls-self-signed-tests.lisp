; Witnesses and teeth for books/tls-self-signed.lisp (row Q10a).  The public
; key is a P-256 SubjectPublicKeyInfo generated for this file; the signature
; is `openssl dgst -sha256 -sign' of the accepted body below with its key
; (the certificate it makes verifies with `openssl verify -x509_strict' at a
; time inside its validity; recorded in the lane's log, not a claim here).
(in-package "ACL2")
(include-book "../../books/tls-self-signed")

(defconst *tsst-spki* '(48 89 48 19 6 7 42 134 72 206 61 2 1 6 8 42 134 72 206 61 3 1 7 3 66 0 4 29 221 125 229 206 113 38 61 79 22 148 150 33 255 150 175 151 35 204 215 104 243 113 142 161 136 178 217 188 53 194 59 211 97 81 224 248 107 227 5 94 174 82 112 65 54 111 6 113 222 14 38 173 240 26 121 219 26 222 188 189 254 206 106))
(defconst *tsst-sig* '( 48 69 2 33 0 144 14 140 138 207 199 109 116 28 192 226 73 3 167 91 170 64 136 251 94 196 86 188 194 236 12 213 204 176 32 94 108 2 32 3 75 123 123 194 49 225 35 84 196 26 186 77 70 239 213 57 151 46 139 210 137 33 133 100 56 120 98 177 255 45 163 ))
(defconst *tsst-serial* (make-list 16 :initial-element 200))
(defconst *tsst-names* (list "news.example.org" "127.0.0.1" "::1"))
(defconst *tsst-now* 812345678000)

; ---------------------------------------------------------------------------
; fn-ssc-tlv-read-of-tlv.  Positive witnesses, every length form: the
; hypotheses hold (an octet tag, true lists, a length below 2^24) and the
; reading is the tag, the content and the rest.
(assert-event (equal (fn-ssc-tlv-read (append (fn-ssc-tlv 48 '(1 2 3)) '(9)))
                     '(48 (1 2 3) (9))))
(assert-event (let ((c (make-list 200 :initial-element 7)))
                (and (equal (take 2 (fn-ssc-tlv 4 c)) '(4 129))
                     (equal (fn-ssc-tlv-read (append (fn-ssc-tlv 4 c) '(1)))
                            (list 4 c '(1))))))
(assert-event (let ((c (make-list 300 :initial-element 7)))
                (and (equal (take 2 (fn-ssc-tlv 4 c)) '(4 130))
                     (equal (fn-ssc-tlv-read (fn-ssc-tlv 4 c)) (list 4 c nil)))))
(assert-event (let ((c (make-list 70000 :initial-element 7)))
                (and (equal (take 2 (fn-ssc-tlv 4 c)) '(4 131))
                     (equal (fn-ssc-tlv-read (fn-ssc-tlv 4 c)) (list 4 c nil)))))
; Hypothesis removal, one per hypothesis (the others checked true):
; a tag that is no octet,
(assert-event (and (true-listp '(1)) (not (fn-ssc-octetp 256))
                   (not (equal (fn-ssc-tlv-read (fn-ssc-tlv 256 '(1))) '(256 (1) nil)))))
; a content that is no true list,
(assert-event (and (fn-ssc-octetp 48) (not (true-listp '(1 . 2)))
                   (not (equal (fn-ssc-tlv-read (fn-ssc-tlv 48 '(1 . 2)))
                               '(48 (1 . 2) nil)))))
; a rest that is no true list,
(assert-event (and (fn-ssc-octetp 48) (not (true-listp 5))
                   (not (equal (fn-ssc-tlv-read (append (fn-ssc-tlv 48 '(1)) 5))
                               '(48 (1) 5)))))
; a content of 2^24 octets (the long form has no fourth octet).
(assert-event (let ((c (make-list *fn-ssc-length-limit* :initial-element 0)))
                (and (fn-ssc-octetp 4) (true-listp c)
                     (not (< (len c) *fn-ssc-length-limit*))
                     (not (equal (fn-ssc-tlv-read (fn-ssc-tlv 4 c)) (list 4 c nil))))))
; Mutation (labelled): a length written in a longer form than DER's minimal
; one is not read.
(assert-event (equal (fn-ssc-tlv-read '(48 129 3 1 2 3)) nil))

; ---------------------------------------------------------------------------
; fn-ssc-plan and fn-ssc-plan-body-is-one-sequence.  Positive witness: the
; antecedent (accepted) and the conclusion (one SEQUENCE, read back).
(assert-event
 (let ((plan (fn-ssc-plan *tsst-names* 365 *tsst-now* t *tsst-serial* *tsst-spki*)))
   (and (equal (car plan) :accepted)
        (fn-ssc-one-sequencep (cadr plan))
        (equal (fn-ssc-tlv 48 (cadr (fn-ssc-tlv-read (cadr plan)))) (cadr plan))
        (equal (len (cadr plan)) 376))))
; The names become the SAN in order: dNSName, iPAddress 4, iPAddress 16.
(assert-event (equal (fn-ssc-general-names *tsst-names*)
                     (append (fn-ssc-tlv 130 (fn-record-string-octets "news.example.org"))
                             '(135 4 127 0 0 1)
                             '(135 16 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1))))
; Refused by name.
(defmacro tsst-refused (reason names days now wall serial spki)
  `(assert-event (equal (fn-ssc-plan ,names ,days ,now ,wall ,serial ,spki)
                        '(:refused ,reason))))
(tsst-refused :no-names nil 365 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :name (list "bad_name") 365 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :name (list "0.0.0.0") 365 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :name (list "::") 365 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :name (list "-a.example") 365 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :name (list "a.example.") 365 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :name (list "ok.example" 7) 365 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :common-name-length
              (list (concatenate 'string (coerce (make-list 63 :initial-element #\a) 'string)
                                 ".ab"))
              365 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :clock *tsst-names* 365 *tsst-now* nil *tsst-serial* *tsst-spki*)
(tsst-refused :days *tsst-names* 0 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :days *tsst-names* 3000000 *tsst-now* t *tsst-serial* *tsst-spki*)
(tsst-refused :serial *tsst-names* 365 *tsst-now* t (make-list 15 :initial-element 1) *tsst-spki*)
(tsst-refused :spki *tsst-names* 365 *tsst-now* t *tsst-serial* (cdr *tsst-spki*))
(tsst-refused :spki *tsst-names* 365 *tsst-now* t *tsst-serial*
              (fn-ssc-tlv 48 (append '(48 13 6 9 42 134 72 134 247 13 1 1 1 5 0)
                                     (fn-ssc-tlv 3 '(0 1 2 3)))))
; A 63-octet label is a name; 64 is not.
(assert-event (fn-ssc-general-name (coerce (make-list 63 :initial-element #\a) 'string)))
(assert-event (not (fn-ssc-general-name (coerce (make-list 64 :initial-element #\a) 'string))))
; Validity: UTCTime through 2049, GeneralizedTime from 2050.
(assert-event (equal (car (fn-ssc-time *tsst-now*)) 23))
(assert-event (equal (car (fn-ssc-time (* 51 365 86400000))) 24))

; ---------------------------------------------------------------------------
; fn-ssc-certificate-carries-the-body and fn-ssc-certificate-pem-carries-the-body.
(defconst *tsst-tbs*
  (cadr (fn-ssc-plan *tsst-names* 365 *tsst-now* t *tsst-serial* *tsst-spki*)))
; Positive witnesses: accepted, and the body read back from the DER and from
; the PEM is the accepted body.
(assert-event (let ((c (fn-ssc-certificate *tsst-tbs* *tsst-sig*)))
                (and (equal (car c) :accepted)
                     (equal (fn-ssc-certificate-body (cadr c)) *tsst-tbs*))))
(assert-event (let ((p (fn-ssc-certificate-pem *tsst-tbs* *tsst-sig*)))
                (and (equal (car p) :accepted)
                     (equal (take 28 (cadr p))
                            (append (fn-record-string-octets "-----BEGIN CERTIFICATE-----")
                                    '(10)))
                     (equal (fn-ssc-certificate-body
                             (fn-ssc-pem-der *fn-ssc-certificate-label* (cadr p)))
                            *tsst-tbs*))))
; Hypothesis removal (the certificate refused): a signature that is not one
; SEQUENCE, and a body that is not one, are refused by name; nothing carries
; the body.
(assert-event (equal (fn-ssc-certificate-pem *tsst-tbs* '(2 1 5)) '(:refused :signature)))
(assert-event (equal (fn-ssc-certificate-pem (cdr *tsst-tbs*) *tsst-sig*) '(:refused :body)))
(assert-event (not (equal (fn-ssc-certificate-body
                           (fn-ssc-pem-der *fn-ssc-certificate-label*
                                           (cadr (fn-ssc-certificate-pem *tsst-tbs* '(2 1 5)))))
                          *tsst-tbs*)))
; Mutation (labelled): one base64 character of the PEM changed, the body read
; back is not the accepted one.
(assert-event (let* ((pem (cadr (fn-ssc-certificate-pem *tsst-tbs* *tsst-sig*)))
                     (bad (update-nth 100 (if (equal (nth 100 pem) 65) 66 65) pem)))
                (not (equal (fn-ssc-certificate-body
                             (fn-ssc-pem-der *fn-ssc-certificate-label* bad))
                            *tsst-tbs*))))

; fn-ssc-key-pem-carries-the-key: a one-SEQUENCE witness (no real key).
(assert-event (let ((p (fn-ssc-key-pem '(48 3 2 1 1))))
                (and (equal (car p) :accepted)
                     (equal (fn-ssc-pem-der *fn-ssc-ec-key-label* (cadr p)) '(48 3 2 1 1)))))
(assert-event (equal (fn-ssc-key-pem '(2 1 1)) '(:refused :key)))
