; Row Q10a (PKT-403/409/588b): a self-signed TLS pair made by the image, no
; `openssl' binary.  ACL2 decides the certificate: it renders the X.509 v3
; TBSCertificate (RFC 5280 section 4.1) in DER (X.690 section 10) from the
; node's names, the clock reading, a validity in days, sixteen random octets
; and the public key the host generated, and it wraps the host's signature
; into the Certificate and both into PEM (RFC 7468).  The host generates the
; key pair (P-256), reads the random octets and the clock, signs the octets
; ACL2 hands it with ECDSA over SHA-256, and writes the files ACL2 renders
; (host/native/tls.lisp fnn-tls-self-signed-write).
;
; Keystones: fn-ssc-tlv-read-of-tlv (the DER framing reads back),
; fn-ssc-plan-body-is-one-sequence (an accepted body is one SEQUENCE) and
; fn-ssc-certificate-pem-carries-the-body (the PEM the host writes decodes
; to a Certificate whose first element is exactly the body ACL2 decided: the
; host's signature wrap cannot alter it).
(in-package "ACL2")
(include-book "native-config")
(include-book "nntp-responses")
(include-book "octet-text")
(include-book "sha256")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; DER framing.  One TLV: a one-octet tag, the definite length in its minimal
; form (short below 128, else 81 / 82 / 83 and one to three octets), the
; content.  2^24 is where the three-octet long form ends; a longer content is
; refused by name (:too-long), never truncated.

(defconst *fn-ssc-length-limit* 16777216)

(defun fn-ssc-octetp (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 256)))

(defun fn-ssc-length-octets (n)
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (cond ((< n 128) (list n))
          ((< n 256) (list 129 n))
          ((< n 65536) (list 130 (floor n 256) (mod n 256)))
          (t (list 131 (floor n 65536) (mod (floor n 256) 256) (mod n 256))))))

(defun fn-ssc-tlv (tag content)
  (declare (xargs :guard t))
  (cons tag (append (fn-ssc-length-octets (len content)) (true-list-fix content))))

(defthm fn-ssc-true-listp-of-tlv
  (true-listp (fn-ssc-tlv tag content))
  :rule-classes :type-prescription)

; The minimal definite length at the head of XS: (mv OK N REST).
(defun fn-ssc-read-length (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (mv nil 0 nil)
    (let ((b (car xs)) (ys (cdr xs)))
      (cond ((not (fn-ssc-octetp b)) (mv nil 0 nil))
            ((< b 128) (mv t b ys))
            ((and (equal b 129) (consp ys) (fn-ssc-octetp (car ys))
                  (<= 128 (car ys)))
             (mv t (car ys) (cdr ys)))
            ((and (equal b 130) (consp ys) (consp (cdr ys))
                  (fn-ssc-octetp (car ys)) (fn-ssc-octetp (cadr ys))
                  (<= 1 (car ys)))
             (mv t (+ (* 256 (car ys)) (cadr ys)) (cddr ys)))
            ((and (equal b 131) (consp ys) (consp (cdr ys)) (consp (cddr ys))
                  (fn-ssc-octetp (car ys)) (fn-ssc-octetp (cadr ys))
                  (fn-ssc-octetp (caddr ys)) (<= 1 (car ys)))
             (mv t (+ (* 65536 (car ys)) (* 256 (cadr ys)) (caddr ys)) (cdddr ys)))
            (t (mv nil 0 nil))))))

;   (TAG CONTENT REST), or NIL when XS does not begin with one DER TLV.
(defun fn-ssc-tlv-read (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (fn-ssc-octetp (car xs)))
      (mv-let (ok n ys) (fn-ssc-read-length (cdr xs))
        (if (and ok (true-listp ys) (<= n (len ys)))
            (list (car xs) (take n ys) (nthcdr n ys))
          nil))
    nil))

(local (defthm fn-ssc-take-len-of-append
         (implies (true-listp a)
                  (equal (take (len a) (append a b)) a))))

(local (defthm fn-ssc-nthcdr-len-of-append
         (equal (nthcdr (len a) (append a b)) b)))

(local (defthm fn-ssc-floor-65536-is-floor-floor
         (implies (natp n)
                  (equal (floor (floor n 256) 256) (floor n 65536)))))

(local (defthm fn-ssc-three-octet-sum
         (implies (natp n)
                  (equal (+ (* 65536 (floor n 65536))
                            (* 256 (mod (floor n 256) 256))
                            (mod n 256))
                         n))
         :hints (("Goal" :use ((:instance floor-mod-elim (x n) (y 256))
                               (:instance floor-mod-elim (x (floor n 256)) (y 256)))
                  :in-theory (disable floor-mod-elim)))))

(local (defthm fn-ssc-read-length-of-length-octets
         (implies (and (natp n) (< n *fn-ssc-length-limit*))
                  (equal (fn-ssc-read-length (append (fn-ssc-length-octets n) ys))
                         (mv t n ys)))))

(local (defthm fn-ssc-len-of-true-list-fix
         (equal (len (true-list-fix x)) (len x))))

(local (defthm fn-ssc-append-assoc
         (equal (append (append a b) c) (append a (append b c)))))

(local (defthm fn-ssc-len-of-append
         (equal (len (append a b)) (+ (len a) (len b)))))

; KEYSTONE: the framing reads back.  What fn-ssc-tlv writes, followed by
; anything, is read as that tag, that content and the rest.
(defthm fn-ssc-tlv-read-of-tlv
  (implies (and (fn-ssc-octetp tag)
                (true-listp content)
                (true-listp rest)
                (< (len content) *fn-ssc-length-limit*))
           (equal (fn-ssc-tlv-read (append (fn-ssc-tlv tag content) rest))
                  (list tag content rest)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ssc-read-length fn-ssc-length-octets
                               (:e fn-ssc-length-octets))
           :use ((:instance fn-ssc-read-length-of-length-octets
                            (n (len content)) (ys (append content rest)))))))

(defun fn-ssc-one-sequencep (xs)
  (declare (xargs :guard t))
  (let ((r (fn-ssc-tlv-read xs)))
    (and (consp r) (equal (car r) 48) (null (caddr r)))))

; -----------------------------------------------------------------------------
; The node's names.  Each is an IPv4 or IPv6 literal (books/native-config.lisp
; reads both; the unspecified address is no one's name) or a DNS host name
; (RFC 1123 section 2.1: letters, digits and hyphens, labels of 1 to 63 with
; no hyphen at either end, 253 octets at most).  Each becomes one
; subjectAltName GeneralName (RFC 5280 section 4.2.1.6): iPAddress [7] or
; dNSName [2].

(defun fn-ssc-ldh-octetp (x)
  (declare (xargs :guard t))
  (and (natp x)
       (or (and (<= 97 x) (<= x 122)) (and (<= 65 x) (<= x 90))
           (and (<= 48 x) (<= x 57)) (equal x 45))))

(defun fn-ssc-dns-labels (xs n prev)
  (declare (xargs :guard (natp n) :measure (len xs)))
  (cond ((atom xs) (and (< 0 n) (not (equal prev 45))))
        ((equal (car xs) 46)
         (and (< 0 n) (not (equal prev 45)) (fn-ssc-dns-labels (cdr xs) 0 nil)))
        ((fn-ssc-ldh-octetp (car xs))
         (and (< n 63)
              (not (and (equal n 0) (equal (car xs) 45)))
              (fn-ssc-dns-labels (cdr xs) (+ 1 n) (car xs))))
        (t nil)))

(defun fn-ssc-dns-namep (xs)
  (declare (xargs :guard t))
  (and (consp xs) (true-listp xs) (<= (len xs) 253) (fn-ssc-dns-labels xs 0 nil)))

(defun fn-ssc-all-zerop (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (equal (car xs) 0) (fn-ssc-all-zerop (cdr xs))) t))

;   The GeneralName octets of NAME (a string), or NIL.
(defun fn-ssc-general-name (name)
  (declare (xargs :guard t))
  (if (not (stringp name))
      nil
    (let* ((xs (fn-record-string-octets name))
           (v4 (fn-native-config-ipv4-address xs)))
      (if (not (equal v4 :bad))
          (and (true-listp v4) (not (fn-ssc-all-zerop v4)) (fn-ssc-tlv 135 v4))
        (let ((v6 (fn-native-config-ipv6-literal xs)))
          (if (not (equal v6 :bad))
              (and (true-listp v6) (not (fn-ssc-all-zerop v6)) (fn-ssc-tlv 135 v6))
            (and (fn-ssc-dns-namep xs) (fn-ssc-tlv 130 xs))))))))

(defun fn-ssc-general-names (names)
  (declare (xargs :guard t))
  (if (consp names)
      (append (fn-ssc-general-name (car names)) (fn-ssc-general-names (cdr names)))
    nil))

(defun fn-ssc-names-okp (names)
  (declare (xargs :guard t))
  (if (consp names)
      (and (consp (fn-ssc-general-name (car names))) (fn-ssc-names-okp (cdr names)))
    (null names)))

; RFC 5280 appendix A.1: ub-common-name 64.
(defconst *fn-ssc-common-name-octets* 64)

; What a name list is refused for before any key is made (`mission' asks
; this before it writes fn.toml): NIL, or the reason.
(defun fn-ssc-names-refusal (names)
  (declare (xargs :guard t))
  (cond ((atom names) :no-names)
        ((not (fn-ssc-names-okp names)) :name)
        ((< *fn-ssc-common-name-octets*
            (len (fn-record-string-octets (car names))))
         :common-name-length)
        (t nil)))

; -----------------------------------------------------------------------------
; Validity (RFC 5280 section 4.1.2.5): UTCTime through 2049, GeneralizedTime
; from 2050, both in UTC to the second.  MS counts from 2000-01-01 (the DTN
; epoch, books/clock-wall-reading.lisp).  notBefore is an hour before the
; reading (a client's clock a little behind still accepts it); notAfter is
; DAYS later.  A year past 9999 cannot be written: refused as :days.

(defconst *fn-ssc-backdate-ms* 3600000)
(defconst *fn-ssc-day-ms* 86400000)

(defun fn-ssc-time (ms)
  (declare (xargs :guard t))
  (let* ((civil (fn-nntp-dtn-civil ms))
         (year (nfix (fn-nntp-civil-year civil)))
         (tail (append (fn-nntp-pad2 (fn-nntp-civil-month civil))
                       (fn-nntp-pad2 (fn-nntp-civil-day civil))
                       (fn-nntp-pad2 (fn-nntp-civil-hour civil))
                       (fn-nntp-pad2 (fn-nntp-civil-minute civil))
                       (fn-nntp-pad2 (fn-nntp-civil-second civil))
                       (list 90))))
    (if (< year 2050)
        (fn-ssc-tlv 23 (append (fn-nntp-pad2 (mod year 100)) tail))
      (fn-ssc-tlv 24 (append (fn-nntp-pad4 year) tail)))))

(defun fn-ssc-not-before-ms (now-ms)
  (declare (xargs :guard t))
  (nfix (- (nfix now-ms) *fn-ssc-backdate-ms*)))

(defun fn-ssc-not-after-ms (now-ms days)
  (declare (xargs :guard t))
  (+ (nfix now-ms) (* (nfix days) *fn-ssc-day-ms*)))

(defun fn-ssc-days-okp (now-ms days)
  (declare (xargs :guard t))
  (and (posp days)
       (<= (nfix (fn-nntp-civil-year
                  (fn-nntp-dtn-civil (fn-ssc-not-after-ms now-ms days))))
           *fn-nntp-max-rendered-year*)))

; -----------------------------------------------------------------------------
; The public key: the host's i2d_PUBKEY, a SubjectPublicKeyInfo for an EC
; key on P-256 (RFC 5480 section 2), the only key this signs with.

(defconst *fn-ssc-ec-p256-algorithm*
  ; SEQUENCE { id-ecPublicKey 1.2.840.10045.2.1, prime256v1 1.2.840.10045.3.1.7 }
  '(48 19 6 7 42 134 72 206 61 2 1 6 8 42 134 72 206 61 3 1 7))

(defconst *fn-ssc-ecdsa-sha256*
  ; AlgorithmIdentifier ecdsa-with-SHA256 1.2.840.10045.4.3.2, no parameters
  ; (RFC 5758 section 3.2).
  '(48 10 6 8 42 134 72 206 61 4 3 2))

;   The subjectPublicKey BIT STRING's key octets (after the unused-bits
;   octet), or NIL when SPKI is not one P-256 SubjectPublicKeyInfo.
(defun fn-ssc-spki-key (spki)
  (declare (xargs :guard t))
  (let ((outer (fn-ssc-tlv-read spki)))
    (and (consp outer) (equal (car outer) 48) (null (caddr outer))
         (let ((alg (fn-ssc-tlv-read (cadr outer))))
           (and (consp alg)
                (equal (fn-ssc-tlv (car alg) (cadr alg)) *fn-ssc-ec-p256-algorithm*)
                (let ((bits (fn-ssc-tlv-read (caddr alg))))
                  (and (consp bits) (equal (car bits) 3) (null (caddr bits))
                       (consp (cadr bits)) (equal (car (cadr bits)) 0)
                       (consp (cdr (cadr bits)))
                       (cdr (cadr bits)))))))))

; The key identifier: RFC 7093 section 2 method 1, the leftmost 160 bits of
; the SHA-256 of the subjectPublicKey's octets.
(defun fn-ssc-key-id (key)
  (declare (xargs :guard t))
  (take 20 (fn-sha256 key)))

; -----------------------------------------------------------------------------
; The TBSCertificate.

(defun fn-ssc-name (cn)
  ; Name ::= SEQUENCE { SET { SEQUENCE { id-at-commonName, UTF8String } } }
  (declare (xargs :guard t))
  (fn-ssc-tlv 48 (fn-ssc-tlv 49 (fn-ssc-tlv 48 (append '(6 3 85 4 3)
                                                       (fn-ssc-tlv 12 cn))))))

(defun fn-ssc-extension (oid critical value)
  (declare (xargs :guard t))
  (fn-ssc-tlv 48 (append (true-list-fix oid) (if critical '(1 1 255) nil) (fn-ssc-tlv 4 value))))

(defun fn-ssc-extensions (names key-id)
  ; [3] EXPLICIT Extensions: basicConstraints CA:TRUE (critical), keyUsage
  ; digitalSignature + keyCertSign (critical), subjectKeyIdentifier,
  ; authorityKeyIdentifier (the same key), subjectAltName.
  (declare (xargs :guard t))
  (fn-ssc-tlv 163
              (fn-ssc-tlv 48
                          (append (fn-ssc-extension '(6 3 85 29 19) t '(48 3 1 1 255))
                                  (fn-ssc-extension '(6 3 85 29 15) t '(3 2 2 132))
                                  (fn-ssc-extension '(6 3 85 29 14) nil
                                                    (fn-ssc-tlv 4 key-id))
                                  (fn-ssc-extension '(6 3 85 29 35) nil
                                                    (fn-ssc-tlv 48 (fn-ssc-tlv 128 key-id)))
                                  (fn-ssc-extension '(6 3 85 29 17) nil
                                                    (fn-ssc-tlv 48 (fn-ssc-general-names names)))))))

; The serial: sixteen host-random octets, the first made 64 + its low six
; bits, so the INTEGER is positive, minimal and 16 octets (RFC 5280 section
; 4.1.2.2: at most 20).
(defconst *fn-ssc-serial-octets* 16)

(defun fn-ssc-serial-okp (serial)
  (declare (xargs :guard t))
  (and (true-listp serial) (fn-cbor-octet-listp serial)
       (equal (len serial) *fn-ssc-serial-octets*)))

(defun fn-ssc-serial (serial)
  (declare (xargs :guard t))
  (if (consp serial)
      (fn-ssc-tlv 2 (cons (+ 64 (mod (nfix (car serial)) 64)) (true-list-fix (cdr serial))))
    (fn-ssc-tlv 2 '(1))))

(defun fn-ssc-tbs-content (names now-ms days serial spki)
  (declare (xargs :guard t))
  (let ((cn (fn-record-string-octets (if (consp names) (car names) ""))))
                (append '(160 3 2 1 2)            ; version v3
                        (fn-ssc-serial serial)
                        *fn-ssc-ecdsa-sha256*
                        (fn-ssc-name cn)          ; issuer = subject
                        (fn-ssc-tlv 48 (append (fn-ssc-time (fn-ssc-not-before-ms now-ms))
                                               (fn-ssc-time (fn-ssc-not-after-ms now-ms days))))
                        (fn-ssc-name cn)
                        (true-list-fix spki)
                        (fn-ssc-extensions names (fn-ssc-key-id (fn-ssc-spki-key spki))))))

(defun fn-ssc-tbs (names now-ms days serial spki)
  (declare (xargs :guard t))
  (fn-ssc-tlv 48 (fn-ssc-tbs-content names now-ms days serial spki)))

;   (:accepted TBS)  the octets the host signs
;   (:refused REASON)  :no-names :name :common-name-length :clock :days
;                      :serial :spki :too-long
; NAMES are strings, the first the subject's common name; NOW-MS and
; HAS-WALL the host's wall reading (fn-otm-wall-reading); DAYS the validity;
; SERIAL sixteen random octets; SPKI the generated public key.
(defun fn-ssc-plan (names days now-ms has-wall serial spki)
  (declare (xargs :guard t))
  (let ((names-refusal (fn-ssc-names-refusal names)))
    (cond (names-refusal (list :refused names-refusal))
          ((not (and has-wall (natp now-ms))) (list :refused :clock))
          ((not (fn-ssc-days-okp now-ms days)) (list :refused :days))
          ((not (fn-ssc-serial-okp serial)) (list :refused :serial))
          ((not (and (true-listp spki) (fn-ssc-spki-key spki))) (list :refused :spki))
          ((not (< (len (fn-ssc-tbs-content names now-ms days serial spki))
                   *fn-ssc-length-limit*))
           (list :refused :too-long))
          (t (list :accepted (fn-ssc-tbs names now-ms days serial spki))))))

(defthm fn-ssc-true-listp-of-tbs-content
  (true-listp (fn-ssc-tbs-content names now-ms days serial spki)))

; KEYSTONE: an accepted body is one DER SEQUENCE, read back as itself.
(defthm fn-ssc-plan-body-is-one-sequence
  (let ((plan (fn-ssc-plan names days now-ms has-wall serial spki)))
    (implies (equal (car plan) :accepted)
             (and (fn-ssc-one-sequencep (cadr plan))
                  (equal (fn-ssc-tlv 48 (cadr (fn-ssc-tlv-read (cadr plan))))
                         (cadr plan)))))
  :hints (("Goal" :in-theory (disable fn-ssc-tbs-content fn-ssc-tlv fn-ssc-tlv-read
                                      fn-ssc-names-refusal fn-ssc-days-okp
                                      fn-ssc-spki-key fn-ssc-serial-okp)
           :use ((:instance fn-ssc-tlv-read-of-tlv
                            (tag 48) (rest nil)
                            (content (fn-ssc-tbs-content names now-ms days serial spki)))))))

(in-theory (disable fn-ssc-tbs-content))

; -----------------------------------------------------------------------------
; The Certificate (RFC 5280 section 4.1): SEQUENCE { tbsCertificate,
; signatureAlgorithm, signatureValue BIT STRING }.  SIG is the host's
; EVP_DigestSignFinal output over TBS: an ECDSA-Sig-Value, one SEQUENCE.

;   (:accepted DER) | (:refused :body | :signature | :too-long)
(defun fn-ssc-certificate (tbs sig)
  (declare (xargs :guard t))
  (cond ((not (and (fn-cbor-octet-listp tbs) (fn-ssc-one-sequencep tbs)))
         (list :refused :body))
        ((not (and (fn-cbor-octet-listp sig) (fn-ssc-one-sequencep sig)))
         (list :refused :signature))
        (t (let ((content (append tbs *fn-ssc-ecdsa-sha256*
                                  (fn-ssc-tlv 3 (cons 0 sig)))))
             (if (< (len content) *fn-ssc-length-limit*)
                 (list :accepted (fn-ssc-tlv 48 content))
               (list :refused :too-long))))))

; The certificate's first element, re-encoded: what a verifier hashes.
(defun fn-ssc-certificate-body (der)
  (declare (xargs :guard t))
  (let* ((outer (fn-ssc-tlv-read der))
         (first (fn-ssc-tlv-read (cadr outer))))
    (fn-ssc-tlv (car first) (cadr first))))

; What the reader accepts is exactly what the writer wrote (DER's minimal
; lengths make the reading canonical).
(local (defthm fn-ssc-length-octets-of-read-length
         (mv-let (ok n ys) (fn-ssc-read-length xs)
           (implies ok
                    (and (natp n) (< n *fn-ssc-length-limit*)
                         (equal (append (fn-ssc-length-octets n) ys) xs))))
         :hints (("Goal" :in-theory (enable fn-ssc-read-length)))))

(local (defthm fn-ssc-append-take-nthcdr
         (implies (and (true-listp ys) (<= n (len ys)) (natp n))
                  (equal (append (take n ys) (nthcdr n ys)) ys))))

(local (defthm fn-ssc-len-of-take
         (equal (len (take n x)) (nfix n))))

(defthm fn-ssc-tlv-of-tlv-read
  (let ((r (fn-ssc-tlv-read xs)))
    (implies r
             (and (equal (append (fn-ssc-tlv (car r) (cadr r)) (caddr r)) xs)
                  (fn-ssc-octetp (car r))
                  (true-listp (cadr r))
                  (true-listp (caddr r))
                  (< (len (cadr r)) *fn-ssc-length-limit*))))
  :hints (("Goal" :in-theory (disable fn-ssc-read-length fn-ssc-length-octets)
           :use ((:instance fn-ssc-length-octets-of-read-length (xs (cdr xs)))))))

(defthm fn-ssc-one-sequencep-shape
  (implies (fn-ssc-one-sequencep xs)
           (and (equal (fn-ssc-tlv 48 (cadr (fn-ssc-tlv-read xs))) xs)
                (true-listp xs)))
  :hints (("Goal" :use ((:instance fn-ssc-tlv-of-tlv-read)))))

(defthm fn-ssc-tlv-read-of-tlv-alone
  (implies (and (fn-ssc-octetp tag)
                (true-listp content)
                (< (len content) *fn-ssc-length-limit*))
           (equal (fn-ssc-tlv-read (fn-ssc-tlv tag content))
                  (list tag content nil)))
  :hints (("Goal" :use ((:instance fn-ssc-tlv-read-of-tlv (rest nil)))
           :in-theory (disable fn-ssc-tlv-read-of-tlv fn-ssc-tlv fn-ssc-tlv-read))))

; One whole TLV followed by anything reads as itself and the rest.
(defthm fn-ssc-tlv-read-of-append-whole
  (let ((r (fn-ssc-tlv-read xs)))
    (implies (and r (null (caddr r)) (true-listp rest))
             (equal (fn-ssc-tlv-read (append xs rest))
                    (list (car r) (cadr r) rest))))
  :hints (("Goal" :in-theory (disable fn-ssc-tlv fn-ssc-tlv-read fn-ssc-tlv-read-of-tlv)
           :use ((:instance fn-ssc-tlv-of-tlv-read)
                 (:instance fn-ssc-tlv-read-of-tlv
                            (tag (car (fn-ssc-tlv-read xs)))
                            (content (cadr (fn-ssc-tlv-read xs))))))))

; KEYSTONE: the certificate carries the decided body.  An accepted
; certificate's first element is TBS, octet for octet.
(defthm fn-ssc-certificate-carries-the-body
  (let ((c (fn-ssc-certificate tbs sig)))
    (implies (equal (car c) :accepted)
             (equal (fn-ssc-certificate-body (cadr c)) tbs)))
  :hints (("Goal" :in-theory (disable fn-ssc-tlv fn-ssc-tlv-read fn-ssc-tlv-read-of-tlv)
           :use ((:instance fn-ssc-one-sequencep-shape (xs tbs))
                 (:instance fn-ssc-tlv-read-of-append-whole
                            (xs tbs)
                            (rest (append *fn-ssc-ecdsa-sha256*
                                          (fn-ssc-tlv 3 (cons 0 sig)))))))))

; -----------------------------------------------------------------------------
; PEM (RFC 7468 section 2): the label's pre- and post-encapsulation
; boundaries around the base64 text in lines of 64.

(local (defthm fn-ssc-nthcdr-of-atom
         (implies (atom x) (equal (nthcdr n x) (if (zp n) x nil)))))

(local (defthm fn-ssc-len-of-nthcdr
         (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))))

(local (defthm fn-ssc-true-listp-of-b64-encode
         (true-listp (fn-ot-b64-encode xs))
         :hints (("Goal" :use ((:instance fn-ot-octet-listp-of-b64-encode))))))

(defun fn-ssc-lines (xs)
  (declare (xargs :guard (true-listp xs) :measure (len xs)))
  (cond ((atom xs) nil)
        ((<= (len xs) 64) (append xs (list 10)))
        (t (append (take 64 xs) (cons 10 (fn-ssc-lines (nthcdr 64 xs)))))))

(defun fn-ssc-unlines (ys)
  (declare (xargs :guard (true-listp ys) :measure (len ys)))
  (cond ((atom ys) nil)
        ((<= (len ys) 65) (take (+ -1 (len ys)) ys))
        (t (append (take 64 ys) (fn-ssc-unlines (nthcdr 65 ys))))))

(defun fn-ssc-pem-begin (label)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "-----BEGIN ") (true-list-fix label)
          (fn-record-string-octets "-----") (list 10)))

(defun fn-ssc-pem-end (label)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "-----END ") (true-list-fix label)
          (fn-record-string-octets "-----") (list 10)))

(defun fn-ssc-pem (label der)
  (declare (xargs :guard t))
  (append (fn-ssc-pem-begin label)
          (fn-ssc-lines (fn-ot-b64-encode der))
          (fn-ssc-pem-end label)))

; The reader of what fn-ssc-pem writes: the boundaries dropped, the lines
; joined, the base64 decoded.
(defun fn-ssc-pem-der (label pem)
  (declare (xargs :guard t))
  (let* ((body (nthcdr (len (fn-ssc-pem-begin label)) (true-list-fix pem)))
         (text (take (nfix (- (len body) (len (fn-ssc-pem-end label)))) body)))
    (mv-let (err der) (fn-ot-b64-decode (fn-ssc-unlines text))
      (declare (ignore err))
      der)))

(defconst *fn-ssc-certificate-label* '(67 69 82 84 73 70 73 67 65 84 69))
(defconst *fn-ssc-ec-key-label* '(69 67 32 80 82 73 86 65 84 69 32 75 69 89))

;   (:accepted PEM) | (:refused REASON): the certificate file's octets.
(defun fn-ssc-certificate-pem (tbs sig)
  (declare (xargs :guard t))
  (let ((c (fn-ssc-certificate tbs sig)))
    (if (equal (car c) :accepted)
        (list :accepted (fn-ssc-pem *fn-ssc-certificate-label* (cadr c)))
      c)))

;   (:accepted PEM) | (:refused :key): the key file's octets.  DER is the
;   host's i2d_PrivateKey of the generated key, an ECPrivateKey (RFC 5915).
(defun fn-ssc-key-pem (der)
  (declare (xargs :guard t))
  (if (and (fn-cbor-octet-listp der) (fn-ssc-one-sequencep der))
      (list :accepted (fn-ssc-pem *fn-ssc-ec-key-label* der))
    (list :refused :key)))

(local (defthm fn-ssc-take-of-append-by-len
         (implies (and (true-listp a) (equal (len a) n))
                  (equal (take n (append a b)) a))))

(local (defthm fn-ssc-nthcdr-of-append-by-len
         (implies (equal (len a) n)
                  (equal (nthcdr n (append a b)) b))))

(local (defthm fn-ssc-nthcdr-of-append
         (implies (natp n)
                  (equal (nthcdr n (append a b))
                         (if (<= n (len a))
                             (append (nthcdr n a) b)
                           (nthcdr (- n (len a)) b))))))

(local (defthm fn-ssc-consp-of-nthcdr
         (implies (and (natp n) (< n (len x)))
                  (consp (nthcdr n x)))))

(local (defthm fn-ssc-consp-of-lines
         (equal (consp (fn-ssc-lines xs)) (consp xs))))

(local (defthm fn-ssc-true-listp-of-take
         (true-listp (take n x))))

(defthm fn-ssc-unlines-of-lines
  (implies (true-listp xs)
           (equal (fn-ssc-unlines (fn-ssc-lines xs)) xs))
  :hints (("Goal" :induct (fn-ssc-lines xs))))

(local (defthm fn-ssc-true-listp-of-lines
         (true-listp (fn-ssc-lines xs))))


(local (defthm fn-ssc-true-listp-of-pem-end
         (true-listp (fn-ssc-pem-end label))))

(local (defthm fn-ssc-true-list-fix-of-true-list
         (implies (true-listp x) (equal (true-list-fix x) x))))

; The PEM that fn-ssc-pem writes decodes to its DER.
(defthm fn-ssc-pem-der-of-pem
  (implies (fn-cbor-octet-listp der)
           (equal (fn-ssc-pem-der label (fn-ssc-pem label der)) der))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ssc-lines fn-ssc-unlines fn-ot-b64-encode
                               fn-ot-b64-decode fn-ssc-pem-begin fn-ssc-pem-end
                               fn-ssc-nthcdr-of-append))))

(local (defthm fn-ssc-octet-listp-of-append
         (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
                  (fn-cbor-octet-listp (append a b)))))

(local (defthm fn-ssc-octet-listp-of-length-octets
         (implies (and (natp n) (< n *fn-ssc-length-limit*))
                  (fn-cbor-octet-listp (fn-ssc-length-octets n)))
         :hints (("Goal" :in-theory (disable |(mod (floor x y) z)|)))))

(defthm fn-ssc-octet-listp-of-tlv
  (implies (and (fn-ssc-octetp tag) (fn-cbor-octet-listp content)
                (< (len content) *fn-ssc-length-limit*))
           (fn-cbor-octet-listp (fn-ssc-tlv tag content)))
  :hints (("Goal" :in-theory (disable fn-ssc-length-octets))))

(local (defthm fn-ssc-len-of-tlv-bound
         (< (len content) (len (fn-ssc-tlv tag content)))
         :rule-classes :linear))

(defthm fn-ssc-certificate-octets
  (let ((c (fn-ssc-certificate tbs sig)))
    (implies (equal (car c) :accepted)
             (fn-cbor-octet-listp (cadr c))))
  :hints (("Goal" :in-theory (disable fn-ssc-tlv fn-ssc-one-sequencep)
           :use ((:instance fn-ssc-octet-listp-of-tlv (tag 3) (content (cons 0 sig)))
                 (:instance fn-ssc-octet-listp-of-tlv
                            (tag 48)
                            (content (append tbs *fn-ssc-ecdsa-sha256*
                                             (fn-ssc-tlv 3 (cons 0 sig)))))))))

; KEYSTONE: the certificate file carries the decided body.  The PEM the
; host writes for an accepted certificate decodes to a Certificate whose
; first element is TBS, the body fn-ssc-plan accepted and the host signed.
(defthm fn-ssc-certificate-pem-carries-the-body
  (let ((p (fn-ssc-certificate-pem tbs sig)))
    (implies (equal (car p) :accepted)
             (equal (fn-ssc-certificate-body
                     (fn-ssc-pem-der *fn-ssc-certificate-label* (cadr p)))
                    tbs)))
  :hints (("Goal" :in-theory (disable fn-ssc-certificate fn-ssc-pem fn-ssc-pem-der
                                      fn-ssc-certificate-body)
           :use ((:instance fn-ssc-certificate-carries-the-body)
                 (:instance fn-ssc-certificate-octets)
                 (:instance fn-ssc-pem-der-of-pem
                            (label *fn-ssc-certificate-label*)
                            (der (cadr (fn-ssc-certificate tbs sig))))))))

; The key file decodes to the host's key octets.
(defthm fn-ssc-key-pem-carries-the-key
  (let ((p (fn-ssc-key-pem der)))
    (implies (equal (car p) :accepted)
             (equal (fn-ssc-pem-der *fn-ssc-ec-key-label* (cadr p)) der)))
  :hints (("Goal" :in-theory (disable fn-ssc-pem fn-ssc-pem-der fn-ssc-one-sequencep)
           :use ((:instance fn-ssc-pem-der-of-pem (label *fn-ssc-ec-key-label*))))))

(in-theory (disable fn-ssc-plan fn-ssc-certificate fn-ssc-certificate-pem
                    fn-ssc-key-pem fn-ssc-pem fn-ssc-pem-der fn-ssc-tlv-read
                    fn-ssc-tlv fn-ssc-names-refusal))
