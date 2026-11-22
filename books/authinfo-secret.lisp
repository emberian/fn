; The AUTHINFO USER/PASS verifier selected by E2.  The historical
; fn-authsec-v2 credential carries a separate pair of SCRAM keys.  USER/PASS
; uses only the salt and the tagged BLAKE3 digest, as in fn1 AUTHINFO.
(in-package "ACL2")
(include-book "blake3-spec")
(include-book "declare")
(fn2-book-layer :e)

(defconst *fn2-authinfo-salt-octets* 16)
(defconst *fn2-authinfo-verifier-octets* 32)
(defconst *fn2-authinfo-tag-text* "fn-authinfo-v1")
; Canonical CBOR byte string header 0x40 + 14, then the 14 tag octets.
(defconst *fn2-authinfo-tag-octets* '(78 102 110 45 97 117 116 104 105 110 102 111 45 118 49))

(defun fn2-authinfo-secret-shapep (salt digest)
  (declare (xargs :guard t))
  (and (fn-b3-octet-listp salt) (equal (len salt) *fn2-authinfo-salt-octets*)
       (fn-b3-octet-listp digest) (equal (len digest) *fn2-authinfo-verifier-octets*)))

(defun fn2-authinfo-secret-model (salt secret)
  (declare (xargs :guard (true-listp salt)))
  (fn-blake3 (append *fn2-authinfo-tag-octets* salt secret)))

(defthm fn2-authinfo-secret-model-shape
  (and (fn-b3-octet-listp (fn2-authinfo-secret-model salt secret))
       (equal (len (fn2-authinfo-secret-model salt secret)) *fn2-authinfo-verifier-octets*)))
(in-theory (disable fn2-authinfo-secret-model fn2-authinfo-secret-shapep))
