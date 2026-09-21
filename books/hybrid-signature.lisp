; fn: selected D09 hybrid signature profile for exact authored source octets.
;
; ACL2 owns the algorithm identifiers, fixed component widths, canonical signed
; preimage, and the conjunction which turns primitive observations into an
; authorization verdict.  The primitive implementations remain trusted under
; A-CRYPTO.  Key generation and custody are deliberately outside this book.

(in-package "ACL2")
(include-book "crypto-seam")
(include-book "article")
(include-book "hybrid-profile")

(local (in-theory (enable fn-cbor-codec-vocabulary
                          fn-record-invariants-vocabulary)))

(defconst *fn-hsig-version* 1)
(defconst *fn-hsig-suite* 1)
(defconst *fn-hsig-ed25519-algorithm* 1)
(defconst *fn-hsig-ml-dsa-65-algorithm* 2)
(defconst *fn-hsig-ed25519-public-key-octets* 32)
(defconst *fn-hsig-ed25519-signature-octets* 64)
(defconst *fn-hsig-ml-dsa-65-public-key-octets* 1952)
(defconst *fn-hsig-ml-dsa-65-signature-octets* 3309)
(defconst *fn-hsig-domain-tag*
  '(102 110 45 97 117 116 104 111 114 101 100 45 115 111 117 114 99 101
    45 104 121 98 114 105 100 45 118 49)) ; fn-authored-source-hybrid-v1

(defun fn-hsig-exact-octets-p (x n)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x) (equal (len x) n)))

(defun fn-hsig-keyset-p (keys)
  (declare (xargs :guard t))
  (and (true-listp keys)
       (equal (len keys) 2)
       (equal (fn-cbor-ag-car (fn-cbor-ag-car keys)) :ed25519)
       (fn-hsig-exact-octets-p (fn-cbor-ag-cdr (fn-cbor-ag-car keys))
                               *fn-hsig-ed25519-public-key-octets*)
       (equal (fn-cbor-ag-car (fn-cbor-ag-car (fn-cbor-ag-cdr keys))) :ml-dsa-65)
       (fn-hsig-exact-octets-p (fn-cbor-ag-cdr (fn-cbor-ag-car (fn-cbor-ag-cdr keys)))
                               *fn-hsig-ml-dsa-65-public-key-octets*)))

(defun fn-hsig-signatures-p (signatures)
  (declare (xargs :guard t))
  (and (true-listp signatures)
       (equal (len signatures) 2)
       (equal (fn-cbor-ag-car (fn-cbor-ag-car signatures)) :ed25519)
       (fn-hsig-exact-octets-p (fn-cbor-ag-cdr (fn-cbor-ag-car signatures))
                               *fn-hsig-ed25519-signature-octets*)
       (equal (fn-cbor-ag-car (fn-cbor-ag-car (fn-cbor-ag-cdr signatures))) :ml-dsa-65)
       (fn-hsig-exact-octets-p (fn-cbor-ag-cdr (fn-cbor-ag-car (fn-cbor-ag-cdr signatures)))
                               *fn-hsig-ml-dsa-65-signature-octets*)))

(defun fn-hsig-subject-p (principal keys source)
  (declare (xargs :guard t))
  (and (fn-hsig-exact-octets-p principal 32)
       (fn-hsig-keyset-p keys)
       (fn-cbor-octet-listp source)
       (<= (len source) *fn-article-max-octets*)))

(defun fn-hsig-subject-body (principal keys source)
  (declare (xargs :guard (fn-hsig-subject-p principal keys source)))
  ;; Fixed-width fields make the enrolled key set self-delimiting; the final
  ;; u16 makes even an empty or suffix-related authored source unambiguous.
  (append (list *fn-hsig-version* *fn-hsig-suite*)
          principal
          (list *fn-hsig-ed25519-algorithm*)
          (fn-cbor-ag-cdr (fn-cbor-ag-car keys))
          (list *fn-hsig-ml-dsa-65-algorithm*)
          (fn-cbor-ag-cdr (fn-cbor-ag-car (fn-cbor-ag-cdr keys)))
          (fn-cbor-u16-bytes (len source))
          source))

(local
 (defthm fn-hsig-octets-append
   (implies (and (fn-cbor-octet-listp a)
                 (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))
   :hints (("Goal" :induct (fn-cbor-octet-listp a)))))

(defthm fn-hsig-subject-body-is-octets
  (implies (fn-hsig-subject-p principal keys source)
           (fn-cbor-octet-listp (fn-hsig-subject-body principal keys source)))
  :hints (("Goal"
           :in-theory (e/d (fn-hsig-subject-p fn-hsig-keyset-p
                            fn-hsig-exact-octets-p fn-hsig-subject-body
                            fn-hsig-octets-append
                            fn-cbor-octet-listp fn-cbor-octetp)
                           (fn-cbor-u16-bytes))
           :use ((:instance fn-cbor-u16-bytes-are-octets
                            (n (len source)))))))

(defun fn-hsig-signed-preimage (principal keys source)
  (declare (xargs :guard (fn-hsig-subject-p principal keys source)
                  :guard-hints
                  (("Goal" :use fn-hsig-subject-body-is-octets
                    :in-theory (disable fn-hsig-subject-body-is-octets)))))
  (fn-digest-tagged-preimage *fn-hsig-domain-tag*
                             (fn-hsig-subject-body principal keys source)))

; This is the authorization subject the native host calls after it has asked
; both primitive libraries to verify the single ACL2-produced preimage.
(defun fn-hsig-authorize (principal keys source signatures
                                    observed-ml-public-key
                                    ed25519-observation ml-dsa-65-observation)
  (declare (xargs :guard t))
  (and (fn-hsig-subject-p principal keys source)
       (fn-hsig-signatures-p signatures)
       (equal observed-ml-public-key
              (fn-cbor-ag-cdr (fn-cbor-ag-car (fn-cbor-ag-cdr keys))))
       (equal ed25519-observation :verified)
       (equal ml-dsa-65-observation :verified)))

(defthm fn-hsig-authorization-requires-both-components-by-definition
  (implies (fn-hsig-authorize principal keys source signatures observed ed ml)
           (and (equal ed :verified) (equal ml :verified)))
  :rule-classes nil)

(defthm fn-hsig-authorization-binds-complete-profile-by-definition
  (implies (fn-hsig-authorize principal keys source signatures observed ed ml)
           (and (fn-hsig-subject-p principal keys source)
                (fn-hsig-keyset-p keys)
                (fn-hsig-signatures-p signatures)))
  :rule-classes nil)

(defthm fn-hsig-authorization-binds-observed-ml-key-by-definition
  (implies (fn-hsig-authorize principal keys source signatures observed ed ml)
           (equal observed
                  (fn-cbor-ag-cdr
                   (fn-cbor-ag-car (fn-cbor-ag-cdr keys)))))
  :rule-classes nil)

(in-theory (disable (:d fn-hsig-exact-octets-p)
                    (:d fn-hsig-keyset-p) (:d fn-hsig-signatures-p)
                    (:d fn-hsig-subject-p) (:d fn-hsig-subject-body)
                    (:d fn-hsig-signed-preimage) (:d fn-hsig-authorize)))

(deftheory fn-hybrid-signature-vocabulary
  '(fn-hsig-exact-octets-p fn-hsig-keyset-p fn-hsig-signatures-p
    fn-hsig-subject-p fn-hsig-subject-body fn-hsig-signed-preimage
    fn-hsig-authorize))
