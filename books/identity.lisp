; fn: content identity and charge policy, owned by ACL2.
;
; The v1 identity profile of `specs/encoding.md`, adopted.  Every content
; identity in the system is
;
;     subject-v1    = SHA-256("fn/subject/v1" || 0x00
;                             || uint32-be(len(payload)) || payload)
;     obligation-v1 = SHA-256("fn/obligation/v1" || 0x00
;                             || uint32-be(len(msgid)) || msgid
;                             || uint32-be(len(subject)) || subject)
;
; and the identity itself is the triple (label-octets, algorithm-id, digest)
; rendered canonically by `fn-id-render`:
;
;     identity = label || 0x00 || version-octet || algorithm-octet || digest
;
; so the kind is carried inside the encoded identity rather than as a hex
; prefix, and the algorithm identifier travels in the container.  Changing the
; hash suite (D09) changes the algorithm octet; it does not change the meaning
; of an identity already written.  Every variable field in a preimage is
; length-prefixed, so no pair of different kinds and no pair of different
; (msgid, subject) splits can share a preimage by construction; ENC-003 is met
; rather than deferred.
;
; The canonical identity is OCTETS.  `fn-id-text` renders it as lowercase
; hexadecimal, whole and label included, and is used only where a string is
; unavoidable: the store record's metadata fields, the workflow journal's JSON
; records and the NNTP header value.  Nothing else renders an identity, and
; the rendering is proved invertible, so a string comparison at one of those
; boundaries is an octet comparison and, by injectivity, a digest comparison.
;
; The digest itself is A-CRYPTO, exactly as in `books/frame.lisp`: the host
; supplies 32 octets and ACL2 owns everything around them.  The functions that
; take a digest are executable and guard verified; `fn-id-subject-of-payload`
; and `fn-id-obligation-of` state the same identities against the constrained
; `fn-frame-digest` so that a theorem can mention the assumption it rests on.
;
; There is exactly one derivation.  The pre-v1 `"sha256:"+hex` and
; `"archive:"+hex` derivation is gone, not kept beside this one: a store
; written under it is refused at open by its configuration format
; (`books/store-config.lisp`, `fn-store-experiment-5`) rather than misread.

(in-package "ACL2")
(include-book "frame")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Lowercase hexadecimal

(defun fn-id-hex-digit (n)
  (declare (xargs :guard (and (natp n) (< n 16))))
  (if (< n 10) (+ 48 n) (+ 87 n)))

(defun fn-id-hex-digitp (octet)
  (declare (xargs :guard t))
  (or (and (natp octet) (<= 48 octet) (<= octet 57))
      (and (natp octet) (<= 97 octet) (<= octet 102))))

(defun fn-id-hex-value (octet)
  (declare (xargs :guard (fn-id-hex-digitp octet)))
  (if (<= octet 57) (- octet 48) (- octet 87)))

(defun fn-id-hex-octets (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (if (consp octets)
      (cons (fn-id-hex-digit (floor (car octets) 16))
            (cons (fn-id-hex-digit (mod (car octets) 16))
                  (fn-id-hex-octets (cdr octets))))
    nil))

(defun fn-id-hex-listp (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (and (fn-id-hex-digitp (car octets))
           (fn-id-hex-listp (cdr octets)))
    (null octets)))

(defun fn-id-unhex (octets)
  ; Inverse of `fn-id-hex-octets` on an even-length lowercase hex list.
  (declare (xargs :guard (fn-id-hex-listp octets) :verify-guards nil))
  (if (and (consp octets) (consp (cdr octets)))
      (cons (+ (* 16 (fn-id-hex-value (car octets)))
               (fn-id-hex-value (car (cdr octets))))
            (fn-id-unhex (cdr (cdr octets))))
    nil))

(verify-guards fn-id-unhex)

; -----------------------------------------------------------------------------
; The v1 profile: labels, version, algorithm

(defconst *fn-id-subject-label*                          ; "fn/subject/v1"
  '(102 110 47 115 117 98 106 101 99 116 47 118 49))
(defconst *fn-id-obligation-label*                       ; "fn/obligation/v1"
  '(102 110 47 111 98 108 105 103 97 116 105 111 110 47 118 49))

; The one octet that terminates a label in both a preimage and an identity.
(defconst *fn-id-separator* 0)

; The profile version and the hash suite, carried in the container.
(defconst *fn-id-version* 1)
(defconst *fn-id-algorithm-sha256* 1)

; label || separator || version || algorithm, then the digest.
(defconst *fn-id-header-octets* 3)
(defconst *fn-id-digest-octets* 32)
(defconst *fn-id-subject-octets* 48)     ; 13 + 3 + 32
(defconst *fn-id-obligation-octets* 51)  ; 16 + 3 + 32

(defun fn-id-digestp (xs)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp xs)
       (equal (len xs) *fn-id-digest-octets*)))

; -----------------------------------------------------------------------------
; Preimages.  Every variable field is preceded by its length as four
; big-endian octets -- the same `fn-cbor-u32-bytes` the frame grammar uses --
; so the fields of a preimage can be read back rather than guessed at from a
; separator that a field might itself contain.

(defun fn-id-subject-prefix (length)
  ; The fixed head of a subject preimage.  The host appends the payload to
  ; this and hashes; the payload never crosses the bridge, exactly as with
  ; `fn-frame-inbound-prefix`.
  (declare (xargs :guard (and (natp length) (<= length *fn-cbor-max-uint*))))
  (append *fn-id-subject-label*
          (cons *fn-id-separator* (fn-cbor-u32-bytes length))))

(defun fn-id-subject-preimage (payload)
  ; The exact bytes the subject digest covers.
  (declare (xargs :guard (and (fn-cbor-octet-listp payload)
                              (<= (len payload) *fn-cbor-max-uint*))))
  (append (fn-id-subject-prefix (len payload)) payload))

(defun fn-id-obligation-preimage (msgid subject)
  ; The exact bytes the obligation digest covers.  Both variable fields are
  ; length-prefixed, so the Message-ID cannot run into the subject identity
  ; whatever octets either of them contains.
  (declare (xargs :guard (and (fn-cbor-octet-listp msgid)
                              (<= (len msgid) *fn-cbor-max-uint*)
                              (fn-cbor-octet-listp subject)
                              (<= (len subject) *fn-cbor-max-uint*))))
  (append *fn-id-obligation-label*
          (cons *fn-id-separator*
                (append (fn-cbor-u32-bytes (len msgid))
                        (append msgid
                                (append (fn-cbor-u32-bytes (len subject))
                                        subject))))))

; -----------------------------------------------------------------------------
; The canonical identity rendering

(defun fn-id-render (label digest)
  ; (label-octets, algorithm-id, digest-octets), canonically: the label, the
  ; separator, the profile version octet, the algorithm octet, the digest.
  (declare (xargs :guard (and (fn-cbor-octet-listp label)
                              (fn-id-digestp digest))))
  (append label
          (cons *fn-id-separator*
                (cons *fn-id-version*
                      (cons *fn-id-algorithm-sha256* digest)))))

(defun fn-id-subject (digest)
  ; The host entry point: `digest` is SHA-256 of the subject preimage.
  (declare (xargs :guard (fn-id-digestp digest)))
  (fn-id-render *fn-id-subject-label* digest))

(defun fn-id-obligation (digest)
  ; The host entry point: `digest` is SHA-256 of the obligation preimage.
  (declare (xargs :guard (fn-id-digestp digest)))
  (fn-id-render *fn-id-obligation-label* digest))

; -----------------------------------------------------------------------------
; The string boundary
;
; A canonical identity is octets.  These two are the only rendering into and
; out of a string, and they are used at exactly three places in the host: the
; store record's metadata fields, the workflow journal's JSON records and the
; NNTP header value.

(defun fn-id-text (identity)
  (declare (xargs :guard (fn-cbor-octet-listp identity)))
  (fn-id-hex-octets identity))

(defun fn-id-from-text (octets)
  (declare (xargs :guard (fn-id-hex-listp octets)))
  (fn-id-unhex octets))

; -----------------------------------------------------------------------------
; The same two identities stated against A-CRYPTO rather than against host
; octets.  These are the specification functions; the theorems that connect
; them to the executable pair above mention `fn-frame-digest` by name.

(defun fn-id-subject-of-payload (payload)
  (declare (xargs :guard (and (fn-cbor-octet-listp payload)
                              (<= (len payload) *fn-cbor-max-uint*))
                  :verify-guards nil))
  (fn-id-subject (fn-frame-digest (fn-id-subject-preimage payload))))

(defun fn-id-obligation-of (msgid subject)
  (declare (xargs :guard (and (fn-cbor-octet-listp msgid)
                              (<= (len msgid) *fn-cbor-max-uint*)
                              (fn-cbor-octet-listp subject)
                              (<= (len subject) *fn-cbor-max-uint*))
                  :verify-guards nil))
  (fn-id-obligation (fn-frame-digest (fn-id-obligation-preimage msgid subject))))

(verify-guards fn-id-subject-of-payload)
(verify-guards fn-id-obligation-of)

; -----------------------------------------------------------------------------
; A recognizer for an identity this book could have produced.  A host that
; hands ACL2 an identity gets it checked against the grammar, not merely
; compared with another octet string of unknown provenance.

(defun fn-id-labelledp (label octets)
  ; The octet check comes first so that the split is never applied to
  ; something that is not a list.
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp octets)
       (let ((split (fn-frame-split (len label) octets)))
         (and split
              (equal (car split) label)
              (let ((tail (cdr split)))
                (and (equal (len tail)
                            (+ *fn-id-header-octets* *fn-id-digest-octets*))
                     (equal (car tail) *fn-id-separator*)
                     (equal (car (cdr tail)) *fn-id-version*)
                     (equal (car (cdr (cdr tail)))
                            *fn-id-algorithm-sha256*)))))))

(defun fn-id-subjectp (octets)
  (declare (xargs :guard t))
  (fn-id-labelledp *fn-id-subject-label* octets))

(defun fn-id-obligationp (octets)
  (declare (xargs :guard t))
  (fn-id-labelledp *fn-id-obligation-label* octets))

; -----------------------------------------------------------------------------
; Charge policy
;
; One unit for the record itself plus one per 4096-octet page of payload.
; `run_store.py` computed this; ACL2 only checked `posp` and accounted.  The
; page size is a local policy choice, not an RFC or storage-hardware fact.

(defconst *fn-id-charge-page-octets* 4096)

(defun fn-charge-for-payload (length)
  (declare (xargs :guard (natp length)))
  (+ 1 (floor (+ (nfix length) (- *fn-id-charge-page-octets* 1))
              *fn-id-charge-page-octets*)))
