; fn: content identity and charge policy, owned by ACL2.
;
; `tools/run_store.py` derived every content identity in the system:
;
;     subject    = "sha256:"  + hex(sha256(payload))
;     obligation = "archive:" + hex(sha256(msgid || 0x00 || subject))
;
; and ACL2 only ever compared the resulting strings.  The derivation is the
; core identity rule of the store, so it belongs here.  This book reproduces
; those exact bytes: the labels, the hexadecimal alphabet and case, the
; separator octet and the order of the preimage are all ACL2 decisions now.
;
; The digest itself is A-CRYPTO, exactly as in `books/frame.lisp`: the host
; supplies 32 octets and ACL2 owns everything around them.  The functions that
; take a digest are executable and guard verified; `fn-id-subject-of-payload`
; and `fn-id-obligation-of` state the same identities against the constrained
; `fn-frame-digest` so that a theorem can mention the assumption it rests on.
;
; The preimage `msgid || 0x00 || subject` is NOT domain separated: it carries
; no domain label, no schema version and no algorithm identifier, so a future
; preimage of another kind could in principle collide with it by construction
; rather than by digest collision.  ENC-003 asks for the opposite.  Changing
; it now would invalidate every existing lab store, so the derivation stands
; and `specs/encoding.md` records the v1 domain-separated profile to adopt.

(in-package "ACL2")
(include-book "frame")

; The derivations are built on the frame field grammar, so this book opens
; it locally; results stay opaque.
(local (in-theory (enable fn-frame-octet-vocabulary
                          fn-frame-fields-vocabulary
                          fn-frame-codec-vocabulary
                          fn-cbor-invariants-vocabulary)))
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
; Labels and identities

(defconst *fn-id-subject-label* '(115 104 97 50 53 54 58))       ; "sha256:"
(defconst *fn-id-obligation-label* '(97 114 99 104 105 118 101 58)) ; "archive:"
(defconst *fn-id-separator* 0)

(defconst *fn-id-digest-octets* 32)
(defconst *fn-id-subject-octets* 71)     ; 7 + 64
(defconst *fn-id-obligation-octets* 72)  ; 8 + 64

(defun fn-id-digestp (xs)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp xs)
       (equal (len xs) *fn-id-digest-octets*)))

(defun fn-id-subject (digest)
  ; The host entry point: `digest` is SHA-256 of the article payload.
  (declare (xargs :guard (fn-id-digestp digest)))
  (append *fn-id-subject-label* (fn-id-hex-octets digest)))

(defun fn-id-obligation (digest)
  ; The host entry point: `digest` is SHA-256 of the obligation preimage.
  (declare (xargs :guard (fn-id-digestp digest)))
  (append *fn-id-obligation-label* (fn-id-hex-octets digest)))

(defun fn-id-obligation-preimage (msgid subject)
  ; The exact bytes the obligation digest covers.  The separator is the one
  ; decision that keeps a Message-ID from running into a subject identity.
  (declare (xargs :guard (and (fn-cbor-octet-listp msgid)
                              (fn-cbor-octet-listp subject))))
  (append msgid (cons *fn-id-separator* subject)))

; The same two identities stated against A-CRYPTO rather than against host
; octets.  These are the specification functions; the theorems that connect
; them to the executable pair above mention `fn-frame-digest` by name.
(defun fn-id-subject-of-payload (payload)
  (declare (xargs :guard (fn-cbor-octet-listp payload) :verify-guards nil))
  (fn-id-subject (fn-frame-digest payload)))

(defun fn-id-obligation-of (msgid subject)
  (declare (xargs :guard (and (fn-cbor-octet-listp msgid)
                              (fn-cbor-octet-listp subject))
                  :verify-guards nil))
  (fn-id-obligation (fn-frame-digest (fn-id-obligation-preimage msgid subject))))

(verify-guards fn-id-subject-of-payload)
(verify-guards fn-id-obligation-of)

; A recognizer for an identity this book could have produced.  A host that
; hands ACL2 a subject string gets it checked against the grammar, not merely
; compared with another string of unknown provenance.
(defun fn-id-labelledp (label octets)
  ; The octet check comes first so that the split is never applied to
  ; something that is not a list.
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp octets)
       (let ((split (fn-frame-split (len label) octets)))
         (and split
              (equal (car split) label)
              (equal (len (cdr split)) (* 2 *fn-id-digest-octets*))
              (fn-id-hex-listp (cdr split))))))

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

; -----------------------------------------------------------------------------
; Export theory.
;
; Enabled on include: nothing but the derivations themselves as executable
; functions.  A book that reasons about them opens this theory locally;
; `identity-invariants' does exactly that and exports the hex keystones.

(deftheory fn-id-definitions
  '(    (:d fn-id-hex-digit) (:d fn-id-hex-digitp) (:d fn-id-hex-value)
    (:d fn-id-hex-octets) (:d fn-id-hex-listp) (:d fn-id-unhex)
    (:d fn-id-digestp) (:d fn-id-subject) (:d fn-id-obligation)
    (:d fn-id-obligation-preimage) (:d fn-id-subject-of-payload)
    (:d fn-id-obligation-of) (:d fn-id-labelledp) (:d fn-id-subjectp)
    (:d fn-id-obligationp) (:d fn-charge-for-payload)))

(in-theory (disable (:d fn-id-hex-digit) (:d fn-id-hex-digitp)
             (:d fn-id-hex-value) (:d fn-id-hex-octets)
             (:d fn-id-hex-listp) (:d fn-id-unhex) (:d fn-id-digestp)
             (:d fn-id-subject) (:d fn-id-obligation)
             (:d fn-id-obligation-preimage) (:d fn-id-subject-of-payload)
             (:d fn-id-obligation-of) (:d fn-id-labelledp)
             (:d fn-id-subjectp) (:d fn-id-obligationp)
             (:d fn-charge-for-payload)))
