; fn: SCRAM-SHA-256 (RFC 5802, RFC 7677), the server's half, with the
; tls-exporter channel binding of RFC 9266 for SCRAM-SHA-256-PLUS.
;
; This book is the mechanism: the stored keys an enrolment derives, the
; grammar of the four messages (RFC 5802 section 7), and the proof check.
; It knows nothing of NNTP; books/sasl.lisp runs the exchange and
; books/nntp-auth.lisp puts it on the wire (RFC 4643 section 2.4).
;
; THE KEYS (RFC 5802 section 3), each over books/hmac-sha256.lisp:
;
;   SaltedPassword  := Hi(Normalize(password), salt, i)
;   ClientKey       := HMAC(SaltedPassword, "Client Key")
;   StoredKey       := H(ClientKey)
;   ServerKey       := HMAC(SaltedPassword, "Server Key")
;   AuthMessage     := client-first-message-bare + "," +
;                      server-first-message + "," +
;                      client-final-message-without-proof
;   ClientSignature := HMAC(StoredKey, AuthMessage)
;   ClientProof     := ClientKey XOR ClientSignature
;   ServerSignature := HMAC(ServerKey, AuthMessage)
;
; The server keeps (salt, i, StoredKey, ServerKey) and never the password or
; SaltedPassword: `fn-scram-keys' is the whole enrolment and its result has
; no other field.  It checks a proof by recovering ClientKey as ClientProof
; XOR ClientSignature and comparing H(ClientKey) with StoredKey.
;
; Normalize is SASLprep (RFC 4013).  fn does not implement the Unicode
; tables: every fn password is an NNTP printable token, octets 33 to 126
; (books/native-auth-admin.lisp fn-native-auth-admin-secretp and the
; XREDEEM PASS token), and on that alphabet SASLprep is the identity (no
; ASCII octet is mapped, normalized differently under NFKC, or prohibited
; except the controls, which the alphabet excludes).  So the identity IS
; SASLprep on every password fn enrols; a client that SASLpreps a non-ASCII
; password presents octets fn never enrolled and fails.  Usernames are
; compared as octets after the saslname decoding (RFC 5802 5.1 "n"), for the
; same reason: fn logins are printable tokens.
;
; WHAT IS PROVED: the keys' shapes; that the stored credential determines
; the check (no password reaches it); that an honest client -- one that
; derived ClientKey from the enrolled password, salt and count -- is
; accepted for every AuthMessage (`fn-scram-honest-proof-verifies'); that a
; client-final carrying any nonce other than the exchange's, or any channel
; binding other than the one the exchange fixed, is refused before any key
; is read; and that an accepted text is the grammar's.  WHAT IS NOT: that a
; client without the password cannot forge a proof, which is HMAC's and
; SHA-256's strength (A-CRYPTO), and anything about the secrecy of the
; server nonce's source (the host's CSPRNG).

(in-package "ACL2")
(include-book "hmac-sha256")
(include-book "octet-text")

; -----------------------------------------------------------------------------
; Octets and constant texts

(defun fn-scram-chars-octets (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (fn-scram-chars-octets (cdr chars)))
    nil))

(defmacro fn-scram-text (s)
  ; A string constant as octets, evaluated when the form is read.
  (list 'quote (fn-scram-chars-octets (coerce s 'list))))

(defconst *fn-scram-client-key-text* (fn-scram-text "Client Key"))
(defconst *fn-scram-server-key-text* (fn-scram-text "Server Key"))
(defconst *fn-scram-mechanism* (fn-scram-text "SCRAM-SHA-256"))
(defconst *fn-scram-plus-mechanism* (fn-scram-text "SCRAM-SHA-256-PLUS"))
(defconst *fn-scram-exporter-name* (fn-scram-text "tls-exporter"))

; RFC 7677 section 4: "the iteration count ... SHOULD be at least 4096".
; fn enrols at exactly this count; a stored count is any positive natural up
; to *fn-scram-max-iterations*, the bound the verifier recognizer admits so
; a hostile credential file cannot ask an enrolment for unbounded work.
(defconst *fn-scram-iterations* 4096)
(defconst *fn-scram-max-iterations* 1000000)

(defconst *fn-scram-comma* 44)
(defconst *fn-scram-equals* 61)

(defun fn-scram-octets (x)
  (declare (xargs :guard t))
  (fn-sha256-fix-octets x))

; -----------------------------------------------------------------------------
; The keys

(defun fn-scram-iterationsp (i)
  (declare (xargs :guard t))
  (and (integerp i) (<= 1 i) (<= i *fn-scram-max-iterations*)))

(defun fn-scram-salted-password (password salt iterations)
  (declare (xargs :guard t))
  (fn-pbkdf2-sha256 password salt iterations))

(defun fn-scram-client-key (salted)
  (declare (xargs :guard t))
  (fn-hmac-sha256 salted *fn-scram-client-key-text*))

(defun fn-scram-stored-key (client-key)
  (declare (xargs :guard t))
  (fn-sha256 client-key))

(defun fn-scram-server-key (salted)
  (declare (xargs :guard t))
  (fn-hmac-sha256 salted *fn-scram-server-key-text*))

(defun fn-scram-keys (password salt iterations)
  ; The enrolment: (StoredKey ServerKey).  PASSWORD is an input and appears
  ; in no field of the result; SaltedPassword is computed once and dropped.
  (declare (xargs :guard t))
  (let ((salted (fn-scram-salted-password password salt iterations)))
    (list (fn-scram-stored-key (fn-scram-client-key salted))
          (fn-scram-server-key salted))))

(defthm fn-scram-keys-shape
  (and (true-listp (fn-scram-keys password salt iterations))
       (equal (len (fn-scram-keys password salt iterations)) 2)
       (fn-sha256-octet-listp (car (fn-scram-keys password salt iterations)))
       (equal (len (car (fn-scram-keys password salt iterations))) 32)
       (fn-sha256-octet-listp (cadr (fn-scram-keys password salt iterations)))
       (equal (len (cadr (fn-scram-keys password salt iterations))) 32))
  :hints (("Goal" :in-theory (disable fn-hmac-sha256 fn-sha256
                                      fn-pbkdf2-sha256))))

(defun fn-scram-client-signature (stored-key auth-message)
  (declare (xargs :guard t))
  (fn-hmac-sha256 stored-key auth-message))

(defun fn-scram-server-signature (server-key auth-message)
  (declare (xargs :guard t))
  (fn-hmac-sha256 server-key auth-message))

(defun fn-scram-proof-validp (stored-key auth-message proof)
  ; RFC 5802 section 3: ClientKey := ClientProof XOR ClientSignature, and
  ; the proof is valid iff H(ClientKey) = StoredKey.  A proof that is not
  ; exactly 32 octets is refused before the comparison.
  (declare (xargs :guard t))
  (and (fn-sha256-octet-listp proof)
       (equal (len proof) 32)
       (equal (fn-sha256 (fn-hmac-xor proof (fn-scram-client-signature
                                            stored-key auth-message)))
              stored-key)
       t))

; What an RFC 5802 client sends: its ClientKey XOR the signature.
(defun fn-scram-client-proof (password salt iterations auth-message)
  (declare (xargs :guard t))
  (let ((client-key (fn-scram-client-key
                     (fn-scram-salted-password password salt iterations))))
    (fn-hmac-xor client-key
                 (fn-scram-client-signature (fn-scram-stored-key client-key)
                                            auth-message))))

; KEYSTONE (completeness).  A client that derived its proof from the
; enrolled password, salt and count is accepted, whatever the AuthMessage:
; the check never rejects the right password.  (The other direction -- a
; wrong password is rejected -- is HMAC/SHA-256 strength, A-CRYPTO, and is
; witnessed on concrete octets in tests/acl2/scram-tests.lisp.)
(defthm fn-scram-honest-proof-verifies
  (fn-scram-proof-validp
   (car (fn-scram-keys password salt iterations))
   auth-message
   (fn-scram-client-proof password salt iterations auth-message))
  :hints (("Goal" :in-theory (disable fn-hmac-sha256 fn-sha256
                                      fn-pbkdf2-sha256 fn-hmac-xor))))

; -----------------------------------------------------------------------------
; The grammar (RFC 5802 section 7)
;
; No value contains a comma: a saslname writes it "=2C", base64 and the
; printable nonce exclude it, and a number has none.  So a message is its
; comma-separated fields exactly, and splitting at commas loses nothing
; (`fn-scram-join-of-split').

(defun fn-scram-split-aux (xs field)
  ; FIELD is the current field reversed.
  (declare (xargs :guard (true-listp field)))
  (if (consp xs)
      (if (equal (car xs) *fn-scram-comma*)
          (cons (revappend field nil) (fn-scram-split-aux (cdr xs) nil))
        (fn-scram-split-aux (cdr xs) (cons (car xs) field)))
    (list (revappend field nil))))

(defun fn-scram-split (xs)
  (declare (xargs :guard t))
  (fn-scram-split-aux xs nil))

(defthm fn-scram-split-aux-is-true-list-listp
  (true-list-listp (fn-scram-split-aux xs field)))

(defthm fn-scram-split-is-true-list-listp
  (true-list-listp (fn-scram-split xs)))

(local
 (defthm fn-scram-true-listp-of-car-of-true-list-listp
   (implies (true-list-listp x)
            (and (true-listp (car x)) (true-listp (cdr x))
                 (true-list-listp (cdr x))))))

(defthm fn-scram-octets-is-true-listp
  (true-listp (fn-scram-octets x))
  :hints (("Goal" :in-theory (enable fn-sha256-fix-octets))))

(defun fn-scram-attrp (field letter)
  ; FIELD is LETTER "=" value.
  (declare (xargs :guard t))
  (and (consp field) (consp (cdr field))
       (equal (car field) letter)
       (equal (cadr field) *fn-scram-equals*)))

(defun fn-scram-attr-value (field)
  (declare (xargs :guard t))
  (if (and (consp field) (consp (cdr field))) (cddr field) nil))

(defun fn-scram-alphap (o)
  (declare (xargs :guard t))
  (or (and (integerp o) (<= 65 o) (<= o 90))
      (and (integerp o) (<= 97 o) (<= o 122))))

(defun fn-scram-no-nulp (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (not (equal (car xs) 0)) (fn-scram-no-nulp (cdr xs))) t))

(defun fn-scram-extensionp (field)
  ; attr-val = ALPHA "=" value; value excludes NUL and ",".
  (declare (xargs :guard t))
  (and (consp field) (consp (cdr field))
       (fn-scram-alphap (car field))
       (equal (cadr field) *fn-scram-equals*)
       (fn-scram-no-nulp (cddr field))))

(defun fn-scram-extensionsp (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (fn-scram-extensionp (car fields))
           (fn-scram-extensionsp (cdr fields)))
    t))

(defun fn-scram-printable-octetp (o)
  ; printable = %x21-2B / %x2D-7E: visible ASCII but ",".
  (declare (xargs :guard t))
  (and (integerp o) (<= 33 o) (<= o 126) (not (equal o *fn-scram-comma*))))

(defun fn-scram-printablep (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-scram-printable-octetp (car xs)) (fn-scram-printablep (cdr xs)))
    (null xs)))

(defun fn-scram-noncep (xs)
  (declare (xargs :guard t))
  (and (consp xs) (fn-scram-printablep xs)))

; saslname = 1*(value-safe-char / "=2C" / "=3D").  Decoding refuses a bare
; "=", NUL, and the empty name (RFC 5802 5.1: the server MUST fail such a
; name).
(defun fn-scram-saslname-decode-aux (xs)
  (declare (xargs :guard t :measure (len xs)))
  (cond ((atom xs) nil)
        ((equal (car xs) 0) :bad)
        ((equal (car xs) *fn-scram-equals*)
         (cond ((and (consp (cdr xs)) (consp (cddr xs))
                     (equal (cadr xs) 50) (equal (caddr xs) 67))
                (let ((rest (fn-scram-saslname-decode-aux (cdddr xs))))
                  (if (equal rest :bad) :bad (cons *fn-scram-comma* rest))))
               ((and (consp (cdr xs)) (consp (cddr xs))
                     (equal (cadr xs) 51) (equal (caddr xs) 68))
                (let ((rest (fn-scram-saslname-decode-aux (cdddr xs))))
                  (if (equal rest :bad) :bad (cons *fn-scram-equals* rest))))
               (t :bad)))
        (t (let ((rest (fn-scram-saslname-decode-aux (cdr xs))))
             (if (equal rest :bad) :bad (cons (car xs) rest))))))

(defun fn-scram-saslname-decode (xs)
  (declare (xargs :guard t))
  (let ((r (fn-scram-saslname-decode-aux xs)))
    (if (or (equal r :bad) (atom r)) :bad r)))

(defun fn-scram-saslname-encode (xs)
  ; The inverse, for tests and for the client half of the round trip.
  (declare (xargs :guard t))
  (if (consp xs)
      (cond ((equal (car xs) *fn-scram-comma*)
             (list* *fn-scram-equals* 50 67 (fn-scram-saslname-encode (cdr xs))))
            ((equal (car xs) *fn-scram-equals*)
             (list* *fn-scram-equals* 51 68 (fn-scram-saslname-encode (cdr xs))))
            (t (cons (car xs) (fn-scram-saslname-encode (cdr xs)))))
    nil))

(defthm fn-scram-saslname-decode-of-encode
  (implies (and (consp xs) (true-listp xs) (not (member-equal 0 xs)))
           (equal (fn-scram-saslname-decode (fn-scram-saslname-encode xs)) xs)))

; -----------------------------------------------------------------------------
; client-first-message
;
;   gs2-header  = gs2-cbind-flag "," [ authzid ] ","
;   gs2-cbind-flag = ("p=" cb-name) / "n" / "y"
;   authzid     = "a=" saslname
;   client-first-message-bare = [reserved-mext ","] username "," nonce
;                               ["," extensions]
;
; The result is (:client-first FLAG AUTHZID USERNAME CNONCE GS2 BARE) with
; FLAG :n, :y or :p (tls-exporter, the only binding fn offers), AUTHZID nil
; or the decoded name, GS2 and BARE the header's and the bare message's exact
; octets; or (:fail REASON), REASON one of RFC 5802 7's server-error-value
; words.  "m=" is refused: section 5.1 "the server MUST fail
; authentication" when a mandatory extension it does not know is present.

(defun fn-scram-cbind-flag (field)
  (declare (xargs :guard t))
  (cond ((equal field (list 110)) :n)
        ((equal field (list 121)) :y)
        ((fn-scram-attrp field 112)
         (if (equal (fn-scram-attr-value field) *fn-scram-exporter-name*)
             :p
           :unsupported))
        (t :bad)))

(defun fn-scram-authzid (field)
  (declare (xargs :guard t))
  (cond ((null field) nil)
        ((fn-scram-attrp field 97)
         (fn-scram-saslname-decode (fn-scram-attr-value field)))
        (t :bad)))

(defun fn-scram-parse-client-first (msg)
  (declare (xargs :guard t))
  (let* ((msg (fn-scram-octets msg))
         (fields (fn-scram-split msg)))
    (if (not (and (consp fields) (consp (cdr fields))
                  (consp (cddr fields)) (consp (cdddr fields))))
        (list :fail :other-error)
      (let* ((flag (fn-scram-cbind-flag (car fields)))
             (authzid (fn-scram-authzid (cadr fields)))
             (user-field (caddr fields))
             (nonce-field (cadddr fields))
             (gs2 (append (car fields) (list *fn-scram-comma*)
                          (cadr fields) (list *fn-scram-comma*)))
             (bare (nthcdr (len gs2) msg)))
        (cond ((equal flag :bad) (list :fail :other-error))
              ((equal flag :unsupported)
               (list :fail :unsupported-channel-binding-type))
              ((equal authzid :bad) (list :fail :invalid-encoding))
              ((fn-scram-attrp user-field 109)
               (list :fail :extensions-not-supported))
              ((not (fn-scram-attrp user-field 110))
               (list :fail :other-error))
              ((equal (fn-scram-saslname-decode (fn-scram-attr-value user-field))
                      :bad)
               (list :fail :invalid-username-encoding))
              ((not (and (fn-scram-attrp nonce-field 114)
                         (fn-scram-noncep (fn-scram-attr-value nonce-field))))
               (list :fail :other-error))
              ((not (fn-scram-extensionsp (cddddr fields)))
               (list :fail :other-error))
              (t (list :client-first flag authzid
                       (fn-scram-saslname-decode (fn-scram-attr-value user-field))
                       (fn-scram-attr-value nonce-field)
                       gs2 bare)))))))

; Total field access for the result records.
(defun fn-scram-nth (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (cond ((atom x) nil)
        ((zp (nfix n)) (car x))
        (t (fn-scram-nth (- (nfix n) 1) (cdr x)))))

(defun fn-scram-failp (r)
  (declare (xargs :guard t))
  (and (consp r) (equal (car r) :fail)))

(defun fn-scram-fail-reason (r)
  (declare (xargs :guard t))
  (fn-scram-nth 1 r))

(defun fn-scram-cf-flag (r) (declare (xargs :guard t)) (fn-scram-nth 1 r))
(defun fn-scram-cf-authzid (r) (declare (xargs :guard t)) (fn-scram-nth 2 r))
(defun fn-scram-cf-username (r) (declare (xargs :guard t)) (fn-scram-nth 3 r))
(defun fn-scram-cf-cnonce (r) (declare (xargs :guard t)) (fn-scram-nth 4 r))
(defun fn-scram-cf-gs2 (r) (declare (xargs :guard t)) (fn-scram-nth 5 r))
(defun fn-scram-cf-bare (r) (declare (xargs :guard t)) (fn-scram-nth 6 r))

; -----------------------------------------------------------------------------
; server-first-message = nonce "," salt "," iteration-count
;   nonce = "r=" c-nonce s-nonce;  salt = "s=" base64;  "i=" posit-number

(defun fn-scram-server-first (cnonce snonce salt iterations)
  (declare (xargs :guard t))
  (append (fn-scram-text "r=") (fn-scram-octets cnonce) (fn-scram-octets snonce)
          (fn-scram-text ",s=") (fn-ot-b64-encode (fn-scram-octets salt))
          (fn-scram-text ",i=") (fn-ot-decimal-octets iterations)))

; -----------------------------------------------------------------------------
; client-final-message = channel-binding "," nonce ["," extensions] "," proof
;   channel-binding = "c=" base64 (of gs2-header || cbind-data)
;   proof           = "p=" base64
;
; The result is (:client-final CBIND NONCE PROOF WITHOUT-PROOF), CBIND and
; PROOF decoded, WITHOUT-PROOF the exact octets before ",p=" (the third part
; of AuthMessage); or (:fail REASON).

(defun fn-scram-last (xs)
  (declare (xargs :guard t))
  (if (consp xs) (if (consp (cdr xs)) (fn-scram-last (cdr xs)) (car xs)) nil))

(defun fn-scram-but-last (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)))
      (cons (car xs) (fn-scram-but-last (cdr xs)))
    nil))

(defun fn-scram-parse-client-final (msg)
  (declare (xargs :guard t))
  (let* ((msg (fn-scram-octets msg))
         (fields (fn-scram-split msg)))
    (if (not (and (consp fields) (consp (cdr fields)) (consp (cddr fields))))
        (list :fail :other-error)
      (let* ((cfield (car fields))
             (nfield (cadr fields))
             (pfield (fn-scram-last fields))
             (middle (cddr (fn-scram-but-last fields)))
             (without (take (nfix (- (len msg) (+ 1 (len pfield)))) msg)))
        (if (not (and (fn-scram-attrp cfield 99)
                      (fn-scram-attrp nfield 114)
                      (fn-scram-noncep (fn-scram-attr-value nfield))
                      (fn-scram-attrp pfield 112)
                      (fn-scram-extensionsp middle)))
            (list :fail :other-error)
          (mv-let (cerr cbind) (fn-ot-b64-decode (fn-scram-attr-value cfield))
            (mv-let (perr proof) (fn-ot-b64-decode (fn-scram-attr-value pfield))
              (if (or cerr perr)
                  (list :fail :invalid-encoding)
                (list :client-final cbind (fn-scram-attr-value nfield)
                      proof without)))))))))

(defun fn-scram-cfin-cbind (r) (declare (xargs :guard t)) (fn-scram-nth 1 r))
(defun fn-scram-cfin-nonce (r) (declare (xargs :guard t)) (fn-scram-nth 2 r))
(defun fn-scram-cfin-proof (r) (declare (xargs :guard t)) (fn-scram-nth 3 r))
(defun fn-scram-cfin-without (r) (declare (xargs :guard t)) (fn-scram-nth 4 r))

; -----------------------------------------------------------------------------
; The server's check of client-final-message, and server-final-message.
;
; The expected channel-binding input is the gs2 header the client sent in
; its first message, followed by the binding data when (and only when) that
; header named tls-exporter.  The order of the checks: grammar, nonce,
; binding, proof.  The first two read no key.

(defun fn-scram-auth-message (bare server-first without-proof)
  (declare (xargs :guard t))
  (append (fn-scram-octets bare) (list *fn-scram-comma*)
          (fn-scram-octets server-first) (list *fn-scram-comma*)
          (fn-scram-octets without-proof)))

(defun fn-scram-expected-cbind (flag gs2 binding)
  (declare (xargs :guard t))
  (if (equal flag :p)
      (append (fn-scram-octets gs2) (fn-scram-octets binding))
    (fn-scram-octets gs2)))

(defun fn-scram-server-final (server-key auth-message)
  ; "v=" base64(ServerSignature).
  (declare (xargs :guard t))
  (append (fn-scram-text "v=")
          (fn-ot-b64-encode (fn-scram-server-signature server-key
                                                       auth-message))))

(defun fn-scram-finish (msg flag gs2 binding nonce bare server-first
                            stored-key server-key)
  ; (:accept SERVER-FINAL) or (:fail REASON).  NONCE is the exchange's
  ; c-nonce || s-nonce, BARE and SERVER-FIRST the first two parts of
  ; AuthMessage.  STORED-KEY nil (an unknown login) fails as a wrong proof
  ; does, after the same work.
  (declare (xargs :guard t))
  (let ((r (fn-scram-parse-client-final msg)))
    (cond ((fn-scram-failp r) r)
          ((not (equal (fn-scram-cfin-nonce r) (fn-scram-octets nonce)))
           (list :fail :nonce-mismatch))
          ((not (equal (fn-scram-cfin-cbind r)
                       (fn-scram-expected-cbind flag gs2 binding)))
           (list :fail :channel-bindings-dont-match))
          (t (let ((am (fn-scram-auth-message bare server-first
                                              (fn-scram-cfin-without r))))
               (if (and stored-key
                        (fn-scram-proof-validp stored-key am
                                               (fn-scram-cfin-proof r)))
                   (list :accept (fn-scram-server-final server-key am))
                 (list :fail :invalid-proof)))))))

; KEYSTONE (the nonce binds the exchange).  A client-final whose nonce is
; not this exchange's c-nonce || s-nonce is refused, whatever proof,
; binding and keys: a final message recorded from another exchange (another
; connection's server nonce) cannot complete this one.
(defthm fn-scram-finish-refuses-another-nonce
  (implies (not (equal (fn-scram-cfin-nonce (fn-scram-parse-client-final msg))
                       (fn-scram-octets nonce)))
           (not (equal (car (fn-scram-finish msg flag gs2 binding nonce bare
                                             server-first stored-key
                                             server-key))
                       :accept)))
  :hints (("Goal" :in-theory (disable fn-scram-parse-client-final
                                      fn-scram-proof-validp
                                      fn-scram-server-final))))

; KEYSTONE (the binding binds the exchange).  A client-final whose
; channel-binding is not the gs2 header followed, under tls-exporter, by
; THIS connection's exporter value is refused: a proof computed over another
; TLS session's exporter (a relayed exchange) cannot complete this one.
(defthm fn-scram-finish-refuses-another-binding
  (implies (not (equal (fn-scram-cfin-cbind (fn-scram-parse-client-final msg))
                       (fn-scram-expected-cbind flag gs2 binding)))
           (not (equal (car (fn-scram-finish msg flag gs2 binding nonce bare
                                             server-first stored-key
                                             server-key))
                       :accept)))
  :hints (("Goal" :in-theory (disable fn-scram-parse-client-final
                                      fn-scram-proof-validp
                                      fn-scram-server-final
                                      fn-scram-expected-cbind))))

; An accept is exactly a valid proof over the AuthMessage the exchange
; built: the only way to :accept.
(defthm fn-scram-finish-accepts-only-a-valid-proof
  (implies (equal (car (fn-scram-finish msg flag gs2 binding nonce bare
                                        server-first stored-key server-key))
                  :accept)
           (fn-scram-proof-validp
            stored-key
            (fn-scram-auth-message
             bare server-first
             (fn-scram-cfin-without (fn-scram-parse-client-final msg)))
            (fn-scram-cfin-proof (fn-scram-parse-client-final msg))))
  :hints (("Goal" :in-theory (disable fn-scram-parse-client-final
                                      fn-scram-proof-validp
                                      fn-scram-server-final
                                      fn-scram-auth-message))))

; -----------------------------------------------------------------------------
; The client's half (for the round-trip theorem and the tests; the server
; never runs it on a password it holds, because it holds none).

(defun fn-scram-client-final-without-proof (flag gs2 binding nonce)
  (declare (xargs :guard t))
  (append (fn-scram-text "c=")
          (fn-ot-b64-encode (fn-scram-expected-cbind flag gs2 binding))
          (fn-scram-text ",r=") (fn-scram-octets nonce)))

(defun fn-scram-client-final (password salt iterations flag gs2 binding nonce
                                       bare server-first)
  (declare (xargs :guard t))
  (let* ((without (fn-scram-client-final-without-proof flag gs2 binding nonce))
         (am (fn-scram-auth-message bare server-first without)))
    (append without (fn-scram-text ",p=")
            (fn-ot-b64-encode
             (fn-scram-client-proof password salt iterations am)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2)

(deftheory fn-scram-internals
  '((:d fn-scram-octets)
    (:d fn-scram-salted-password) (:d fn-scram-client-key)
    (:d fn-scram-stored-key) (:d fn-scram-server-key) (:d fn-scram-keys)
    (:d fn-scram-client-signature) (:d fn-scram-server-signature)
    (:d fn-scram-proof-validp) (:d fn-scram-client-proof)
    (:d fn-scram-split-aux) (:d fn-scram-split) (:d fn-scram-attrp)
    (:d fn-scram-attr-value) (:d fn-scram-saslname-decode-aux)
    (:d fn-scram-saslname-decode) (:d fn-scram-saslname-encode)
    (:d fn-scram-cbind-flag) (:d fn-scram-authzid)
    (:d fn-scram-parse-client-first) (:d fn-scram-parse-client-final)
    (:d fn-scram-server-first) (:d fn-scram-auth-message)
    (:d fn-scram-expected-cbind) (:d fn-scram-server-final)
    (:d fn-scram-finish) (:d fn-scram-client-final-without-proof)
    (:d fn-scram-client-final)))

(in-theory (disable fn-scram-internals))

; -----------------------------------------------------------------------------
; The client's own messages parse back (completeness of the grammar).
;
; A client-first message built from a login (saslname-encoded) and a
; printable nonce, and a client-final message built by fn-scram-client-final,
; parse to exactly the fields they were built from; so an RFC 5802 client
; with the enrolled password completes the exchange
; (books/sasl.lisp fn-sasl-scram-honest-client-completes).

(defun fn-scram-no-commap (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (not (equal (car xs) 44)) (fn-scram-no-commap (cdr xs))) t))

(local (defthm fn-scram-split-aux-steps
  (and (implies (not (equal x 44))
                (equal (fn-scram-split-aux (cons x r) f)
                       (fn-scram-split-aux r (cons x f))))
       (equal (fn-scram-split-aux (cons 44 r) f)
              (cons (revappend f nil) (fn-scram-split-aux r nil))))
  :hints (("Goal" :in-theory (enable fn-scram-split-aux)))))

(local (defthm fn-scram-split-aux-past-a-field
  (implies (fn-scram-no-commap a)
           (equal (fn-scram-split-aux (append a (cons 44 b)) f)
                  (cons (revappend (revappend a f) nil) (fn-scram-split-aux b nil))))
  :hints (("Goal" :induct (fn-scram-split-aux a f)
           :in-theory (enable fn-scram-split-aux)))))

(local (defthm fn-scram-split-aux-of-a-last-field
  (implies (fn-scram-no-commap a)
           (equal (fn-scram-split-aux a f) (list (revappend (revappend a f) nil))))
  :hints (("Goal" :in-theory (enable fn-scram-split-aux)))))

(local (defthm fn-scram-revappend-revappend
  (equal (revappend (revappend x a) b) (revappend a (append x b)))))

(local (defthm fn-scram-sextet-is-not-a-comma
  (not (equal (fn-ot-b64-sextet n) 44))
  :hints (("Goal" :in-theory (enable fn-ot-b64-sextet)))))

(local (defthm fn-scram-b64-has-no-comma
  (fn-scram-no-commap (fn-ot-b64-encode xs))
  :hints (("Goal" :in-theory (enable fn-ot-b64-encode fn-ot-b64-c0 fn-ot-b64-c1
                                     fn-ot-b64-c2 fn-ot-b64-c3 fn-ot-b64-c1-last
                                     fn-ot-b64-c2-last)))))

(defthm fn-scram-b64-is-printable
  (fn-scram-printablep (fn-ot-b64-encode xs))
  :hints (("Goal" :in-theory (enable fn-ot-b64-encode fn-ot-b64-c0 fn-ot-b64-c1
                                     fn-ot-b64-c2 fn-ot-b64-c3 fn-ot-b64-c1-last
                                     fn-ot-b64-c2-last fn-scram-printablep
                                     fn-scram-printable-octetp fn-ot-b64-sextet))))

(defthm fn-scram-printablep-of-append
  (implies (and (fn-scram-printablep a) (fn-scram-printablep b))
           (fn-scram-printablep (append a b)))
  :hints (("Goal" :in-theory (enable fn-scram-printablep))))

(defthm fn-scram-printable-facts
  (implies (fn-scram-printablep x)
           (and (fn-scram-no-commap x) (fn-sha256-octet-listp x) (true-listp x)))
  :hints (("Goal" :in-theory (enable fn-scram-printablep fn-scram-printable-octetp
                                     fn-sha256-octet-listp))))

(local (defthm fn-scram-cbor-octets-are-sha256-octets
  (implies (fn-cbor-octet-listp x)
           (and (fn-sha256-octet-listp x) (true-listp x)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp
                                     fn-sha256-octet-listp)))))

(local (defthm fn-scram-sha256-octets-are-cbor-octets
  (implies (fn-sha256-octet-listp x) (fn-cbor-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp
                                     fn-sha256-octet-listp)))))

(local (defthm fn-scram-b64-shape
  (and (fn-sha256-octet-listp (fn-ot-b64-encode xs))
       (true-listp (fn-ot-b64-encode xs)))
  :hints (("Goal" :in-theory (disable fn-ot-b64-encode)
           :use ((:instance fn-scram-cbor-octets-are-sha256-octets
                            (x (fn-ot-b64-encode xs))))))))

(local (defthm fn-scram-len-of-append
  (equal (len (append a b)) (+ (len a) (len b)))))

(local (defthm fn-scram-take-of-append
  (implies (and (true-listp a) (equal n (len a)))
           (equal (take n (append a b)) a))))

(local (defthm fn-scram-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-scram-parse-client-final-of-a-client-message
  (implies (and (fn-scram-noncep n) (fn-sha256-octet-listp cb)
                (fn-sha256-octet-listp pr))
           (equal (fn-scram-parse-client-final
                   (append (fn-scram-text "c=") (fn-ot-b64-encode cb)
                           (fn-scram-text ",r=") n (fn-scram-text ",p=")
                           (fn-ot-b64-encode pr)))
                  (list :client-final cb n pr
                        (append (fn-scram-text "c=") (fn-ot-b64-encode cb)
                                (fn-scram-text ",r=") n))))
  :hints (("Goal"
           :use ((:instance fn-scram-take-of-append
                            (a (append (fn-scram-text "c=") (fn-ot-b64-encode cb)
                                       (fn-scram-text ",r=") n))
                            (b (append (fn-scram-text ",p=") (fn-ot-b64-encode pr)))
                            (n (len (append (fn-scram-text "c=") (fn-ot-b64-encode cb)
                                            (fn-scram-text ",r=") n)))))
           :in-theory (e/d (fn-scram-parse-client-final fn-scram-split fn-scram-octets
                            fn-scram-attrp fn-scram-attr-value fn-scram-noncep)
                           (fn-scram-take-of-append fn-ot-b64-encode fn-ot-b64-decode
                            fn-scram-split-aux fn-sha256-fix-octets
                            fn-scram-printablep)))))

(local (defthm fn-scram-saslname-encode-has-no-comma
  (fn-scram-no-commap (fn-scram-saslname-encode x))
  :hints (("Goal" :in-theory (enable fn-scram-saslname-encode)))))

(local (defthm fn-scram-no-nulp-is-no-member-0
  (implies (fn-scram-no-nulp x) (not (member-equal 0 x)))
  :hints (("Goal" :in-theory (enable fn-scram-no-nulp)))))

(local (defthm fn-scram-saslname-encode-is-octets
  (implies (fn-sha256-octet-listp x)
           (fn-sha256-octet-listp (fn-scram-saslname-encode x)))
  :hints (("Goal" :in-theory (enable fn-scram-saslname-encode
                                     fn-sha256-octet-listp)))))

(defthm fn-scram-parse-client-first-of-a-client-message
  (implies (and (consp login) (fn-sha256-octet-listp login) (fn-scram-no-nulp login)
                (fn-scram-noncep cn))
           (equal (fn-scram-parse-client-first
                   (append (fn-scram-text "n,,n=") (fn-scram-saslname-encode login)
                           (fn-scram-text ",r=") cn))
                  (list :client-first :n nil login cn (fn-scram-text "n,,")
                        (append (fn-scram-text "n=") (fn-scram-saslname-encode login)
                                (fn-scram-text ",r=") cn))))
  :hints (("Goal"
           :use ((:instance fn-scram-saslname-decode-of-encode (xs login))
                 (:instance fn-sha256-octet-listp-implies-true-listp (xs login)))
           :in-theory (e/d (fn-scram-parse-client-first fn-scram-split fn-scram-octets
                            fn-scram-attrp fn-scram-attr-value fn-scram-noncep
                            fn-scram-cbind-flag fn-scram-authzid fn-scram-extensionsp)
                           (fn-scram-saslname-encode fn-scram-saslname-decode
                            fn-scram-split-aux fn-sha256-fix-octets fn-scram-printablep
                            fn-scram-saslname-decode-of-encode)))))

(local (defthm fn-scram-client-proof-is-octets
  (fn-sha256-octet-listp (fn-scram-client-proof pw salt i am))
  :hints (("Goal" :in-theory (enable fn-scram-client-proof)))))

(defthm fn-scram-parse-of-the-client-final
  (implies (fn-scram-noncep nonce)
           (let ((cfin (fn-scram-client-final pw salt i :n (fn-scram-text "n,,") nil
                                              nonce bare sf))
                 (without (fn-scram-client-final-without-proof
                           :n (fn-scram-text "n,,") nil nonce)))
             (equal (fn-scram-parse-client-final cfin)
                    (list :client-final (fn-scram-text "n,,") nonce
                          (fn-scram-client-proof pw salt i
                                                 (fn-scram-auth-message bare sf without))
                          without))))
  :hints (("Goal"
           :use ((:instance fn-scram-parse-client-final-of-a-client-message
                            (cb (fn-scram-text "n,,")) (n nonce)
                            (pr (fn-scram-client-proof
                                 pw salt i
                                 (fn-scram-auth-message
                                  bare sf
                                  (fn-scram-client-final-without-proof
                                   :n (fn-scram-text "n,,") nil nonce)))))
                 (:instance fn-scram-printable-facts (x nonce))
                 (:instance fn-sha256-fix-octets-is-identity-on-octets (m nonce)))
           :in-theory (e/d (fn-scram-client-final fn-scram-client-final-without-proof
                            fn-scram-expected-cbind fn-scram-octets fn-scram-noncep)
                           (fn-scram-parse-client-final-of-a-client-message
                            fn-scram-parse-client-final fn-scram-client-proof
                            fn-scram-auth-message fn-ot-b64-encode
                            fn-sha256-fix-octets)))))

(defthm fn-scram-stored-key-is-a-cons
  (consp (car (fn-scram-keys pw salt i)))
  :hints (("Goal" :use ((:instance fn-scram-keys-shape (password pw) (iterations i)))
           :in-theory (disable fn-scram-keys fn-scram-keys-shape))))

; The server accepts the final message an RFC 5802 client sends from the
; password the keys were derived from, whatever the exchange's nonce,
; client-first-bare and server-first.
(defthm fn-scram-finish-accepts-the-honest-client
  (implies (fn-scram-noncep nonce)
           (equal (car (fn-scram-finish
                        (fn-scram-client-final pw salt i :n (fn-scram-text "n,,") nil
                                               nonce bare sf)
                        :n (fn-scram-text "n,,") nil nonce bare sf
                        (car (fn-scram-keys pw salt i))
                        (cadr (fn-scram-keys pw salt i))))
                  :accept))
  :hints (("Goal"
           :use ((:instance fn-scram-parse-of-the-client-final)
                 (:instance fn-scram-honest-proof-verifies (password pw) (iterations i)
                            (auth-message (fn-scram-auth-message
                                           bare sf
                                           (fn-scram-client-final-without-proof
                                            :n (fn-scram-text "n,,") nil nonce))))
                 (:instance fn-scram-printable-facts (x nonce))
                 (:instance fn-scram-stored-key-is-a-cons)
                 (:instance fn-sha256-fix-octets-is-identity-on-octets (m nonce)))
           :in-theory (e/d (fn-scram-finish fn-scram-failp fn-scram-nth
                            fn-scram-cfin-nonce fn-scram-cfin-cbind fn-scram-cfin-proof
                            fn-scram-cfin-without fn-scram-expected-cbind fn-scram-octets
                            fn-scram-noncep)
                           (fn-scram-parse-of-the-client-final fn-scram-stored-key-is-a-cons
                            fn-scram-parse-client-final fn-scram-client-final
                            fn-scram-client-final-without-proof fn-scram-proof-validp
                            fn-scram-client-proof fn-scram-auth-message fn-scram-keys
                            fn-scram-honest-proof-verifies fn-scram-server-final
                            fn-sha256-fix-octets)))))

(in-theory (disable fn-scram-no-commap))
