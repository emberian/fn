; fn: the posting-account parameter of Injection-Info (P2, PRF-206).
;
; RFC 5536 section 3.2.8 lets an injecting agent name the account an
; article was posted from, "posting-account", and says it may be obscured.
; fn obscures it with a key only the node holds (PKT-574, decided by the
; coordinator 2026-09-26): the value is the lowercase hexadecimal HMAC-SHA256
; (RFC 2104; FIPS 180-4 SHA-256, books/sha256.lisp) of the login under a
; 32-octet secret generated at `fn init' into the node's key directory
; (host side: the file posting-account.key, mode 0600, beside the signing
; keys; never in fn.toml and never printed).
;
; What this book proves (PRF-206 (c)), over the functions the injecting
; agent calls:
;   * `fn-pa-account-value-is-hex': the value is exactly 64 octets, each a
;     lowercase hexadecimal digit, whatever the login.  So the header carries
;     no octet of the login except by coincidence of a hex digit, and nothing
;     of its length.
;   * `fn-pa-account-value-depends-only-on-the-mac': two logins whose MACs
;     under the key agree give the same value, and so the same header
;     (books/injection.lisp `fn-inj-info-params-...'): the login reaches the
;     article only through the MAC.
;   * `fn-pa-account-value-determines-the-mac': the value names the MAC
;     (hex is injective), so an operator holding the key who recomputes the
;     value for a friend's login answers exactly "this article came from that
;     login's session" when the two agree.
; What it does NOT prove: that two logins with one value are one login.
; That is HMAC-SHA256's collision resistance, a cryptographic assumption
; about the real function (AGENTS.md: an abstract model proves nothing about
; a real hash).  The pessimistic figure: for n distinct logins under one key
; the chance that any two share a value is at most n(n-1)/2^257 (birthday
; bound on 256 bits); a stranger without the key who tests a candidate login
; must forge an HMAC value (2^-256 per guess), not merely hash a dictionary.

(in-package "ACL2")
(include-book "sha256")

(local (include-book "arithmetic-5/top" :dir :system))

(defconst *fn-pa-block-octets* 64)

(defun fn-pa-xor-each (bytes pad)
  (declare (xargs :guard (and (fn-sha256-octet-listp bytes) (natp pad)
                              (<= pad 255))
                  :verify-guards nil))
  (if (consp bytes)
      (cons (fn-sha256-byte (logxor (car bytes) pad))
            (fn-pa-xor-each (cdr bytes) pad))
    nil))

; RFC 2104 section 2: a key longer than the block is hashed first; the key
; is then padded with zeros to the block length B = 64.
(defun fn-pa-block-key (key)
  (declare (xargs :guard (fn-sha256-octet-listp key)))
  (let ((k (if (< *fn-pa-block-octets* (len key)) (fn-sha256-of-octets key) key)))
    (fn-sha256-appx k (fn-sha256-zeros (- *fn-pa-block-octets* (len k))))))

(defthm fn-pa-octet-listp-of-xor-each
  (fn-sha256-octet-listp (fn-pa-xor-each bytes pad)))

(defthm fn-pa-octet-listp-of-block-key
  (implies (fn-sha256-octet-listp key)
           (fn-sha256-octet-listp (fn-pa-block-key key))))

(defun fn-pa-hmac (key msg)
  "HMAC-SHA256 (RFC 2104) of MSG under KEY, both read as octets."
  (declare (xargs :guard t :verify-guards nil))
  (let* ((key (fn-sha256-fix-octets key))
         (msg (fn-sha256-fix-octets msg))
         (k0 (fn-pa-block-key key)))
    (fn-sha256-of-octets
     (fn-sha256-appx (fn-pa-xor-each k0 92)
                     (fn-sha256-of-octets
                      (fn-sha256-appx (fn-pa-xor-each k0 54) msg))))))

(defun fn-pa-hex-digit (n)
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (if (< n 10) (+ 48 n) (+ 87 (min n 15)))))

(defun fn-pa-hex (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (let ((b (nfix (car bytes))))
        (cons (fn-pa-hex-digit (floor (min b 255) 16))
              (cons (fn-pa-hex-digit (mod (min b 255) 16))
                    (fn-pa-hex (cdr bytes)))))
    nil))

; The posting-account value for LOGIN under KEY.
(defun fn-pa-account-value (key login)
  (declare (xargs :guard t :verify-guards nil))
  (fn-pa-hex (fn-pa-hmac key login)))

; -----------------------------------------------------------------------------
; Theorems

(defun fn-pa-hex-octetp (b)
  (declare (xargs :guard t))
  (and (integerp b)
       (or (and (<= 48 b) (<= b 57)) (and (<= 97 b) (<= b 102)))))

(defun fn-pa-hex-octetsp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (fn-pa-hex-octetp (car bytes)) (fn-pa-hex-octetsp (cdr bytes)))
    (null bytes)))

(defthm fn-pa-hex-digit-is-hex
  (fn-pa-hex-octetp (fn-pa-hex-digit n)))

(defthm fn-pa-hex-is-hex
  (fn-pa-hex-octetsp (fn-pa-hex bytes))
  :hints (("Goal" :in-theory (disable fn-pa-hex-digit))))

(defthm fn-pa-len-of-hex
  (equal (len (fn-pa-hex bytes)) (* 2 (len bytes))))

(defthm fn-pa-len-of-hmac
  (equal (len (fn-pa-hmac key msg)) 32)
  :hints (("Goal" :in-theory (enable fn-pa-hmac))))

(defthm fn-pa-hmac-is-octets
  (fn-sha256-octet-listp (fn-pa-hmac key msg))
  :hints (("Goal" :in-theory (enable fn-pa-hmac))))

(in-theory (disable fn-pa-hmac))

; The value is 64 lowercase hexadecimal digits for every key and login.
(defthm fn-pa-account-value-is-hex
  (and (fn-pa-hex-octetsp (fn-pa-account-value key login))
       (equal (len (fn-pa-account-value key login)) 64)))

; The login reaches the value only through its MAC.
(defthm fn-pa-account-value-depends-only-on-the-mac
  (implies (equal (fn-pa-hmac key login1) (fn-pa-hmac key login2))
           (equal (fn-pa-account-value key login1)
                  (fn-pa-account-value key login2))))

; Hex is injective on octets: the value names the MAC.
(defthm fn-pa-hex-digit-injective
  (implies (and (natp a) (natp b) (<= a 15) (<= b 15))
           (equal (equal (fn-pa-hex-digit a) (fn-pa-hex-digit b))
                  (equal a b))))

(defun fn-pa-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= (car xs) 255) (fn-pa-octetsp (cdr xs)))
    (null xs)))

(defthm fn-pa-octet-split
  (implies (and (natp b) (<= b 255))
           (equal (+ (mod b 16) (* 16 (floor b 16))) b))
  :rule-classes nil)

(defthm fn-pa-nibbles-bounded
  (implies (and (natp b) (<= b 255))
           (and (natp (floor b 16)) (<= (floor b 16) 15)
                (natp (mod b 16)) (<= (mod b 16) 15)))
  :rule-classes nil)

(defthm fn-pa-octet-hex-injective
  (implies (and (natp a) (<= a 255) (natp b) (<= b 255)
                (equal (fn-pa-hex-digit (floor a 16))
                       (fn-pa-hex-digit (floor b 16)))
                (equal (fn-pa-hex-digit (mod a 16))
                       (fn-pa-hex-digit (mod b 16))))
           (equal a b))
  :hints (("Goal" :in-theory (disable fn-pa-hex-digit)
           :use (fn-pa-nibbles-bounded
                 (:instance fn-pa-nibbles-bounded (b a))
                 fn-pa-octet-split
                 (:instance fn-pa-octet-split (b a))
                 (:instance fn-pa-hex-digit-injective
                            (a (floor a 16)) (b (floor b 16)))
                 (:instance fn-pa-hex-digit-injective
                            (a (mod a 16)) (b (mod b 16))))))
  :rule-classes nil)

(defun fn-pa-cdr2 (x y)
  (if (and (consp x) (consp y)) (fn-pa-cdr2 (cdr x) (cdr y)) nil))

(defthm fn-pa-hex-injective
  (implies (and (fn-pa-octetsp x) (fn-pa-octetsp y)
                (equal (fn-pa-hex x) (fn-pa-hex y)))
           (equal x y))
  :hints (("Goal" :induct (fn-pa-cdr2 x y)
           :in-theory (disable fn-pa-hex-digit))
          ("Subgoal *1/1"
           :use ((:instance fn-pa-octet-hex-injective (a (car x)) (b (car y))))))
  :rule-classes nil)

(defthm fn-pa-octetsp-of-sha256
  (implies (fn-sha256-octet-listp x) (fn-pa-octetsp x)))

(defthm fn-pa-account-value-determines-the-mac
  (implies (equal (fn-pa-account-value key1 login1)
                  (fn-pa-account-value key2 login2))
           (equal (fn-pa-hmac key1 login1) (fn-pa-hmac key2 login2)))
  :hints (("Goal"
           :in-theory (disable fn-pa-hex)
           :use ((:instance fn-pa-hex-injective
                            (x (fn-pa-hmac key1 login1))
                            (y (fn-pa-hmac key2 login2)))))))

(verify-guards fn-pa-xor-each)
(verify-guards fn-pa-hmac)
(verify-guards fn-pa-account-value)
