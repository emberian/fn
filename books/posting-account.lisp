; fn: the posting-account parameter of Injection-Info (P2, PRF-206).
;
; RFC 5536 section 3.2.8 lets an injecting agent name the account an
; article was posted from, "posting-account", and says it may be obscured.
; fn obscures it with a key only the node holds (PKT-574; gpt-6 wave-5
; review section 3): the value is the lowercase hexadecimal HMAC-SHA256 of
; the login under the posting-account purpose key of the owner's key ring,
; HKDF-SHA256 of the current epoch's root with the node identity as salt
; and the info label `fn/posting-account/v1' (books/node-secret.lisp
; fn-ns-posting-account-key, fn-ns-posting-account-mac; the root is
; STORE/keys/node-secret.key, mode 0600, never in fn.toml, never printed,
; carried by the owner as fn-own-node-secret).  The Cancel-Lock key is the
; same root under `fn/cancel-lock/v1'; the two HKDF inputs never coincide
; (fn-ns-cancel-lock-and-posting-account-inputs-differ).  A key rotation
; changes every login's value.
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
(include-book "node-secret")

(local (include-book "arithmetic-5/top" :dir :system))

; The MAC the value renders (books/node-secret.lisp).
(defun fn-pa-mac (secret login)
  (declare (xargs :guard t))
  (fn-ns-posting-account-mac secret login))

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

; The posting-account value for LOGIN under the node SECRET.
(defun fn-pa-account-value (secret login)
  (declare (xargs :guard t))
  (fn-pa-hex (fn-pa-mac secret login)))

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

(defthm fn-pa-len-of-mac
  (equal (len (fn-pa-mac secret login)) 32)
  :hints (("Goal" :in-theory (disable fn-ns-posting-account-mac)
           :use ((:instance fn-ns-posting-account-mac-shape (ring secret))))))

(defthm fn-pa-mac-is-octets
  (fn-sha256-octet-listp (fn-pa-mac secret login))
  :hints (("Goal" :in-theory (disable fn-ns-posting-account-mac)
           :use ((:instance fn-ns-posting-account-mac-shape (ring secret))))))

(in-theory (disable fn-pa-mac))

; The value is 64 lowercase hexadecimal digits for every key and login.
(defthm fn-pa-account-value-is-hex
  (and (fn-pa-hex-octetsp (fn-pa-account-value secret login))
       (equal (len (fn-pa-account-value secret login)) 64)))

; The login reaches the value only through its MAC.
(defthm fn-pa-account-value-depends-only-on-the-mac
  (implies (equal (fn-pa-mac secret login1) (fn-pa-mac secret login2))
           (equal (fn-pa-account-value secret login1)
                  (fn-pa-account-value secret login2))))

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
  (implies (equal (fn-pa-account-value secret1 login1)
                  (fn-pa-account-value secret2 login2))
           (equal (fn-pa-mac secret1 login1) (fn-pa-mac secret2 login2)))
  :hints (("Goal"
           :in-theory (disable fn-pa-hex)
           :use ((:instance fn-pa-hex-injective
                            (x (fn-pa-mac secret1 login1))
                            (y (fn-pa-mac secret2 login2)))))))
