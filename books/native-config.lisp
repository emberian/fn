; fn: bounded, inert native operator configuration profile.
;
; This is intentionally not a general TOML implementation.  The accepted
; language is the documented fn.toml profile: ASCII table headers, simple
; keys, booleans, decimal naturals, and quoted printable-ASCII strings without
; escapes or inline comments.  General TOML features are refused explicitly.
; The raw host supplies only octets; defaults, field bounds, loopback policy,
; pair constraints and the normalized record are owned here.

(in-package "ACL2")
(include-book "records")

(defconst *fn-ncfg-max-octets* 16384)
(defconst *fn-ncfg-max-lines* 128)
(defconst *fn-ncfg-max-path* 512)
(defconst *fn-ncfg-max-text* 256)
(defconst *fn-ncfg-max-server* 128)
(defconst *fn-ncfg-default-listener-host* "127.0.0.1")
(defconst *fn-ncfg-default-listener-port* 1119)
(defconst *fn-ncfg-default-agent* "fn-operator@localhost")
(defconst *fn-ncfg-default-max-connections* 32)
(defconst *fn-ncfg-default-clock-error-ms* 1000)

(defconst *fn-ncfg-listener-ipv4-loopback* '(127 0 0 1))
(defconst *fn-ncfg-listener-ipv6-loopback*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1))

(defun fn-native-config-listener-hostp (host)
  "The three deployment-local listener spellings the profile admits."
  (declare (xargs :guard t))
  (member-equal host '("127.0.0.1" "::1" "localhost")))

(defun fn-native-config-listener-address (host-octets)
  "ACL2's complete address projection for an admitted listener host.

The raw owner receives its existing host-octets callback argument, asks this
subject for the concrete loopback family/address, and never resolves a name.
`localhost' is deliberately the IPv4 loopback projection, matching the prior
host resolver's intended deployment behavior.
"
  (declare (xargs :guard t))
  (cond ((or (equal host-octets (fn-record-string-octets "127.0.0.1"))
             (equal host-octets (fn-record-string-octets "localhost")))
         (list :inet *fn-ncfg-listener-ipv4-loopback*))
        ((equal host-octets (fn-record-string-octets "::1"))
         (list :inet6 *fn-ncfg-listener-ipv6-loopback*))
        (t :bad)))

(defun fn-ncfg-ws-p (x)
  (declare (xargs :guard t))
  (or (equal x 32) (equal x 9) (equal x 13)))

(defun fn-ncfg-trim-left (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (fn-ncfg-ws-p (car xs)))
      (fn-ncfg-trim-left (cdr xs))
    xs))

(defun fn-ncfg-trim-right-rev (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (fn-ncfg-ws-p (car xs)))
      (fn-ncfg-trim-right-rev (cdr xs))
    xs))

(defun fn-ncfg-reverse-aux (xs acc)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-ncfg-reverse-aux (cdr xs) (cons (car xs) acc))
    acc))

(defun fn-ncfg-reverse (xs)
  (declare (xargs :guard t))
  (fn-ncfg-reverse-aux xs nil))

(defun fn-ncfg-first (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-ncfg-rest (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

(defun fn-ncfg-second (x)
  (declare (xargs :guard t))
  (fn-ncfg-first (fn-ncfg-rest x)))

(defun fn-ncfg-third (x)
  (declare (xargs :guard t))
  (fn-ncfg-first (fn-ncfg-rest (fn-ncfg-rest x))))

(defun fn-ncfg-nth (n x)
  (declare (xargs :guard t))
  (if (and (natp n) (consp x))
      (if (zp n) (car x) (fn-ncfg-nth (1- n) (cdr x)))
    nil))

(defun fn-ncfg-trim (xs)
  (declare (xargs :guard t))
  (fn-ncfg-reverse
   (fn-ncfg-trim-right-rev (fn-ncfg-reverse (fn-ncfg-trim-left xs)))))

(defun fn-ncfg-ascii-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= (car xs) 127)
           (fn-ncfg-ascii-octetsp (cdr xs)))
    (null xs)))

(defun fn-ncfg-lines-aux (xs current-rev lines-rev)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (car xs) 10)
          (fn-ncfg-lines-aux (cdr xs) nil
                             (cons (fn-ncfg-reverse current-rev) lines-rev))
        (fn-ncfg-lines-aux (cdr xs) (cons (car xs) current-rev) lines-rev))
    (fn-ncfg-reverse (cons (fn-ncfg-reverse current-rev) lines-rev))))

(defun fn-ncfg-lines (xs)
  (declare (xargs :guard t))
  (fn-ncfg-lines-aux xs nil nil))

(defun fn-ncfg-split-equals (xs left-rev)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (car xs) 61)
          (list (fn-ncfg-reverse left-rev) (cdr xs))
        (fn-ncfg-split-equals (cdr xs) (cons (car xs) left-rev)))
    :bad))

(defun fn-ncfg-ident-octetp (x)
  (declare (xargs :guard t))
  (and (natp x)
       (or (and (<= 65 x) (<= x 90))
      (and (<= 97 x) (<= x 122))
      (and (<= 48 x) (<= x 57))
      (equal x 95) (equal x 45))))

(defun fn-ncfg-identp-tail (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-ncfg-ident-octetp (car xs)) (fn-ncfg-identp-tail (cdr xs)))
    t))

(defun fn-ncfg-identp (xs)
  (declare (xargs :guard t))
  (and (consp xs)
       (fn-ncfg-ident-octetp (car xs)) (fn-ncfg-identp-tail (cdr xs))))

(defun fn-ncfg-digitp (x)
  (declare (xargs :guard t))
  (and (natp x) (<= 48 x) (<= x 57)))

(defun fn-ncfg-decimal-aux (xs value)
  (declare (xargs :guard t))
  (if (not (natp value)) :bad
    (if (consp xs)
        (if (fn-ncfg-digitp (car xs))
            (fn-ncfg-decimal-aux (cdr xs) (+ (* 10 value) (- (car xs) 48)))
          :bad)
      value)))

(defun fn-ncfg-decimal (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (<= (len xs) 5))
      (fn-ncfg-decimal-aux xs 0)
    :bad))

(defun fn-ncfg-printablep (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= 32 (car xs)) (<= (car xs) 126)
           (not (equal (car xs) 34))
           (not (equal (car xs) 92))
           (fn-ncfg-printablep (cdr xs)))
    t))

(defun fn-ncfg-quoted-value (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (equal (car xs) 34)
           (consp (cdr xs)) (equal (fn-ncfg-first (fn-ncfg-reverse xs)) 34))
      (let ((inner (fn-ncfg-reverse
                    (fn-ncfg-rest (fn-ncfg-reverse (cdr xs))))))
        (if (fn-ncfg-printablep inner)
            (list :string (fn-record-octets-string inner))
          :bad))
    :bad))

(defun fn-ncfg-parse-value (xs)
  (declare (xargs :guard t))
  (cond ((equal xs '(116 114 117 101)) (list :bool t))
        ((equal xs '(102 97 108 115 101)) (list :bool nil))
        ((and (consp xs) (equal (car xs) 34)) (fn-ncfg-quoted-value xs))
        (t (let ((n (fn-ncfg-decimal xs)))
             (if (equal n :bad) :bad (list :nat n))))))

(defun fn-ncfg-tablep (name)
  (declare (xargs :guard t))
  (member-equal name '("store" "listener" "auth" "posting" "anchor"
                       "acl2" "log" "control")))

(defun fn-ncfg-key-allowedp (table key)
  (declare (xargs :guard t))
  (cond ((equal table "store") (equal key "path"))
        ((equal table "listener")
         (member-equal key '("host" "port" "tls_cert" "tls_key")))
        ((equal table "auth")
         (member-equal key '("required" "protected_only" "path")))
        ((equal table "posting") (member-equal key '("enabled" "agent")))
        ((equal table "anchor") (equal key "server"))
        ((equal table "acl2") (member-equal key '("path" "slots")))
        ((equal table "log") (equal key "path"))
        ((equal table "control") (equal key "path"))
        (t nil)))

(defun fn-ncfg-memberp (item xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (or (equal item (car xs)) (fn-ncfg-memberp item (cdr xs)))
    nil))

(defun fn-ncfg-pair-seenp (pairs table key)
  (declare (xargs :guard t))
  (if (consp pairs)
      (or (and (equal (fn-ncfg-first (car pairs)) table)
               (equal (fn-ncfg-second (car pairs)) key))
          (fn-ncfg-pair-seenp (cdr pairs) table key))
    nil))

(defun fn-ncfg-table-seenp (tables table)
  (declare (xargs :guard t))
  (fn-ncfg-memberp table tables))

(defun fn-ncfg-parse-lines (lines current tables pairs)
  (declare (xargs :guard t))
  (if (consp lines)
      (let ((line (fn-ncfg-trim (car lines))))
        (cond
         ((or (null line) (equal (fn-ncfg-first line) 35))
          (fn-ncfg-parse-lines (cdr lines) current tables pairs))
         ((and (equal (fn-ncfg-first line) 91)
               (equal (fn-ncfg-first (fn-ncfg-reverse line)) 93))
          (let* ((raw (fn-ncfg-reverse
                       (fn-ncfg-rest (fn-ncfg-reverse (cdr line)))))
                 (name (fn-record-octets-string raw)))
            (if (and (fn-ncfg-identp raw) (fn-ncfg-tablep name)
                     (not (fn-ncfg-table-seenp tables name)))
                (fn-ncfg-parse-lines (cdr lines) name (cons name tables) pairs)
              :bad)))
         (t (let ((split (fn-ncfg-split-equals line nil)))
              (if (or (equal split :bad) (null current)) :bad
                (let* ((raw-key (fn-ncfg-trim (fn-ncfg-first split)))
                       (raw-value (fn-ncfg-trim (fn-ncfg-second split)))
                       (key (fn-record-octets-string raw-key))
                       (value (fn-ncfg-parse-value raw-value)))
                  (if (and (fn-ncfg-identp raw-key)
                           (fn-ncfg-key-allowedp current key)
                           (not (fn-ncfg-pair-seenp pairs current key))
                           (not (equal value :bad)))
                      (fn-ncfg-parse-lines (cdr lines) current tables
                                           (cons (list current key value) pairs))
                    :bad)))))))
    pairs))

(defun fn-ncfg-value (pairs table key)
  (declare (xargs :guard t))
  (if (consp pairs)
      (if (and (equal (fn-ncfg-first (car pairs)) table)
               (equal (fn-ncfg-second (car pairs)) key))
          (fn-ncfg-third (car pairs))
        (fn-ncfg-value (cdr pairs) table key))
    nil))

(defun fn-ncfg-string-okp (text bound)
  (declare (xargs :guard t))
  (and (natp bound) (stringp text)
       (consp (fn-record-string-octets text))
       (<= (len (fn-record-string-octets text)) bound)))

(defun fn-ncfg-string-value (value default bound requiredp)
  (declare (xargs :guard t))
  (cond ((not (natp bound)) :bad)
        ((null value) (cond (requiredp :bad)
                            ((null default) nil)
                            ((fn-ncfg-string-okp default bound) default)
                            (t :bad)))
        ((and (true-listp value) (equal (len value) 2)
              (equal (car value) :string)
              (fn-ncfg-string-okp (fn-ncfg-second value) bound))
         (fn-ncfg-second value))
        (t :bad)))

(defun fn-ncfg-bool-value (value default)
  (declare (xargs :guard t))
  (if (null value) default
    (if (and (true-listp value) (equal (len value) 2)
             (equal (car value) :bool))
        (fn-ncfg-second value)
      :bad)))

(defun fn-ncfg-nat-value (value default ceiling)
  (declare (xargs :guard t))
  (if (not (natp ceiling)) :bad
    (if (null value) default
    (if (and (true-listp value) (equal (len value) 2)
             (equal (car value) :nat) (natp (fn-ncfg-second value))
             (<= (fn-ncfg-second value) ceiling))
        (fn-ncfg-second value)
      :bad))))

(defun fn-native-config-make (store host port tls-cert tls-key auth-required
                                     auth-protected auth-path posting-enabled
                                     agent anchor log control acl2-path acl2-slots)
  (declare (xargs :guard t))
  (list store host port tls-cert tls-key auth-required auth-protected auth-path
        posting-enabled agent anchor log control acl2-path acl2-slots
        *fn-ncfg-default-max-connections* *fn-ncfg-default-clock-error-ms*))

(defun fn-native-config-store (c) (declare (xargs :guard t)) (fn-ncfg-nth 0 c))
(defun fn-native-config-listener-host (c) (declare (xargs :guard t)) (fn-ncfg-nth 1 c))
(defun fn-native-config-listener-port (c) (declare (xargs :guard t)) (fn-ncfg-nth 2 c))
(defun fn-native-config-tls-cert (c) (declare (xargs :guard t)) (fn-ncfg-nth 3 c))
(defun fn-native-config-tls-key (c) (declare (xargs :guard t)) (fn-ncfg-nth 4 c))
(defun fn-native-config-auth-requiredp (c) (declare (xargs :guard t)) (fn-ncfg-nth 5 c))
(defun fn-native-config-auth-protected-onlyp (c) (declare (xargs :guard t)) (fn-ncfg-nth 6 c))
(defun fn-native-config-auth-path (c) (declare (xargs :guard t)) (fn-ncfg-nth 7 c))
(defun fn-native-config-posting-enabledp (c) (declare (xargs :guard t)) (fn-ncfg-nth 8 c))
(defun fn-native-config-posting-agent (c) (declare (xargs :guard t)) (fn-ncfg-nth 9 c))
(defun fn-native-config-anchor-server (c) (declare (xargs :guard t)) (fn-ncfg-nth 10 c))
(defun fn-native-config-log-path (c) (declare (xargs :guard t)) (fn-ncfg-nth 11 c))
(defun fn-native-config-control-path (c) (declare (xargs :guard t)) (fn-ncfg-nth 12 c))
(defun fn-native-config-acl2-path (c) (declare (xargs :guard t)) (fn-ncfg-nth 13 c))
(defun fn-native-config-acl2-slots (c) (declare (xargs :guard t)) (fn-ncfg-nth 14 c))
(defun fn-native-config-owner-max-connections (c) (declare (xargs :guard t)) (fn-ncfg-nth 15 c))
(defun fn-native-config-owner-clock-error-ms (c) (declare (xargs :guard t)) (fn-ncfg-nth 16 c))

(defun fn-ncfg-under-store (store suffix)
  ; Keep the raw string primitive behind a total ACL2 function.  This is also
  ; why a malformed required store field cannot make the parser's executable
  ; counterpart enter Common Lisp with an unchecked string argument.
  (declare (xargs :guard t))
  (if (and (stringp store) (stringp suffix))
      (concatenate 'string store suffix)
    ""))

(defun fn-ncfg-normalize (pairs)
  (declare (xargs :guard t))
  (let* ((store (fn-ncfg-string-value (fn-ncfg-value pairs "store" "path") nil *fn-ncfg-max-path* t))
         (host (fn-ncfg-string-value (fn-ncfg-value pairs "listener" "host") *fn-ncfg-default-listener-host* *fn-ncfg-max-text* nil))
         (port (fn-ncfg-nat-value (fn-ncfg-value pairs "listener" "port") *fn-ncfg-default-listener-port* 65535))
         (tls-cert (fn-ncfg-string-value (fn-ncfg-value pairs "listener" "tls_cert") nil *fn-ncfg-max-path* nil))
         (tls-key (fn-ncfg-string-value (fn-ncfg-value pairs "listener" "tls_key") nil *fn-ncfg-max-path* nil))
         (required (fn-ncfg-bool-value (fn-ncfg-value pairs "auth" "required") nil))
         (protected (fn-ncfg-bool-value (fn-ncfg-value pairs "auth" "protected_only") nil))
         (auth-path (fn-ncfg-string-value (fn-ncfg-value pairs "auth" "path")
                                           (fn-ncfg-under-store store "/auth.toml") *fn-ncfg-max-path* nil))
         (enabled (fn-ncfg-bool-value (fn-ncfg-value pairs "posting" "enabled") t))
         (agent (fn-ncfg-string-value (fn-ncfg-value pairs "posting" "agent") *fn-ncfg-default-agent* *fn-ncfg-max-text* nil))
         (anchor (fn-ncfg-string-value (fn-ncfg-value pairs "anchor" "server") nil *fn-ncfg-max-server* nil))
         (log (fn-ncfg-string-value (fn-ncfg-value pairs "log" "path") nil *fn-ncfg-max-path* nil))
         (control (fn-ncfg-string-value (fn-ncfg-value pairs "control" "path")
                                         (fn-ncfg-under-store store "/control.sock") *fn-ncfg-max-path* nil))
         (acl2-path (fn-ncfg-string-value (fn-ncfg-value pairs "acl2" "path") nil *fn-ncfg-max-path* nil))
         (acl2-slots (fn-ncfg-nat-value (fn-ncfg-value pairs "acl2" "slots") nil 65535)))
    (if (or (equal store :bad) (equal host :bad) (equal port :bad)
            (equal tls-cert :bad) (equal tls-key :bad) (equal required :bad)
            (equal protected :bad) (equal auth-path :bad) (equal enabled :bad)
            (equal agent :bad) (equal anchor :bad) (equal log :bad)
            (equal control :bad) (equal acl2-path :bad) (equal acl2-slots :bad)
            (not (fn-native-config-listener-hostp host))
            (equal port 0) (not (iff tls-cert tls-key)))
        :bad
      (fn-native-config-make store host port tls-cert tls-key required protected
                             auth-path enabled agent anchor log control acl2-path acl2-slots))))

(defthm fn-native-config-listener-address-of-admitted-host
  (implies (fn-native-config-listener-hostp host)
           (not (equal (fn-native-config-listener-address
                        (fn-record-string-octets host))
                       :bad)))
  :hints (("Goal" :in-theory (enable fn-native-config-listener-hostp
                                     fn-native-config-listener-address))))

(defun fn-native-config-load (octets)
  ; The public semantic subject called by the native host wrapper.
  (declare (xargs :guard t))
  (if (and (fn-ncfg-ascii-octetsp octets) (<= (len octets) *fn-ncfg-max-octets*))
      (let ((lines (fn-ncfg-lines octets)))
        (if (< *fn-ncfg-max-lines* (len lines))
            (list :refused :bounds-or-encoding)
          (let ((pairs (fn-ncfg-parse-lines lines nil nil nil)))
            (if (equal pairs :bad)
                (list :refused :syntax)
              (let ((config (fn-ncfg-normalize pairs)))
                (if (equal config :bad) (list :refused :invalid) (list :accepted config)))))))
    (list :refused :bounds-or-encoding)))

(defun fn-native-config-operator-availablep (config)
  ; A later native operator must call this before claiming a setting is live.
  ; Today only the store/listener core profile is consumable by the saved image.
  (declare (xargs :guard t))
  (and (null (fn-native-config-tls-cert config))
       (null (fn-native-config-tls-key config))
       (not (fn-native-config-auth-requiredp config))
       (not (fn-native-config-auth-protected-onlyp config))
       (equal (fn-native-config-posting-enabledp config) t)
       (equal (fn-native-config-posting-agent config) *fn-ncfg-default-agent*)
       (null (fn-native-config-anchor-server config))
       (null (fn-native-config-log-path config))
       (null (fn-native-config-acl2-path config))
       (null (fn-native-config-acl2-slots config))))

(defthm fn-native-config-load-bounded-input-refuses
  (implies (or (not (fn-ncfg-ascii-octetsp octets))
               (< *fn-ncfg-max-octets* (len octets)))
           (equal (fn-native-config-load octets)
                  (list :refused :bounds-or-encoding))))

(in-theory (disable fn-native-config-load))
