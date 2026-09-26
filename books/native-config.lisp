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

; Work bounds, not data bounds (D27 classification, PRF-102).  fn.toml has a
; fixed schema: ten tables and twenty-seven keys, each admitted at most once
; (`fn-ncfg-pair-seenp', `fn-ncfg-table-seenp'), with no repeated table, so it
; names no collection the store holds -- groups, peers, credentials and
; policy live in the store and its profile.  These two bound the work of one
; read of that fixed-size file (its values are at most 27 x 512 octets).  The
; store profile cannot bound it in any case: fn.toml is read before the store
; is opened, and names the store (`[store] path').
(defconst *fn-ncfg-max-octets* 16384)
(defconst *fn-ncfg-max-lines* 128)
(defconst *fn-ncfg-max-path* 512)
(defconst *fn-ncfg-max-text* 256)
(defconst *fn-ncfg-max-server* 128)
(defconst *fn-ncfg-default-listener-host* "127.0.0.1")
(defconst *fn-ncfg-default-listener-port* 1119)
(defconst *fn-ncfg-default-max-connections* 32)
(defconst *fn-ncfg-default-clock-error-ms* 1000)

; The operator's tables (PKT-096, D28 spike deferral 1).  `[alerts]' and
; `[ops]' are the operator command's: its alert hook and thresholds, and the
; unit, release and log-rotation settings.  The owner reads none of them; they
; are admitted, bounded and normalized here so that the whole of fn.toml has
; one grammar and one owner, and `operator CONFIG show' renders them.
; Defaults are the spike's figures.  A mission (`[ops] mission') is one of the
; names below; its fn.toml and store profile are books/native-config-show.lisp.
(defconst *fn-ncfg-default-headroom-min-percent* 10)
(defconst *fn-ncfg-default-refusal-rate-per-minute* 30)
(defconst *fn-ncfg-default-cooldown-seconds* 900)
(defconst *fn-ncfg-default-ops-scope* "user")
(defconst *fn-ncfg-default-keep-releases* 3)
(defconst *fn-ncfg-default-log-max-bytes* 67108864)
(defconst *fn-ncfg-default-log-keep* 7)
(defconst *fn-ncfg-ops-scopes* '("user" "system"))
(defconst *fn-ncfg-mission-names* '("small-community" "relay" "archive"))

(defconst *fn-ncfg-listener-ipv4-loopback* '(127 0 0 1))
(defconst *fn-ncfg-listener-ipv6-loopback*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1))

(defun fn-ncfg-ipv4-digitp (octet)
  (declare (xargs :guard t))
  (and (natp octet) (<= 48 octet) (<= octet 57)))

(defun fn-ncfg-ipv4-reverse (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (append (fn-ncfg-ipv4-reverse (cdr xs)) (list (car xs)))
    nil))

(defun fn-ncfg-ipv4-address-aux (xs value digits parts-rev)
  (declare (xargs :guard t :measure (len xs)))
  (cond
   ((consp xs)
    (cond
     ((fn-ncfg-ipv4-digitp (car xs))
      (let ((next (+ (* 10 (nfix value)) (- (car xs) 48))))
        (if (and (< (nfix digits) 3) (<= next 255)
                 (not (and (posp digits) (equal value 0))))
            (fn-ncfg-ipv4-address-aux
             (cdr xs) next (1+ (nfix digits)) parts-rev)
          :bad)))
     ((and (equal (car xs) 46) (posp digits) (< (len parts-rev) 3))
      (fn-ncfg-ipv4-address-aux (cdr xs) 0 0 (cons value parts-rev)))
     (t :bad)))
   ((and (posp digits) (equal (len parts-rev) 3))
    (fn-ncfg-ipv4-reverse (cons value parts-rev)))
   (t :bad)))

(defun fn-native-config-ipv4-address (host-octets)
  (declare (xargs :guard t))
  (fn-ncfg-ipv4-address-aux host-octets 0 0 nil))

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

; A decimal of 1 to 20 digits: every frame natural fits (below 2^64).  This
; bounds the work of reading one value; each key's own ceiling is applied at
; normalization (`fn-ncfg-nat-value').
(defconst *fn-ncfg-max-decimal-digits* 20)
(defconst *fn-ncfg-max-u64* 18446744073709551615)

(defun fn-ncfg-decimal (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (<= (len xs) *fn-ncfg-max-decimal-digits*))
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
                       "acl2" "log" "control" "alerts" "ops")))

(defun fn-ncfg-key-allowedp (table key)
  (declare (xargs :guard t))
  (cond ((equal table "store") (equal key "path"))
        ((equal table "listener")
         (member-equal key '("host" "port" "tls_cert" "tls_key" "tls_port")))
        ((equal table "auth")
         (member-equal key '("required" "protected_only" "path")))
        ((equal table "posting") (member-equal key '("enabled" "agent")))
        ((equal table "anchor") (equal key "server"))
        ((equal table "acl2") (member-equal key '("path" "slots")))
        ((equal table "log") (equal key "path"))
        ((equal table "control") (equal key "path"))
        ((equal table "alerts")
         (member-equal key '("command" "headroom_min_percent"
                             "refusal_rate_per_minute" "cooldown_seconds")))
        ((equal table "ops")
         (member-equal key '("mission" "unit" "scope" "keep_releases"
                             "log_max_bytes" "log_keep" "memory_max")))
        (t nil)))

(defun fn-ncfg-memberp (item xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (or (equal item (car xs)) (fn-ncfg-memberp item (cdr xs)))
    nil))

; -----------------------------------------------------------------------------
; The listener address grammar (NNT-041, PRF-197).
;
; `[listener] host' is one address or a comma-separated list of them; the
; owner binds one listener per address (and one implicit-TLS listener per
; address when `tls_port' is set).  Each address is exactly one of:
;   - an IPv4 dotted quad without leading zeros, not 0.0.0.0;
;   - an IPv6 literal in RFC 4291 section 2.2's text forms (hex groups of one
;     to four digits, one "::" at most, an embedded dotted quad last),
;     optionally bracketed as RFC 3986 section 3.2.2's IP-literal (the port
;     is `[listener] port', never inside the host), not "::" and not an
;     IPv4-mapped ::ffff:0:0/96 address (write the IPv4 address instead:
;     OpenBSD's AF_INET6 sockets never carry IPv4);
;   - the name `localhost', which is the IPv4 loopback (never resolved).
; The refusal names which of these an address failed.  The wildcard and
; mapped refusals are fn's local policy, not an RFC requirement: a listener
; reachable off the box is named explicitly (docs/operator.md).

(defconst *fn-ncfg-ipv6-unspecified*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
(defconst *fn-ncfg-ipv6-mapped-prefix* '(0 0 0 0 0 0 0 0 0 0 255 255))
(defconst *fn-ncfg-localhost-octets* '(108 111 99 97 108 104 111 115 116))

(defun fn-ncfg-split-on (xs sep)
  ; The fields of XS between SEP octets; always at least one field.
  (declare (xargs :guard t))
  (if (consp xs)
      (let ((rest (fn-ncfg-split-on (cdr xs) sep)))
        (if (equal (car xs) sep)
            (cons nil rest)
          (cons (cons (car xs) (fn-ncfg-first rest)) (fn-ncfg-rest rest))))
    (list nil)))

(defun fn-ncfg-has-octetp (x xs)
  (declare (xargs :guard t))
  (and (consp xs) (or (equal (car xs) x) (fn-ncfg-has-octetp x (cdr xs)))))

(defun fn-ncfg-hex-value (c)
  ; A hex digit's value (either case), or nil.
  (declare (xargs :guard t))
  (cond ((not (natp c)) nil)
        ((and (<= 48 c) (<= c 57)) (- c 48))
        ((and (<= 97 c) (<= c 102)) (- c 87))
        ((and (<= 65 c) (<= c 70)) (- c 55))
        (t nil)))

(defthm fn-ncfg-hex-value-type
  (or (null (fn-ncfg-hex-value c)) (natp (fn-ncfg-hex-value c)))
  :rule-classes :type-prescription)

(defthm fn-ncfg-hex-value-is-a-digit
  (implies (fn-ncfg-hex-value c) (< (fn-ncfg-hex-value c) 16))
  :rule-classes :linear)

(defun fn-ncfg-hex-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-ncfg-hex-value (car xs)) (fn-ncfg-hex-listp (cdr xs)))
    (null xs)))

(defun fn-ncfg-hex-at (i rev)
  ; The value of the digit I places from the right, 0 past the left end.
  (declare (xargs :guard t))
  (let ((d (fn-ncfg-hex-value (fn-ncfg-nth i rev)))) (if d d 0)))

(defthm fn-ncfg-hex-at-type
  (natp (fn-ncfg-hex-at i rev))
  :rule-classes :type-prescription)

(defthm fn-ncfg-hex-at-is-a-digit
  (< (fn-ncfg-hex-at i rev) 16)
  :rule-classes :linear)

(defun fn-ncfg-app (xs ys)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-ncfg-app (cdr xs) ys)) ys))

(defun fn-ncfg-octet-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (< (car xs) 256) (fn-ncfg-octet-listp (cdr xs)))
    (null xs)))

(defthm fn-ncfg-app-shape
  (and (equal (len (fn-ncfg-app xs ys)) (+ (len xs) (len ys)))
       (implies (and (fn-ncfg-octet-listp xs) (fn-ncfg-octet-listp ys))
                (fn-ncfg-octet-listp (fn-ncfg-app xs ys)))))

(defun fn-ncfg-v6-group-octets (field)
  ; One to four hex digits: the group's two octets, big-endian, or :bad.
  (declare (xargs :guard t))
  (if (and (consp field) (<= (len field) 4) (fn-ncfg-hex-listp field))
      (let ((rev (fn-ncfg-reverse field)))
        (list (+ (* 16 (fn-ncfg-hex-at 3 rev)) (fn-ncfg-hex-at 2 rev))
              (+ (* 16 (fn-ncfg-hex-at 1 rev)) (fn-ncfg-hex-at 0 rev))))
    :bad))

(defthm fn-ncfg-v6-group-octets-shape
  (implies (not (equal (fn-ncfg-v6-group-octets f) :bad))
           (and (fn-ncfg-octet-listp (fn-ncfg-v6-group-octets f))
                (equal (len (fn-ncfg-v6-group-octets f)) 2)))
  :hints (("Goal" :in-theory (e/d (fn-ncfg-v6-group-octets)
                                  (fn-ncfg-reverse fn-ncfg-hex-at fn-ncfg-hex-listp)))))

(in-theory (disable fn-ncfg-v6-group-octets))

(defthm fn-ncfg-octet-listp-of-append
  (implies (and (fn-ncfg-octet-listp a) (fn-ncfg-octet-listp b))
           (fn-ncfg-octet-listp (append a b))))

(defthm fn-ncfg-len-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-ncfg-ipv4-reverse-shape
  (implies (fn-ncfg-octet-listp xs)
           (and (fn-ncfg-octet-listp (fn-ncfg-ipv4-reverse xs))
                (equal (len (fn-ncfg-ipv4-reverse xs)) (len xs)))))

(defthm fn-ncfg-ipv4-address-aux-shape
  (implies (and (fn-ncfg-octet-listp parts-rev) (<= (len parts-rev) 3)
                (natp value) (< value 256)
                (not (equal (fn-ncfg-ipv4-address-aux xs value digits parts-rev) :bad)))
           (and (fn-ncfg-octet-listp (fn-ncfg-ipv4-address-aux xs value digits parts-rev))
                (equal (len (fn-ncfg-ipv4-address-aux xs value digits parts-rev)) 4))))

(defthm fn-native-config-ipv4-address-shape
  (implies (not (equal (fn-native-config-ipv4-address xs) :bad))
           (and (fn-ncfg-octet-listp (fn-native-config-ipv4-address xs))
                (equal (len (fn-native-config-ipv4-address xs)) 4))))

(in-theory (disable fn-native-config-ipv4-address))

(defun fn-ncfg-v6-part (fields tailp)
  ; Octets of colon-separated FIELDS; with TAILP the last may be a dotted quad.
  (declare (xargs :guard t))
  (if (consp fields)
      (if (and tailp (not (consp (cdr fields)))
               (fn-ncfg-has-octetp 46 (car fields)))
          (fn-native-config-ipv4-address (car fields))
        (let ((g (fn-ncfg-v6-group-octets (car fields)))
              (rest (fn-ncfg-v6-part (cdr fields) tailp)))
          (if (or (equal g :bad) (equal rest :bad))
              :bad
            (fn-ncfg-app g rest))))
    nil))

(defthm fn-ncfg-v6-part-shape
  (implies (not (equal (fn-ncfg-v6-part fields tailp) :bad))
           (fn-ncfg-octet-listp (fn-ncfg-v6-part fields tailp))))

(in-theory (disable fn-ncfg-v6-part))

(defun fn-ncfg-v6-fields (xs)
  (declare (xargs :guard t))
  (if (consp xs) (fn-ncfg-split-on xs 58) nil))

(defun fn-ncfg-v6-double-colon (xs)
  ; (LEFT . RIGHT) around the first "::" in XS, or nil when there is none.
  (declare (xargs :guard t))
  (cond ((not (consp xs)) nil)
        ((and (equal (car xs) 58) (consp (cdr xs)) (equal (cadr xs) 58))
         (cons nil (cddr xs)))
        (t (let ((r (fn-ncfg-v6-double-colon (cdr xs))))
             (and r (cons (cons (car xs) (car r)) (cdr r)))))))

(defun fn-ncfg-zeros (n)
  (declare (xargs :guard t :measure (nfix n)))
  (if (and (natp n) (< 0 n)) (cons 0 (fn-ncfg-zeros (1- n))) nil))

(defthm fn-ncfg-zeros-shape
  (and (fn-ncfg-octet-listp (fn-ncfg-zeros n))
       (equal (len (fn-ncfg-zeros n)) (nfix n))))

(defun fn-ncfg-ipv6-unbracketed (xs)
  (declare (xargs :guard t))
  (let ((dc (fn-ncfg-v6-double-colon xs)))
    (if dc
        (let ((left (fn-ncfg-v6-part (fn-ncfg-v6-fields (car dc)) nil))
              (right (fn-ncfg-v6-part (fn-ncfg-v6-fields (cdr dc)) t)))
          (if (or (equal left :bad) (equal right :bad)
                  (fn-ncfg-v6-double-colon (cdr dc))
                  (< 14 (+ (len left) (len right))))
              :bad
            (fn-ncfg-app left (fn-ncfg-app (fn-ncfg-zeros (- 16 (+ (len left) (len right))))
                                           right))))
      (let ((all (fn-ncfg-v6-part (fn-ncfg-split-on xs 58) t)))
        (if (and (not (equal all :bad)) (equal (len all) 16)) all :bad)))))

(defthm fn-ncfg-ipv6-unbracketed-shape
  (implies (not (equal (fn-ncfg-ipv6-unbracketed xs) :bad))
           (and (fn-ncfg-octet-listp (fn-ncfg-ipv6-unbracketed xs))
                (equal (len (fn-ncfg-ipv6-unbracketed xs)) 16))))

(in-theory (disable fn-ncfg-ipv6-unbracketed))

(defun fn-native-config-ipv6-literal (xs)
  ; RFC 4291 section 2.2 text, bare or bracketed (RFC 3986 section 3.2.2).
  (declare (xargs :guard t))
  (if (and (consp xs) (equal (car xs) 91))
      (let ((inner-rev (fn-ncfg-reverse (cdr xs))))
        (if (and (consp inner-rev) (equal (car inner-rev) 93))
            (fn-ncfg-ipv6-unbracketed (fn-ncfg-reverse (cdr inner-rev)))
          :bad))
    (fn-ncfg-ipv6-unbracketed xs)))

(defthm fn-native-config-ipv6-literal-shape
  (implies (not (equal (fn-native-config-ipv6-literal xs) :bad))
           (and (fn-ncfg-octet-listp (fn-native-config-ipv6-literal xs))
                (equal (len (fn-native-config-ipv6-literal xs)) 16))))

(in-theory (disable fn-native-config-ipv6-literal))

(defun fn-ncfg-prefixp (p xs)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp xs) (equal (car p) (car xs)) (fn-ncfg-prefixp (cdr p) (cdr xs)))
    t))

(defun fn-ncfg-listener-element (text)
  ; (:ok PROJECTION) or (:refused REASON) for one trimmed address.
  (declare (xargs :guard t))
  (let ((ipv4 (fn-native-config-ipv4-address text)))
    (cond ((not (equal ipv4 :bad))
           (if (equal ipv4 '(0 0 0 0))
               (list :refused :listener-unspecified)
             (list :ok (list :inet ipv4))))
          ((equal text *fn-ncfg-localhost-octets*)
           (list :ok (list :inet *fn-ncfg-listener-ipv4-loopback*)))
          (t (let ((ipv6 (fn-native-config-ipv6-literal text)))
               (cond ((equal ipv6 :bad) (list :refused :listener-address))
                     ((equal ipv6 *fn-ncfg-ipv6-unspecified*)
                      (list :refused :listener-unspecified))
                     ((fn-ncfg-prefixp *fn-ncfg-ipv6-mapped-prefix* ipv6)
                      (list :refused :listener-mapped))
                     (t (list :ok (list :inet6 ipv6)))))))))

(defun fn-ncfg-listener-plan (elements)
  ; (:ok PROJECTIONS) in the written order, or the first address's refusal.
  (declare (xargs :guard t))
  (if (consp elements)
      (let ((r (fn-ncfg-listener-element (fn-ncfg-trim (car elements)))))
        (if (equal (fn-ncfg-first r) :refused)
            r
          (let ((rest (fn-ncfg-listener-plan (cdr elements))))
            (cond ((equal (fn-ncfg-first rest) :refused) rest)
                  ((fn-ncfg-memberp (fn-ncfg-second r) (fn-ncfg-second rest))
                   (list :refused :listener-duplicate))
                  (t (list :ok (cons (fn-ncfg-second r)
                                     (fn-ncfg-second rest))))))))
    (list :ok nil)))

(defun fn-native-config-listener-plan (host-octets)
  (declare (xargs :guard t))
  (fn-ncfg-listener-plan (fn-ncfg-split-on host-octets 44)))

(defun fn-native-config-listener-addresses (host-octets)
  "ACL2's complete projection of an admitted `[listener] host': the list of
(FAMILY ADDRESS-OCTETS) the owner binds, in the written order, or :bad.  The
raw owner binds exactly these octets and never resolves a name."
  (declare (xargs :guard t))
  (let ((plan (fn-native-config-listener-plan host-octets)))
    (if (equal (fn-ncfg-first plan) :ok) (fn-ncfg-second plan) :bad)))

(defun fn-native-config-listener-address (host-octets)
  "The projection of one address (the single-address form of the list)."
  (declare (xargs :guard t))
  (let ((r (fn-ncfg-listener-element host-octets)))
    (if (equal (fn-ncfg-first r) :ok) (fn-ncfg-second r) :bad)))

(defun fn-native-config-listener-hostp (host)
  "One or more listener addresses, each admitted by the grammar above."
  (declare (xargs :guard t))
  (and (stringp host)
       (not (equal (fn-native-config-listener-addresses
                    (fn-record-string-octets host))
                   :bad))))

(defun fn-native-config-listener-projectionp (p)
  ; What the owner may bind: an AF_INET dotted quad that is not the wildcard,
  ; or an AF_INET6 address that is neither the wildcard nor IPv4-mapped.
  (declare (xargs :guard t))
  (and (consp p) (consp (cdr p)) (null (cddr p))
       (fn-ncfg-octet-listp (cadr p))
       (or (and (equal (car p) :inet) (equal (len (cadr p)) 4)
                (not (equal (cadr p) '(0 0 0 0))))
           (and (equal (car p) :inet6) (equal (len (cadr p)) 16)
                (not (equal (cadr p) *fn-ncfg-ipv6-unspecified*))
                (not (fn-ncfg-prefixp *fn-ncfg-ipv6-mapped-prefix* (cadr p)))))))

(defun fn-native-config-listener-projection-listp (ps)
  (declare (xargs :guard t))
  (if (consp ps)
      (and (fn-native-config-listener-projectionp (car ps))
           (fn-native-config-listener-projection-listp (cdr ps)))
    (null ps)))

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
                                     agent anchor log control acl2-path acl2-slots
                                     alert-command headroom refusal-rate cooldown
                                     mission unit scope keep-releases log-max-bytes
                                     log-keep memory-max tls-port)
  ; The eleven after control-path are the operator's `[alerts]' and `[ops]' rows, read by the
  ; operator's command through `operator CONFIG show', never by the owner.
  (declare (xargs :guard t))
  (list store host port tls-cert tls-key auth-required auth-protected auth-path
        posting-enabled agent anchor log control acl2-path acl2-slots
        *fn-ncfg-default-max-connections* *fn-ncfg-default-clock-error-ms*
        alert-command headroom refusal-rate cooldown
        mission unit scope keep-releases log-max-bytes log-keep memory-max
        tls-port))

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
(defun fn-native-config-alerts-command (c) (declare (xargs :guard t)) (fn-ncfg-nth 17 c))
(defun fn-native-config-alerts-headroom-min-percent (c) (declare (xargs :guard t)) (fn-ncfg-nth 18 c))
(defun fn-native-config-alerts-refusal-rate-per-minute (c) (declare (xargs :guard t)) (fn-ncfg-nth 19 c))
(defun fn-native-config-alerts-cooldown-seconds (c) (declare (xargs :guard t)) (fn-ncfg-nth 20 c))
(defun fn-native-config-ops-mission (c) (declare (xargs :guard t)) (fn-ncfg-nth 21 c))
(defun fn-native-config-ops-unit (c) (declare (xargs :guard t)) (fn-ncfg-nth 22 c))
(defun fn-native-config-ops-scope (c) (declare (xargs :guard t)) (fn-ncfg-nth 23 c))
(defun fn-native-config-ops-keep-releases (c) (declare (xargs :guard t)) (fn-ncfg-nth 24 c))
(defun fn-native-config-ops-log-max-bytes (c) (declare (xargs :guard t)) (fn-ncfg-nth 25 c))
(defun fn-native-config-ops-log-keep (c) (declare (xargs :guard t)) (fn-ncfg-nth 26 c))
(defun fn-native-config-ops-memory-max (c) (declare (xargs :guard t)) (fn-ncfg-nth 27 c))
; `[listener] tls_port': the implicit-TLS listener, or nil for none.  RFC
; 4642 section 1 describes the separate port (563) that begins TLS at
; connect and discourages it in favour of STARTTLS; fn offers it as a local
; policy because deployed readers (tin 2.6) speak only that form.  RFC 8143
; section 3, which is not among the supplied RFCs, later reversed the
; preference.  The session behind it is the STARTTLS session after its
; handshake (books/served-implicit-tls.lisp).
(defun fn-native-config-listener-tls-port (c) (declare (xargs :guard t)) (fn-ncfg-nth 28 c))

(defun fn-ncfg-absolutep (path)
  (declare (xargs :guard t))
  (and (stringp path) (< 0 (length path)) (equal (char path 0) #\/)))

(defun fn-ncfg-optional-absolutep (path)
  (declare (xargs :guard t))
  (or (null path) (fn-ncfg-absolutep path)))

(defun fn-ncfg-optional-memberp (text names)
  (declare (xargs :guard t))
  (or (null text) (fn-ncfg-memberp text names)))

(defun fn-ncfg-pairedp (a b)
  "Both present or both absent (the TLS certificate and key)."
  (declare (xargs :guard t))
  (iff a b))

(defun fn-ncfg-tls-port-okp (tls-port port tls-cert)
  "No implicit-TLS listener, or one on a nonzero port other than PORT with a certificate."
  (declare (xargs :guard t))
  (or (null tls-port)
      (and (not (equal tls-port 0))
           (not (equal tls-port port))
           (if tls-cert t nil))))

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
         (tls-port (fn-ncfg-nat-value (fn-ncfg-value pairs "listener" "tls_port") nil 65535))
         (required (fn-ncfg-bool-value (fn-ncfg-value pairs "auth" "required") nil))
         (protected (fn-ncfg-bool-value (fn-ncfg-value pairs "auth" "protected_only") nil))
         (auth-path (fn-ncfg-string-value (fn-ncfg-value pairs "auth" "path")
                                           (fn-ncfg-under-store store "/auth.toml") *fn-ncfg-max-path* nil))
         (enabled (fn-ncfg-bool-value (fn-ncfg-value pairs "posting" "enabled") t))
         (agent (fn-ncfg-string-value (fn-ncfg-value pairs "posting" "agent") nil *fn-ncfg-max-text* nil))
         (anchor (fn-ncfg-string-value (fn-ncfg-value pairs "anchor" "server") nil *fn-ncfg-max-server* nil))
         (log (fn-ncfg-string-value (fn-ncfg-value pairs "log" "path") nil *fn-ncfg-max-path* nil))
         (control (fn-ncfg-string-value (fn-ncfg-value pairs "control" "path")
                                         (fn-ncfg-under-store store "/control.sock") *fn-ncfg-max-path* nil))
         (acl2-path (fn-ncfg-string-value (fn-ncfg-value pairs "acl2" "path") nil *fn-ncfg-max-path* nil))
         (acl2-slots (fn-ncfg-nat-value (fn-ncfg-value pairs "acl2" "slots") nil 65535))
         (alert-command (fn-ncfg-string-value (fn-ncfg-value pairs "alerts" "command") nil *fn-ncfg-max-path* nil))
         (headroom (fn-ncfg-nat-value (fn-ncfg-value pairs "alerts" "headroom_min_percent")
                                      *fn-ncfg-default-headroom-min-percent* 100))
         (refusal-rate (fn-ncfg-nat-value (fn-ncfg-value pairs "alerts" "refusal_rate_per_minute")
                                          *fn-ncfg-default-refusal-rate-per-minute* *fn-ncfg-max-u64*))
         (cooldown (fn-ncfg-nat-value (fn-ncfg-value pairs "alerts" "cooldown_seconds")
                                      *fn-ncfg-default-cooldown-seconds* *fn-ncfg-max-u64*))
         (mission (fn-ncfg-string-value (fn-ncfg-value pairs "ops" "mission") nil *fn-ncfg-max-text* nil))
         (unit (fn-ncfg-string-value (fn-ncfg-value pairs "ops" "unit") nil *fn-ncfg-max-text* nil))
         (scope (fn-ncfg-string-value (fn-ncfg-value pairs "ops" "scope") *fn-ncfg-default-ops-scope* *fn-ncfg-max-text* nil))
         (keep-releases (fn-ncfg-nat-value (fn-ncfg-value pairs "ops" "keep_releases")
                                           *fn-ncfg-default-keep-releases* *fn-ncfg-max-u64*))
         (log-max-bytes (fn-ncfg-nat-value (fn-ncfg-value pairs "ops" "log_max_bytes")
                                           *fn-ncfg-default-log-max-bytes* *fn-ncfg-max-u64*))
         (log-keep (fn-ncfg-nat-value (fn-ncfg-value pairs "ops" "log_keep")
                                      *fn-ncfg-default-log-keep* *fn-ncfg-max-u64*))
         (memory-max (fn-ncfg-string-value (fn-ncfg-value pairs "ops" "memory_max") nil *fn-ncfg-max-text* nil)))
    (if (or (equal store :bad) (equal host :bad) (equal port :bad)
            (equal tls-cert :bad) (equal tls-key :bad) (equal required :bad)
            (equal protected :bad) (equal auth-path :bad) (equal enabled :bad)
            (equal agent :bad) (equal anchor :bad) (equal log :bad)
            (equal control :bad) (equal acl2-path :bad) (equal acl2-slots :bad)
            (not (fn-native-config-listener-hostp host))
            (equal port 0) (not (fn-ncfg-pairedp tls-cert tls-key))
            ; The implicit-TLS listener: a port of its own, and only with the
            ; certificate and key its handshake needs.
            (equal tls-port :bad) (not (fn-ncfg-tls-port-okp tls-port port tls-cert))
            ; The operator's tables: each row's own relation (PKT-096).
            (equal alert-command :bad) (equal headroom :bad)
            (equal refusal-rate :bad) (equal cooldown :bad)
            (equal mission :bad) (equal unit :bad) (equal scope :bad)
            (equal keep-releases :bad) (equal log-max-bytes :bad)
            (equal log-keep :bad) (equal memory-max :bad)
            (not (fn-ncfg-optional-absolutep alert-command))
            (not (fn-ncfg-optional-memberp mission *fn-ncfg-mission-names*))
            (not (fn-ncfg-memberp scope *fn-ncfg-ops-scopes*))
            (equal keep-releases 0) (equal log-max-bytes 0))
        :bad
      (fn-native-config-make store host port tls-cert tls-key required protected
                             auth-path enabled agent anchor log control acl2-path acl2-slots
                             alert-command headroom refusal-rate cooldown
                             mission unit scope keep-releases log-max-bytes
                             log-keep memory-max tls-port))))

(defthm fn-ncfg-listener-element-ok-is-a-projection
  (implies (equal (fn-ncfg-first (fn-ncfg-listener-element text)) :ok)
           (fn-native-config-listener-projectionp
            (fn-ncfg-second (fn-ncfg-listener-element text)))))

(defthm fn-ncfg-memberp-is-member-equal
  (iff (fn-ncfg-memberp x xs) (member-equal x xs)))

(defthm fn-ncfg-first-of-cons (equal (fn-ncfg-first (cons a b)) a))
(defthm fn-ncfg-second-of-cons (equal (fn-ncfg-second (cons a b)) (fn-ncfg-first b)))

(defthm fn-ncfg-listener-element-tag-ok
  (implies (not (equal (fn-ncfg-first (fn-ncfg-listener-element text)) :refused))
           (equal (fn-ncfg-first (fn-ncfg-listener-element text)) :ok)))

(defthm fn-ncfg-listener-plan-tag-ok
  (implies (not (equal (fn-ncfg-first (fn-ncfg-listener-plan elements)) :refused))
           (equal (fn-ncfg-first (fn-ncfg-listener-plan elements)) :ok))
  :hints (("Goal" :in-theory (disable fn-ncfg-listener-element fn-ncfg-trim))))

(defthm fn-ncfg-listener-plan-ok-shape
  (implies (equal (fn-ncfg-first (fn-ncfg-listener-plan elements)) :ok)
           (and (fn-native-config-listener-projection-listp
                 (fn-ncfg-second (fn-ncfg-listener-plan elements)))
                (no-duplicatesp-equal
                 (fn-ncfg-second (fn-ncfg-listener-plan elements)))
                (equal (len (fn-ncfg-second (fn-ncfg-listener-plan elements)))
                       (len elements))))
  :hints (("Goal" :in-theory (disable fn-ncfg-listener-element fn-ncfg-trim
                                      fn-native-config-listener-projectionp
                                      fn-ncfg-first fn-ncfg-second)
           :induct (fn-ncfg-listener-plan elements))))

(defthm fn-ncfg-split-on-is-nonempty
  (consp (fn-ncfg-split-on xs sep))
  :rule-classes :type-prescription)

(defthm fn-ncfg-split-on-has-a-field
  (< 0 (len (fn-ncfg-split-on xs sep)))
  :rule-classes :linear)

;  KEYSTONE (PRF-197; NNT-041).  The subject is
; `fn-native-config-listener-addresses', which the owner calls through
; host/native-config-host.lisp `fn-native-config-host-listener-addresses'
; (host/native/owner.lisp `fnn-owner-run-normalized') and binds octet for
; octet: every admitted `[listener] host' projects to a nonempty,
; duplicate-free list of bindable addresses, each an AF_INET dotted quad
; other than 0.0.0.0 or an AF_INET6 literal other than :: and ::ffff:0:0/96.
(defthm fn-native-config-listener-addresses-are-bindable-projections
  (let ((ps (fn-native-config-listener-addresses host-octets)))
    (implies (not (equal ps :bad))
             (and (consp ps)
                  (fn-native-config-listener-projection-listp ps)
                  (no-duplicatesp-equal ps))))
  :hints (("Goal" :in-theory (disable fn-ncfg-listener-plan-ok-shape
                                      fn-ncfg-listener-plan fn-ncfg-first fn-ncfg-second)
           :use ((:instance fn-ncfg-listener-plan-ok-shape
                            (elements (fn-ncfg-split-on host-octets 44)))))))

; Which of the three forms each admitted address is: a dotted quad, the
; name `localhost' (the IPv4 loopback), or an IPv6 literal.
(defthm fn-ncfg-listener-element-classifies-by-definition
  (let ((r (fn-ncfg-listener-element text)))
    (implies (equal (fn-ncfg-first r) :ok)
             (or (equal (fn-ncfg-second r)
                        (list :inet (fn-native-config-ipv4-address text)))
                 (and (equal text *fn-ncfg-localhost-octets*)
                      (equal (fn-ncfg-second r)
                             (list :inet *fn-ncfg-listener-ipv4-loopback*)))
                 (equal (fn-ncfg-second r)
                        (list :inet6 (fn-native-config-ipv6-literal text))))))
  :rule-classes nil)

(defthm fn-native-config-listener-address-of-admitted-host
  (implies (fn-native-config-listener-hostp host)
           (not (equal (fn-native-config-listener-addresses
                        (fn-record-string-octets host))
                       :bad)))
  :rule-classes nil)

(defun fn-ncfg-listener-refusal (pairs)
  ; Why `[listener] host' is refused, or nil when it is admitted or absent.
  (declare (xargs :guard t))
  (let ((host (fn-ncfg-string-value (fn-ncfg-value pairs "listener" "host")
                                    *fn-ncfg-default-listener-host*
                                    *fn-ncfg-max-text* nil)))
    (and (stringp host)
         (let ((plan (fn-native-config-listener-plan
                      (fn-record-string-octets host))))
           (and (equal (fn-ncfg-first plan) :refused)
                (fn-ncfg-second plan))))))

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
                (if (equal config :bad)
                    (let ((why (fn-ncfg-listener-refusal pairs)))
                      (list :refused (or why :invalid)))
                  (list :accepted config)))))))
    (list :refused :bounds-or-encoding)))

;; What the native owner consumes, and the one key it cannot.
;;
;; `[log] path' is consumed: the operator opens it append-only before the
;; store (host/native/operator.lisp) and the owner writes the service log
;; lines books/owner-log.lisp renders there instead of to stderr.  It must
;; be absolute, because the service's working directory is not part of the
;; profile.
;;
;; `[posting] agent' is not a slot this node has.  The injecting agent's
;; <path-identity> is what fn writes into Path and Injection-Info (RFC 5537
;; section 3.2.1, RFC 5536 section 3.2.8), and fn keeps it in ONE place:
;; the replayed configuration policy `path-identity', which peer loop
;; suppression reads too (fn-peer-local-identity) and the owner installs
;; into every served POST (books/owner-agent.lisp fn-oag-post-config).  A
;; second value here could only disagree with Path, so the key is refused
;; by name and the operator sets `policy set path-identity IDENTITY'.
;;
;; `[anchor] server' and `[acl2]' have no native consumer.
(defun fn-native-config-log-pathp (path)
  (declare (xargs :guard t))
  (or (null path)
      (and (stringp path)
           (< 0 (length path))
           (equal (char path 0) #\/))))

(defun fn-native-config-unsupported-key (config)
  "The first key of CONFIG the native owner cannot consume, or nil."
  ; The saved image consumes the paired TLS paths through its OpenSSL boundary.
  ; Protected-only credentials therefore require a configured TLS context;
  ; the parser's paired-path check makes one certificate imply one key.
  (declare (xargs :guard t))
  (cond ((and (fn-native-config-auth-protected-onlyp config)
              (not (fn-native-config-tls-cert config)))
         "protected_only")
        ((not (booleanp (fn-native-config-posting-enabledp config))) "enabled")
        ((fn-native-config-posting-agent config) "agent")
        ((fn-native-config-anchor-server config) "anchor")
        ((not (fn-native-config-log-pathp (fn-native-config-log-path config)))
         "log")
        ((fn-native-config-acl2-path config) "acl2")
        ((fn-native-config-acl2-slots config) "acl2")
        (t nil)))

(defun fn-native-config-operator-availablep (config)
  (declare (xargs :guard t))
  (null (fn-native-config-unsupported-key config)))

(defthm fn-native-config-load-bounded-input-refuses
  (implies (or (not (fn-ncfg-ascii-octetsp octets))
               (< *fn-ncfg-max-octets* (len octets)))
           (equal (fn-native-config-load octets)
                  (list :refused :bounds-or-encoding))))

(in-theory (disable fn-native-config-load))
