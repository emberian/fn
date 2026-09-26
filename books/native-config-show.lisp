; fn: the normalized fn.toml, rendered back (PKT-096), and the missions (PKT-097).
;
; `operator CONFIG show' prints what books/native-config.lisp made of the
; file: every table and key in one canonical order, defaults filled in, as
; fn.toml text.  The operator's command reads its `[alerts]' and `[ops]'
; settings from that text rather than from its own parse of the file, and a
; mission's fn.toml is the same rendering of the mission's configuration.
; The keystone `fn-native-config-show-round-trip' says the rendering is
; exact: loading the text `show' prints gives back the configuration it was
; printed from, for every well-formed configuration, and
; `fn-native-config-load-yields-show-wfp' says every configuration the loader
; accepts is well formed.

(in-package "ACL2")
(include-book "native-config")
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))

; -----------------------------------------------------------------------------
; Values

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defun fn-ncfg-show-digits-rev (n)
    "The decimal digits of N, least significant first."
    (declare (xargs :guard t :measure (nfix n)))
    (if (or (not (natp n)) (< n 10))
        (list (+ 48 (nfix n)))
      (cons (+ 48 (mod n 10)) (fn-ncfg-show-digits-rev (floor n 10))))))

(defun fn-ncfg-show-nat (n)
  (declare (xargs :guard t))
  (fn-ncfg-reverse (fn-ncfg-show-digits-rev n)))

(defun fn-ncfg-show-string (text)
  (declare (xargs :guard t))
  (cons 34 (append (fn-record-string-octets text) (list 34))))

(defconst *fn-ncfg-true-octets* '(116 114 117 101))
(defconst *fn-ncfg-false-octets* '(102 97 108 115 101))

; A parsed value (`fn-ncfg-parse-value''s shape) as fn.toml text.
(defun fn-ncfg-show-value (pv)
  (declare (xargs :guard t))
  (let ((kind (fn-ncfg-first pv)) (x (fn-ncfg-second pv)))
    (cond ((equal kind :string) (fn-ncfg-show-string x))
          ((equal kind :bool) (if x *fn-ncfg-true-octets* *fn-ncfg-false-octets*))
          (t (fn-ncfg-show-nat x)))))

; The values `show' renders: the ones the parser produces.
(defun fn-ncfg-show-textp (x bound)
  (declare (xargs :guard t))
  (and (fn-ncfg-string-okp x bound)
       (fn-ncfg-printablep (fn-record-string-octets x))))

(defun fn-ncfg-show-valuep (pv)
  (declare (xargs :guard t))
  (and (true-listp pv) (equal (len pv) 2)
       (let ((kind (car pv)) (x (cadr pv)))
         (cond ((equal kind :string) (fn-ncfg-show-textp x *fn-ncfg-max-path*))
               ((equal kind :bool) (booleanp x))
               ((equal kind :nat) (and (natp x) (<= x *fn-ncfg-max-u64*)))
               (t nil)))))

; -----------------------------------------------------------------------------
; Lines

(defun fn-ncfg-show-header (table)
  (declare (xargs :guard t))
  (cons 91 (append (fn-record-string-octets table) (list 93))))

(defun fn-ncfg-show-line (key pv)
  (declare (xargs :guard t))
  (append (fn-record-string-octets key) (cons 61 (fn-ncfg-show-value pv))))

; One `key=value' line, or none for an unset optional key.
(defun fn-ncfg-show-entry (key pv)
  (declare (xargs :guard t))
  (if pv (list (fn-ncfg-show-line key pv)) nil))

(defun fn-ncfg-opt-string (x)
  (declare (xargs :guard t))
  (if x (list :string x) nil))

(defun fn-ncfg-opt-nat (x)
  (declare (xargs :guard t))
  (if x (list :nat x) nil))

(defun fn-native-config-show-lines (c)
  "The canonical fn.toml lines of configuration C: every table, every set key."
  (declare (xargs :guard t))
  (append
   (list (fn-ncfg-show-header "store"))
   (fn-ncfg-show-entry "path" (list :string (fn-native-config-store c)))
   (list (fn-ncfg-show-header "listener"))
   (fn-ncfg-show-entry "host" (list :string (fn-native-config-listener-host c)))
   (fn-ncfg-show-entry "port" (list :nat (fn-native-config-listener-port c)))
   (fn-ncfg-show-entry "tls_cert" (fn-ncfg-opt-string (fn-native-config-tls-cert c)))
   (fn-ncfg-show-entry "tls_key" (fn-ncfg-opt-string (fn-native-config-tls-key c)))
   (fn-ncfg-show-entry "tls_port" (fn-ncfg-opt-nat (fn-native-config-listener-tls-port c)))
   (list (fn-ncfg-show-header "auth"))
   (fn-ncfg-show-entry "required" (list :bool (fn-native-config-auth-requiredp c)))
   (fn-ncfg-show-entry "protected_only" (list :bool (fn-native-config-auth-protected-onlyp c)))
   (fn-ncfg-show-entry "path" (list :string (fn-native-config-auth-path c)))
   (list (fn-ncfg-show-header "posting"))
   (fn-ncfg-show-entry "enabled" (list :bool (fn-native-config-posting-enabledp c)))
   (fn-ncfg-show-entry "agent" (fn-ncfg-opt-string (fn-native-config-posting-agent c)))
   (list (fn-ncfg-show-header "anchor"))
   (fn-ncfg-show-entry "server" (fn-ncfg-opt-string (fn-native-config-anchor-server c)))
   (list (fn-ncfg-show-header "acl2"))
   (fn-ncfg-show-entry "path" (fn-ncfg-opt-string (fn-native-config-acl2-path c)))
   (fn-ncfg-show-entry "slots" (fn-ncfg-opt-nat (fn-native-config-acl2-slots c)))
   (list (fn-ncfg-show-header "log"))
   (fn-ncfg-show-entry "path" (fn-ncfg-opt-string (fn-native-config-log-path c)))
   (list (fn-ncfg-show-header "control"))
   (fn-ncfg-show-entry "path" (list :string (fn-native-config-control-path c)))
   (list (fn-ncfg-show-header "alerts"))
   (fn-ncfg-show-entry "command" (fn-ncfg-opt-string (fn-native-config-alerts-command c)))
   (fn-ncfg-show-entry "headroom_min_percent" (list :nat (fn-native-config-alerts-headroom-min-percent c)))
   (fn-ncfg-show-entry "refusal_rate_per_minute" (list :nat (fn-native-config-alerts-refusal-rate-per-minute c)))
   (fn-ncfg-show-entry "cooldown_seconds" (list :nat (fn-native-config-alerts-cooldown-seconds c)))
   (list (fn-ncfg-show-header "ops"))
   (fn-ncfg-show-entry "mission" (fn-ncfg-opt-string (fn-native-config-ops-mission c)))
   (fn-ncfg-show-entry "unit" (fn-ncfg-opt-string (fn-native-config-ops-unit c)))
   (fn-ncfg-show-entry "scope" (list :string (fn-native-config-ops-scope c)))
   (fn-ncfg-show-entry "keep_releases" (list :nat (fn-native-config-ops-keep-releases c)))
   (fn-ncfg-show-entry "log_max_bytes" (list :nat (fn-native-config-ops-log-max-bytes c)))
   (fn-ncfg-show-entry "log_keep" (list :nat (fn-native-config-ops-log-keep c)))
   (fn-ncfg-show-entry "memory_max" (fn-ncfg-opt-string (fn-native-config-ops-memory-max c)))))

(defun fn-ncfg-list-fix (x)
  (declare (xargs :guard t))
  (if (consp x) (cons (car x) (fn-ncfg-list-fix (cdr x))) nil))

(defun fn-ncfg-show-join (lines)
  "LINES as octets, each followed by a line feed."
  (declare (xargs :guard t))
  (if (consp lines)
      (append (fn-ncfg-list-fix (car lines)) (cons 10 (fn-ncfg-show-join (cdr lines))))
    nil))

(defun fn-native-config-show-octets (c)
  "What `operator CONFIG show' prints, and what a mission writes as fn.toml."
  (declare (xargs :guard t))
  (fn-ncfg-show-join (fn-native-config-show-lines c)))

; -----------------------------------------------------------------------------
; The configurations `show' renders exactly

(defun fn-ncfg-show-opt-textp (x bound)
  (declare (xargs :guard t))
  (or (null x) (fn-ncfg-show-textp x bound)))

(defun fn-ncfg-show-opt-natp (x ceiling)
  (declare (xargs :guard t))
  (or (null x) (and (natp x) (natp ceiling) (<= x ceiling))))

(defun fn-ncfg-show-natp (x ceiling)
  (declare (xargs :guard t))
  (and (natp x) (natp ceiling) (<= x ceiling)))

(defun fn-ncfg-show-shapep (c)
  "C is the list `fn-native-config-make' builds from its own fields."
  (declare (xargs :guard t))
  (equal c (fn-native-config-make
            (fn-native-config-store c) (fn-native-config-listener-host c)
            (fn-native-config-listener-port c) (fn-native-config-tls-cert c)
            (fn-native-config-tls-key c) (fn-native-config-auth-requiredp c)
            (fn-native-config-auth-protected-onlyp c) (fn-native-config-auth-path c)
            (fn-native-config-posting-enabledp c) (fn-native-config-posting-agent c)
            (fn-native-config-anchor-server c) (fn-native-config-log-path c)
            (fn-native-config-control-path c) (fn-native-config-acl2-path c)
            (fn-native-config-acl2-slots c) (fn-native-config-alerts-command c)
            (fn-native-config-alerts-headroom-min-percent c)
            (fn-native-config-alerts-refusal-rate-per-minute c)
            (fn-native-config-alerts-cooldown-seconds c)
            (fn-native-config-ops-mission c) (fn-native-config-ops-unit c)
            (fn-native-config-ops-scope c) (fn-native-config-ops-keep-releases c)
            (fn-native-config-ops-log-max-bytes c) (fn-native-config-ops-log-keep c)
            (fn-native-config-ops-memory-max c)
            (fn-native-config-listener-tls-port c))))

(defun fn-native-config-show-wfp (c)
  "Every field of C is one the grammar admits, with the relations normalization checks."
  (declare (xargs :guard t))
  (and (fn-ncfg-show-shapep c)
       (fn-ncfg-show-textp (fn-native-config-store c) *fn-ncfg-max-path*)
       (fn-ncfg-show-textp (fn-native-config-listener-host c) *fn-ncfg-max-text*)
       (fn-native-config-listener-hostp (fn-native-config-listener-host c))
       (fn-ncfg-show-natp (fn-native-config-listener-port c) 65535)
       (not (equal (fn-native-config-listener-port c) 0))
       (fn-ncfg-show-opt-textp (fn-native-config-tls-cert c) *fn-ncfg-max-path*)
       (fn-ncfg-show-opt-textp (fn-native-config-tls-key c) *fn-ncfg-max-path*)
       (fn-ncfg-pairedp (fn-native-config-tls-cert c) (fn-native-config-tls-key c))
       (booleanp (fn-native-config-auth-requiredp c))
       (booleanp (fn-native-config-auth-protected-onlyp c))
       (fn-ncfg-show-textp (fn-native-config-auth-path c) *fn-ncfg-max-path*)
       (booleanp (fn-native-config-posting-enabledp c))
       (fn-ncfg-show-opt-textp (fn-native-config-posting-agent c) *fn-ncfg-max-text*)
       (fn-ncfg-show-opt-textp (fn-native-config-anchor-server c) *fn-ncfg-max-server*)
       (fn-ncfg-show-opt-textp (fn-native-config-log-path c) *fn-ncfg-max-path*)
       (fn-ncfg-show-textp (fn-native-config-control-path c) *fn-ncfg-max-path*)
       (fn-ncfg-show-opt-textp (fn-native-config-acl2-path c) *fn-ncfg-max-path*)
       (fn-ncfg-show-opt-natp (fn-native-config-acl2-slots c) 65535)
       (fn-ncfg-show-opt-textp (fn-native-config-alerts-command c) *fn-ncfg-max-path*)
       (fn-ncfg-optional-absolutep (fn-native-config-alerts-command c))
       (fn-ncfg-show-natp (fn-native-config-alerts-headroom-min-percent c) 100)
       (fn-ncfg-show-natp (fn-native-config-alerts-refusal-rate-per-minute c) *fn-ncfg-max-u64*)
       (fn-ncfg-show-natp (fn-native-config-alerts-cooldown-seconds c) *fn-ncfg-max-u64*)
       (fn-ncfg-show-opt-textp (fn-native-config-ops-mission c) *fn-ncfg-max-text*)
       (fn-ncfg-optional-memberp (fn-native-config-ops-mission c) *fn-ncfg-mission-names*)
       (fn-ncfg-show-opt-textp (fn-native-config-ops-unit c) *fn-ncfg-max-text*)
       (fn-ncfg-show-textp (fn-native-config-ops-scope c) *fn-ncfg-max-text*)
       (fn-ncfg-memberp (fn-native-config-ops-scope c) *fn-ncfg-ops-scopes*)
       (fn-ncfg-show-natp (fn-native-config-ops-keep-releases c) *fn-ncfg-max-u64*)
       (not (equal (fn-native-config-ops-keep-releases c) 0))
       (fn-ncfg-show-natp (fn-native-config-ops-log-max-bytes c) *fn-ncfg-max-u64*)
       (not (equal (fn-native-config-ops-log-max-bytes c) 0))
       (fn-ncfg-show-natp (fn-native-config-ops-log-keep c) *fn-ncfg-max-u64*)
       (fn-ncfg-show-opt-textp (fn-native-config-ops-memory-max c) *fn-ncfg-max-text*)
       (fn-ncfg-show-opt-natp (fn-native-config-listener-tls-port c) 65535)
       (fn-ncfg-tls-port-okp (fn-native-config-listener-tls-port c)
                             (fn-native-config-listener-port c)
                             (fn-native-config-tls-cert c))))

; -----------------------------------------------------------------------------
; Lemmas: lists

(defun fn-ncfg-opt-pair (table key pv pairs)
  (declare (xargs :guard t))
  (if pv (cons (list table key pv) pairs) pairs))

(local
 (progn
   (defthm fn-ncfg-reverse-aux-is-revappend
     (equal (fn-ncfg-reverse-aux xs acc) (revappend xs acc)))
   (defthm fn-ncfg-reverse-is-rev
     (equal (fn-ncfg-reverse xs) (rev xs)))
   (defthm fn-ncfg-list-fix-is-list-fix
     (equal (fn-ncfg-list-fix x) (list-fix x)))
   (defthm fn-ncfg-car-of-rev
     (equal (car (rev x)) (car (last x))))
   (defthm fn-ncfg-first-is-car
     (equal (fn-ncfg-first x) (car x)))
   (defthm fn-ncfg-rest-is-cdr
     (equal (fn-ncfg-rest x) (cdr x)))
   (defthm fn-ncfg-second-is-cadr
     (equal (fn-ncfg-second x) (cadr x)))
   (defthm fn-ncfg-third-is-caddr
     (equal (fn-ncfg-third x) (caddr x)))
   (defthm fn-ncfg-string-octets-aux-true-listp
     (true-listp (fn-record-string-octets-aux chars)))
   (defthm fn-ncfg-string-octets-true-listp
     (true-listp (fn-record-string-octets x))
     :rule-classes :type-prescription)
   (defthm fn-ncfg-octets-chars-of-string-octets-aux
     (implies (character-listp chars)
              (and (fn-cbor-octet-listp (fn-record-string-octets-aux chars))
                   (equal (fn-record-octets-chars
                           (fn-record-string-octets-aux chars))
                          chars)))
     :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp))))
   (defthm fn-ncfg-octets-string-of-string-octets
     (implies (stringp name)
              (equal (fn-record-octets-string (fn-record-string-octets name))
                     name)))))

; Digits.
(defun fn-ncfg-digit-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-ncfg-digitp (car xs)) (fn-ncfg-digit-listp (cdr xs)))
    (null xs)))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm fn-ncfg-digit-listp-of-show-digits-rev
    (fn-ncfg-digit-listp (fn-ncfg-show-digits-rev n)))

  (local
   (defthm fn-ncfg-digit-listp-of-append
     (equal (fn-ncfg-digit-listp (append a b))
            (and (fn-ncfg-digit-listp (list-fix a)) (fn-ncfg-digit-listp b)))))

  (local
   (defthm fn-ncfg-digit-listp-of-rev
     (implies (fn-ncfg-digit-listp xs) (fn-ncfg-digit-listp (rev xs)))))

  (defthm fn-ncfg-digit-listp-of-show-nat
    (fn-ncfg-digit-listp (fn-ncfg-show-nat n)))

  (local
   (defthm fn-ncfg-decimal-aux-of-append
     (implies (and (fn-ncfg-digit-listp xs) (natp v))
              (equal (fn-ncfg-decimal-aux (append xs ys) v)
                     (fn-ncfg-decimal-aux ys (fn-ncfg-decimal-aux xs v))))))

  (local
   (defthm fn-ncfg-decimal-aux-natp
     (implies (and (fn-ncfg-digit-listp xs) (natp v))
              (natp (fn-ncfg-decimal-aux xs v)))
     :rule-classes (:rewrite :type-prescription)))

  (local
   (defthm fn-ncfg-decimal-aux-of-rev-digits
     (implies (natp n)
              (equal (fn-ncfg-decimal-aux (rev (fn-ncfg-show-digits-rev n)) 0) n))))

  (defthm fn-ncfg-decimal-aux-of-show-nat
    (implies (natp n)
             (equal (fn-ncfg-decimal-aux (fn-ncfg-show-nat n) 0) n))))

(encapsulate ()
  (local (defun fn-ncfg-pow10 (k) (if (zp k) 1 (* 10 (fn-ncfg-pow10 (1- k))))))
  (local
   (encapsulate ()
     (local (include-book "arithmetic-5/top" :dir :system))
     (defthm fn-ncfg-floor-10-below
       (implies (and (natp n) (natp p) (< n (* 10 p))) (< (floor n 10) p))
       :rule-classes :linear)
     (defthm fn-ncfg-floor-10-less
       (implies (and (natp n) (<= 10 n)) (< (floor n 10) n))
       :rule-classes :linear)
     (defthm fn-ncfg-floor-10-natp
       (implies (natp n) (natp (floor n 10)))
       :rule-classes :type-prescription)))
  (local
   (defun fn-ncfg-digits-induct (n k)
     (declare (xargs :measure (nfix n)
                     :hints (("Goal" :in-theory (disable floor)))))
     (if (or (not (natp n)) (< n 10)) k (fn-ncfg-digits-induct (floor n 10) (1- k)))))
  (local
   (defthm fn-ncfg-len-show-digits-rev-bound
     (implies (and (natp n) (posp k) (< n (fn-ncfg-pow10 k)))
              (<= (len (fn-ncfg-show-digits-rev n)) k))
     :hints (("Goal" :induct (fn-ncfg-digits-induct n k)
              :in-theory (disable floor)
              :expand ((fn-ncfg-pow10 k) (fn-ncfg-show-digits-rev n))))
     :rule-classes nil))
  (defthm fn-ncfg-len-show-nat
    (implies (and (natp n) (<= n *fn-ncfg-max-u64*))
             (and (consp (fn-ncfg-show-nat n))
                  (<= (len (fn-ncfg-show-nat n)) 20)))
    :hints (("Goal" :use ((:instance fn-ncfg-len-show-digits-rev-bound (k 20)))
             :in-theory (disable floor))))
  (defthm fn-ncfg-decimal-of-show-nat
    (implies (and (natp n) (<= n *fn-ncfg-max-u64*))
             (equal (fn-ncfg-decimal (fn-ncfg-show-nat n)) n))
    :hints (("Goal" :in-theory (disable fn-ncfg-show-nat)))))

; Values parse back.
(defun fn-ncfg-show-octetp (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x 127) (not (equal x 10))))

(defun fn-ncfg-show-octetsp (xs)
  "A true list of ASCII octets with no line feed."
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-ncfg-show-octetp (car xs)) (fn-ncfg-show-octetsp (cdr xs)))
    (null xs)))

(local
 (progn
   (defthm fn-ncfg-show-octetsp-of-append
     (equal (fn-ncfg-show-octetsp (append a b))
            (and (fn-ncfg-show-octetsp (list-fix a)) (fn-ncfg-show-octetsp b))))
   (defthm fn-ncfg-show-octetsp-of-rev
     (implies (fn-ncfg-show-octetsp xs) (fn-ncfg-show-octetsp (rev xs))))
   (defthm fn-ncfg-show-octetsp-of-printable
     (implies (and (fn-ncfg-printablep xs) (true-listp xs))
              (fn-ncfg-show-octetsp xs)))
   (defthm fn-ncfg-show-octetsp-of-digits
     (implies (fn-ncfg-digit-listp xs) (fn-ncfg-show-octetsp xs)))
   (defthm fn-ncfg-show-octetsp-of-ident-tail
     (implies (and (fn-ncfg-identp-tail xs) (true-listp xs))
              (fn-ncfg-show-octetsp xs)))
   (defthm fn-ncfg-show-octetsp-true-listp
     (implies (fn-ncfg-show-octetsp xs) (true-listp xs))
     :rule-classes :forward-chaining)
   (defthm fn-ncfg-digit-listp-true-listp
     (implies (fn-ncfg-digit-listp xs) (true-listp xs))
     :rule-classes :forward-chaining)

   (defthm fn-ncfg-parse-value-of-show-string
     (implies (and (stringp x) (fn-ncfg-printablep (fn-record-string-octets x)))
              (equal (fn-ncfg-parse-value (fn-ncfg-show-string x))
                     (list :string x)))
     :hints (("Goal" :in-theory (enable fn-ncfg-quoted-value))))

   (defthm fn-ncfg-digit-list-not-literal
     (implies (and (fn-ncfg-digit-listp xs) (consp xs))
              (and (not (equal xs '(116 114 117 101)))
                   (not (equal xs '(102 97 108 115 101)))
                   (not (equal (car xs) 34)))))

   (defthm fn-ncfg-parse-value-of-show-nat
     (implies (and (natp n) (<= n *fn-ncfg-max-u64*))
              (equal (fn-ncfg-parse-value (fn-ncfg-show-nat n))
                     (list :nat n)))
     :hints (("Goal" :in-theory (disable fn-ncfg-show-nat fn-ncfg-decimal
                                         fn-ncfg-digit-list-not-literal)
              :use ((:instance fn-ncfg-digit-list-not-literal
                               (xs (fn-ncfg-show-nat n)))))))

   (defthm fn-ncfg-len-2-shape
     (implies (and (true-listp x) (equal (len x) 2))
              (equal (list (car x) (cadr x)) x))
     :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)))))
     :rule-classes nil)
   (defthm fn-ncfg-show-valuep-shape
     (implies (fn-ncfg-show-valuep pv)
              (equal (list (car pv) (cadr pv)) pv))
     :hints (("Goal" :use ((:instance fn-ncfg-len-2-shape (x pv)))))
     :rule-classes nil)

   (defthm fn-ncfg-parse-value-of-show-value
     (implies (fn-ncfg-show-valuep pv)
              (equal (fn-ncfg-parse-value (fn-ncfg-show-value pv)) pv))
     :hints (("Goal" :in-theory (disable fn-ncfg-show-nat fn-ncfg-show-string
                                         fn-ncfg-parse-value)
              :use fn-ncfg-show-valuep-shape)))

   (defthm fn-ncfg-digit-list-ends
     (implies (and (fn-ncfg-digit-listp xs) (consp xs))
              (and (not (fn-ncfg-ws-p (car xs)))
                   (not (fn-ncfg-ws-p (car (last xs)))))))
   (defthm fn-ncfg-last-of-append-consp
     (implies (consp b) (equal (last (append a b)) (last b))))
   (defthm fn-ncfg-show-value-shape
     (implies (fn-ncfg-show-valuep pv)
              (and (consp (fn-ncfg-show-value pv))
                   (fn-ncfg-show-octetsp (fn-ncfg-show-value pv))
                   (not (fn-ncfg-ws-p (car (fn-ncfg-show-value pv))))
                   (not (fn-ncfg-ws-p (car (last (fn-ncfg-show-value pv)))))))
     :hints (("Goal" :in-theory (disable fn-ncfg-show-nat fn-record-string-octets)
              :use ((:instance fn-ncfg-len-show-nat (n (cadr pv)))
                    (:instance fn-ncfg-digit-listp-of-show-nat (n (cadr pv)))
                    (:instance fn-ncfg-digit-list-ends (xs (fn-ncfg-show-nat (cadr pv))))))))

   ; Trimming a line that starts and ends with a non-blank is the identity.
   (defthm fn-ncfg-trim-left-noop
     (implies (not (fn-ncfg-ws-p (car xs)))
              (equal (fn-ncfg-trim-left xs) xs)))
   (defthm fn-ncfg-trim-right-rev-noop
     (implies (not (fn-ncfg-ws-p (car xs)))
              (equal (fn-ncfg-trim-right-rev xs) xs)))
   (defthm fn-ncfg-trim-noop
     (implies (and (true-listp xs)
                   (not (fn-ncfg-ws-p (car xs)))
                   (not (fn-ncfg-ws-p (car (last xs)))))
              (equal (fn-ncfg-trim xs) xs)))

   (defun fn-ncfg-no-equals-p (xs)
     (if (consp xs)
         (and (not (equal (car xs) 61)) (fn-ncfg-no-equals-p (cdr xs)))
       t))
   (defthm fn-ncfg-ident-tail-no-equals
     (implies (fn-ncfg-identp-tail xs) (fn-ncfg-no-equals-p xs)))
   (defthm fn-ncfg-split-equals-of-line
     (implies (fn-ncfg-no-equals-p k)
              (equal (fn-ncfg-split-equals (append k (cons 61 v)) acc)
                     (list (rev (revappend k acc)) v)))
     :hints (("Goal" :induct (fn-ncfg-reverse-aux k acc)
              :in-theory (disable fn-ncfg-reverse-aux-is-revappend))))))

; -----------------------------------------------------------------------------
; Lines parse back.

(defun fn-ncfg-show-pvp (pv)
  (declare (xargs :guard t))
  (or (null pv) (fn-ncfg-show-valuep pv)))

(local
 (progn
   (defthm fn-ncfg-identp-parts
     (implies (fn-ncfg-identp xs)
              (and (consp xs)
                   (true-listp (list-fix xs))
                   (fn-ncfg-identp-tail xs)
                   (not (fn-ncfg-ws-p (car xs)))
                   (not (equal (car xs) 35))
                   (not (equal (car xs) 91))
                   (not (equal (car xs) 61))
                   (not (fn-ncfg-ws-p (car (last xs))))))
     :hints (("Goal" :in-theory (enable fn-ncfg-identp))))

   (defthm fn-ncfg-show-line-facts
     (implies (and (fn-ncfg-identp (fn-record-string-octets key))
                   (fn-ncfg-show-valuep pv))
              (and (consp (fn-ncfg-show-line key pv))
                   (not (equal (car (fn-ncfg-show-line key pv)) 35))
                   (not (equal (car (fn-ncfg-show-line key pv)) 91))
                   (equal (fn-ncfg-trim (fn-ncfg-show-line key pv))
                          (fn-ncfg-show-line key pv))
                   (equal (fn-ncfg-split-equals (fn-ncfg-show-line key pv) nil)
                          (list (fn-record-string-octets key)
                                (fn-ncfg-show-value pv)))
                   (equal (fn-ncfg-trim (fn-record-string-octets key))
                          (fn-record-string-octets key))
                   (equal (fn-ncfg-trim (fn-ncfg-show-value pv))
                          (fn-ncfg-show-value pv))))
     :hints (("Goal" :in-theory (e/d (fn-ncfg-show-line)
                                     (fn-ncfg-show-value fn-ncfg-identp fn-ncfg-trim
                                      fn-record-string-octets fn-ncfg-show-valuep))
              :use ((:instance fn-ncfg-identp-parts (xs (fn-record-string-octets key)))
                    (:instance fn-ncfg-show-value-shape)
                    (:instance fn-ncfg-trim-noop (xs (fn-ncfg-show-line key pv)))
                    (:instance fn-ncfg-trim-noop (xs (fn-record-string-octets key)))
                    (:instance fn-ncfg-trim-noop (xs (fn-ncfg-show-value pv)))))))

   (defthm fn-ncfg-parse-lines-of-entry
     (implies (and (stringp key)
                   (fn-ncfg-key-allowedp current key)
                   (fn-ncfg-identp (fn-record-string-octets key))
                   (fn-ncfg-show-pvp pv)
                   (not (fn-ncfg-pair-seenp pairs current key)))
              (equal (fn-ncfg-parse-lines (append (fn-ncfg-show-entry key pv) rest)
                                          current tables pairs)
                     (fn-ncfg-parse-lines rest current tables
                                          (fn-ncfg-opt-pair current key pv pairs))))
     :hints (("Goal" :expand ((fn-ncfg-parse-lines
                               (cons (fn-ncfg-show-line key pv) rest)
                               current tables pairs))
              :in-theory (disable fn-ncfg-show-line fn-ncfg-show-value fn-ncfg-identp
                                  fn-ncfg-trim fn-ncfg-parse-value fn-ncfg-key-allowedp
                                  fn-record-string-octets fn-ncfg-split-equals
                                  fn-ncfg-show-valuep fn-ncfg-pair-seenp
                                  fn-record-octets-string))))

   (defthm fn-ncfg-parse-lines-of-header
     (implies (and (fn-ncfg-tablep name)
                   (fn-ncfg-identp (fn-record-string-octets name))
                   (not (fn-ncfg-table-seenp tables name)))
              (equal (fn-ncfg-parse-lines (cons (fn-ncfg-show-header name) rest)
                                          current tables pairs)
                     (fn-ncfg-parse-lines rest name (cons name tables) pairs)))
     :hints (("Goal" :expand ((fn-ncfg-parse-lines
                               (cons (fn-ncfg-show-header name) rest)
                               current tables pairs))
              :in-theory (disable fn-ncfg-identp fn-ncfg-trim fn-ncfg-tablep
                                  fn-ncfg-table-seenp))))

   (defthm fn-ncfg-parse-lines-of-last
     (equal (fn-ncfg-parse-lines (list nil) current tables pairs) pairs))

   (defthm fn-ncfg-pair-seenp-of-opt-pair
     (equal (fn-ncfg-pair-seenp (fn-ncfg-opt-pair c k pv pairs) table key)
            (or (and pv (equal c table) (equal k key))
                (fn-ncfg-pair-seenp pairs table key))))

   (defthm fn-ncfg-value-of-opt-pair
     (equal (fn-ncfg-value (fn-ncfg-opt-pair c k pv pairs) table key)
            (if (and (equal c table) (equal k key))
                (if pv pv (fn-ncfg-value pairs table key))
              (fn-ncfg-value pairs table key))))

   ; Lines of the joined text.
   (defun fn-ncfg-show-lines-okp (lines)
     (if (consp lines)
         (and (fn-ncfg-show-octetsp (car lines))
              (fn-ncfg-show-lines-okp (cdr lines)))
       t))

   (defthm fn-ncfg-lines-aux-of-line
     (implies (fn-ncfg-show-octetsp line)
              (equal (fn-ncfg-lines-aux (append line (cons 10 rest)) cur acc)
                     (fn-ncfg-lines-aux rest nil (cons (rev (revappend line cur)) acc))))
     :hints (("Goal" :induct (fn-ncfg-reverse-aux line cur)
              :in-theory (disable fn-ncfg-reverse-aux-is-revappend))))

   (defthm fn-ncfg-lines-aux-of-join
     (implies (fn-ncfg-show-lines-okp lines)
              (equal (fn-ncfg-lines-aux (fn-ncfg-show-join lines) nil acc)
                     (rev (cons nil (revappend lines acc)))))
     :hints (("Goal" :induct (fn-ncfg-reverse-aux lines acc)
              :in-theory (disable fn-ncfg-reverse-aux-is-revappend)
              :expand ((fn-ncfg-show-join lines)))))

   (defthm fn-ncfg-lines-of-join
     (implies (and (fn-ncfg-show-lines-okp lines) (true-listp lines))
              (equal (fn-ncfg-lines (fn-ncfg-show-join lines))
                     (append lines (list nil)))))

   (defthm fn-ncfg-show-join-of-append
     (equal (fn-ncfg-show-join (append a b))
            (append (fn-ncfg-show-join a) (fn-ncfg-show-join b))))

   (defthm fn-ncfg-ascii-of-show-octets
     (implies (fn-ncfg-show-octetsp xs) (fn-ncfg-ascii-octetsp xs)))

   (defthm fn-ncfg-ascii-octetsp-of-append
     (equal (fn-ncfg-ascii-octetsp (append a b))
            (and (fn-ncfg-ascii-octetsp (list-fix a)) (fn-ncfg-ascii-octetsp b))))

   (defthm fn-ncfg-ascii-of-join
     (implies (fn-ncfg-show-lines-okp lines)
              (fn-ncfg-ascii-octetsp (fn-ncfg-show-join lines))))

   (defthm fn-ncfg-show-lines-okp-of-append
     (equal (fn-ncfg-show-lines-okp (append a b))
            (and (fn-ncfg-show-lines-okp a) (fn-ncfg-show-lines-okp b))))))


(defun fn-ncfg-show-pairs (c)
  "The pairs `fn-ncfg-parse-lines' collects from the lines of C, newest first."
  (declare (xargs :guard t))
  (fn-ncfg-opt-pair "ops" "memory_max" (fn-ncfg-opt-string (fn-native-config-ops-memory-max c))
    (fn-ncfg-opt-pair "ops" "log_keep" (list :nat (fn-native-config-ops-log-keep c))
    (fn-ncfg-opt-pair "ops" "log_max_bytes" (list :nat (fn-native-config-ops-log-max-bytes c))
    (fn-ncfg-opt-pair "ops" "keep_releases" (list :nat (fn-native-config-ops-keep-releases c))
    (fn-ncfg-opt-pair "ops" "scope" (list :string (fn-native-config-ops-scope c))
    (fn-ncfg-opt-pair "ops" "unit" (fn-ncfg-opt-string (fn-native-config-ops-unit c))
    (fn-ncfg-opt-pair "ops" "mission" (fn-ncfg-opt-string (fn-native-config-ops-mission c))
    (fn-ncfg-opt-pair "alerts" "cooldown_seconds" (list :nat (fn-native-config-alerts-cooldown-seconds c))
    (fn-ncfg-opt-pair "alerts" "refusal_rate_per_minute" (list :nat (fn-native-config-alerts-refusal-rate-per-minute c))
    (fn-ncfg-opt-pair "alerts" "headroom_min_percent" (list :nat (fn-native-config-alerts-headroom-min-percent c))
    (fn-ncfg-opt-pair "alerts" "command" (fn-ncfg-opt-string (fn-native-config-alerts-command c))
    (fn-ncfg-opt-pair "control" "path" (list :string (fn-native-config-control-path c))
    (fn-ncfg-opt-pair "log" "path" (fn-ncfg-opt-string (fn-native-config-log-path c))
    (fn-ncfg-opt-pair "acl2" "slots" (fn-ncfg-opt-nat (fn-native-config-acl2-slots c))
    (fn-ncfg-opt-pair "acl2" "path" (fn-ncfg-opt-string (fn-native-config-acl2-path c))
    (fn-ncfg-opt-pair "anchor" "server" (fn-ncfg-opt-string (fn-native-config-anchor-server c))
    (fn-ncfg-opt-pair "posting" "agent" (fn-ncfg-opt-string (fn-native-config-posting-agent c))
    (fn-ncfg-opt-pair "posting" "enabled" (list :bool (fn-native-config-posting-enabledp c))
    (fn-ncfg-opt-pair "auth" "path" (list :string (fn-native-config-auth-path c))
    (fn-ncfg-opt-pair "auth" "protected_only" (list :bool (fn-native-config-auth-protected-onlyp c))
    (fn-ncfg-opt-pair "auth" "required" (list :bool (fn-native-config-auth-requiredp c))
    (fn-ncfg-opt-pair "listener" "tls_port" (fn-ncfg-opt-nat (fn-native-config-listener-tls-port c))
    (fn-ncfg-opt-pair "listener" "tls_key" (fn-ncfg-opt-string (fn-native-config-tls-key c))
    (fn-ncfg-opt-pair "listener" "tls_cert" (fn-ncfg-opt-string (fn-native-config-tls-cert c))
    (fn-ncfg-opt-pair "listener" "port" (list :nat (fn-native-config-listener-port c))
    (fn-ncfg-opt-pair "listener" "host" (list :string (fn-native-config-listener-host c))
    (fn-ncfg-opt-pair "store" "path" (list :string (fn-native-config-store c))
    nil))))))))))))))))))))))))))))

; -----------------------------------------------------------------------------
; Normalization gives the fields back.

(local
 (progn
   (defthm fn-ncfg-string-value-of-string
     (implies (and (natp bound) (fn-ncfg-string-okp x bound))
              (equal (fn-ncfg-string-value (list :string x) default bound requiredp) x)))
   (defthm fn-ncfg-string-value-of-opt-string
     (implies (and (natp bound) (fn-ncfg-show-opt-textp x bound))
              (equal (fn-ncfg-string-value (fn-ncfg-opt-string x) nil bound nil) x)))
   (defthm fn-ncfg-bool-value-of-bool
     (implies (booleanp b) (equal (fn-ncfg-bool-value (list :bool b) default) b)))
   (defthm fn-ncfg-nat-value-of-nat
     (implies (fn-ncfg-show-natp n ceiling)
              (equal (fn-ncfg-nat-value (list :nat n) default ceiling) n)))
   (defthm fn-ncfg-nat-value-of-opt-nat
     (implies (and (natp ceiling) (fn-ncfg-show-opt-natp n ceiling))
              (equal (fn-ncfg-nat-value (fn-ncfg-opt-nat n) nil ceiling) n)))

   (defthm fn-ncfg-show-textp-facts
     (implies (fn-ncfg-show-textp x b)
              (and (stringp x) (fn-ncfg-string-okp x b)))
     :rule-classes :forward-chaining)
   (defthm fn-ncfg-show-opt-textp-facts
     (implies (fn-ncfg-show-opt-textp x b)
              (and (not (equal x :bad)) (or (null x) (stringp x))))
     :rule-classes :forward-chaining)
   (defthm fn-ncfg-show-natp-facts
     (implies (fn-ncfg-show-natp x c) (natp x))
     :rule-classes :forward-chaining)
   (defthm fn-ncfg-show-opt-natp-facts
     (implies (fn-ncfg-show-opt-natp x c) (not (equal x :bad)))
     :rule-classes :forward-chaining)

   (defthm fn-ncfg-show-pvp-of-string
     (implies (and (fn-ncfg-show-textp x b) (<= b *fn-ncfg-max-path*))
              (fn-ncfg-show-pvp (list :string x))))
   (defthm fn-ncfg-show-pvp-of-opt-string
     (implies (and (fn-ncfg-show-opt-textp x b) (<= b *fn-ncfg-max-path*))
              (fn-ncfg-show-pvp (fn-ncfg-opt-string x))))
   (defthm fn-ncfg-show-pvp-of-nat
     (implies (and (fn-ncfg-show-natp n c) (<= c *fn-ncfg-max-u64*))
              (fn-ncfg-show-pvp (list :nat n))))
   (defthm fn-ncfg-show-pvp-of-opt-nat
     (implies (and (fn-ncfg-show-opt-natp n c) (<= c *fn-ncfg-max-u64*))
              (fn-ncfg-show-pvp (fn-ncfg-opt-nat n))))
   (defthm fn-ncfg-show-pvp-of-bool
     (implies (booleanp b) (fn-ncfg-show-pvp (list :bool b))))

   (defthm fn-ncfg-show-lines-okp-of-entry
     (implies (and (fn-ncfg-identp (fn-record-string-octets key))
                   (fn-ncfg-show-pvp pv))
              (fn-ncfg-show-lines-okp (fn-ncfg-show-entry key pv)))
     :hints (("Goal" :in-theory (e/d (fn-ncfg-show-line)
                                     (fn-ncfg-show-value fn-ncfg-identp
                                      fn-record-string-octets fn-ncfg-show-valuep))
              :use ((:instance fn-ncfg-identp-parts (xs (fn-record-string-octets key)))
                    (:instance fn-ncfg-show-value-shape)))))

   (defthm fn-ncfg-len-show-entry
     (<= (len (fn-ncfg-show-entry key pv)) 1)
     :rule-classes :linear)

   ; Lengths.
   (defthm fn-ncfg-len-string-octets-of-textp
     (implies (fn-ncfg-show-opt-textp x b)
              (<= (len (fn-record-string-octets x)) (nfix b)))
     :rule-classes :linear)
   (defthm fn-ncfg-len-string-octets-of-show-textp
     (implies (fn-ncfg-show-textp x b)
              (<= (len (fn-record-string-octets x)) (nfix b)))
     :rule-classes :linear)
   (defthm fn-ncfg-len-join-entry-string
     (implies (fn-ncfg-show-textp x b)
              (<= (len (fn-ncfg-show-join (fn-ncfg-show-entry key (list :string x))))
                  (+ 4 (len (fn-record-string-octets key)) (nfix b))))
     :hints (("Goal" :in-theory (enable fn-ncfg-show-line)))
     :rule-classes :linear)
   (defthm fn-ncfg-len-join-entry-opt-string
     (implies (fn-ncfg-show-opt-textp x b)
              (<= (len (fn-ncfg-show-join (fn-ncfg-show-entry key (fn-ncfg-opt-string x))))
                  (+ 4 (len (fn-record-string-octets key)) (nfix b))))
     :hints (("Goal" :in-theory (enable fn-ncfg-show-line)))
     :rule-classes :linear)
   (defthm fn-ncfg-len-show-nat-linear
     (implies (and (natp n) (<= n *fn-ncfg-max-u64*))
              (<= (len (fn-ncfg-show-nat n)) 20))
     :hints (("Goal" :use fn-ncfg-len-show-nat :in-theory (disable fn-ncfg-show-nat)))
     :rule-classes :linear)
   (defthm fn-ncfg-len-join-entry-nat
     (implies (and (fn-ncfg-show-natp n c) (<= c *fn-ncfg-max-u64*))
              (<= (len (fn-ncfg-show-join (fn-ncfg-show-entry key (list :nat n))))
                  (+ 22 (len (fn-record-string-octets key)))))
     :hints (("Goal" :in-theory (e/d (fn-ncfg-show-line) (fn-ncfg-show-nat))))
     :rule-classes :linear)
   (defthm fn-ncfg-len-join-entry-opt-nat
     (implies (and (fn-ncfg-show-opt-natp n c) (<= c *fn-ncfg-max-u64*))
              (<= (len (fn-ncfg-show-join (fn-ncfg-show-entry key (fn-ncfg-opt-nat n))))
                  (+ 22 (len (fn-record-string-octets key)))))
     :hints (("Goal" :in-theory (e/d (fn-ncfg-show-line) (fn-ncfg-show-nat))))
     :rule-classes :linear)
   (defthm fn-ncfg-len-join-entry-bool
     (<= (len (fn-ncfg-show-join (fn-ncfg-show-entry key (list :bool b))))
         (+ 7 (len (fn-record-string-octets key))))
     :hints (("Goal" :in-theory (enable fn-ncfg-show-line)))
     :rule-classes :linear)

   (defthm fn-ncfg-show-natp-weaken
     (implies (and (fn-ncfg-show-natp n c) (<= c *fn-ncfg-max-u64*))
              (fn-ncfg-show-natp n *fn-ncfg-max-u64*)))
   (defthm fn-ncfg-show-opt-natp-weaken
     (implies (and (fn-ncfg-show-opt-natp n c) (<= c *fn-ncfg-max-u64*))
              (fn-ncfg-show-opt-natp n *fn-ncfg-max-u64*)))

   (defthm fn-ncfg-show-shapep-make
     (implies (fn-ncfg-show-shapep c)
              (equal (fn-native-config-make
                      (fn-native-config-store c) (fn-native-config-listener-host c)
                      (fn-native-config-listener-port c) (fn-native-config-tls-cert c)
                      (fn-native-config-tls-key c) (fn-native-config-auth-requiredp c)
                      (fn-native-config-auth-protected-onlyp c) (fn-native-config-auth-path c)
                      (fn-native-config-posting-enabledp c) (fn-native-config-posting-agent c)
                      (fn-native-config-anchor-server c) (fn-native-config-log-path c)
                      (fn-native-config-control-path c) (fn-native-config-acl2-path c)
                      (fn-native-config-acl2-slots c) (fn-native-config-alerts-command c)
                      (fn-native-config-alerts-headroom-min-percent c)
                      (fn-native-config-alerts-refusal-rate-per-minute c)
                      (fn-native-config-alerts-cooldown-seconds c)
                      (fn-native-config-ops-mission c) (fn-native-config-ops-unit c)
                      (fn-native-config-ops-scope c) (fn-native-config-ops-keep-releases c)
                      (fn-native-config-ops-log-max-bytes c) (fn-native-config-ops-log-keep c)
                      (fn-native-config-ops-memory-max c)
                      (fn-native-config-listener-tls-port c))
                     c)))))

(local
 (progn
   (defthm fn-ncfg-opt-pair-of-nil
     (equal (fn-ncfg-opt-pair c k nil pairs) pairs))
   (defthm fn-ncfg-show-lines-okp-of-header
     (implies (fn-ncfg-identp (fn-record-string-octets name))
              (fn-ncfg-show-octetsp (fn-ncfg-show-header name)))
     :hints (("Goal" :in-theory (disable fn-ncfg-identp fn-record-string-octets)
              :use ((:instance fn-ncfg-identp-parts (xs (fn-record-string-octets name)))))))
   (defthm fn-ncfg-len-show-header
     (equal (len (fn-ncfg-show-header name))
            (+ 2 (len (fn-record-string-octets name)))))))

(local
 (defthm fn-ncfg-show-join-of-cons
   (equal (fn-ncfg-show-join (cons a b))
          (append (list-fix a) (cons 10 (fn-ncfg-show-join b))))))

(local
 (defthm fn-ncfg-show-lines-parse
   (implies (fn-native-config-show-wfp c)
            (equal (fn-ncfg-parse-lines (append (fn-native-config-show-lines c) (list nil))
                                        nil nil nil)
                   (fn-ncfg-show-pairs c)))
   :hints (("Goal" :in-theory (e/d (fn-native-config-show-wfp)
                                   (fn-ncfg-show-entry fn-ncfg-show-header
                                    fn-ncfg-opt-string fn-ncfg-opt-nat fn-ncfg-opt-pair
                                    fn-ncfg-show-textp fn-ncfg-show-opt-textp
                                    fn-ncfg-show-natp fn-ncfg-show-opt-natp
                                    fn-ncfg-show-shapep fn-ncfg-show-pvp
                                    fn-ncfg-parse-lines
                                    fn-native-config-listener-hostp
                                    fn-ncfg-optional-absolutep fn-ncfg-optional-memberp
                                    fn-ncfg-memberp fn-native-config-store fn-native-config-listener-host
                                    fn-native-config-listener-port fn-native-config-tls-cert
                                    fn-native-config-tls-key fn-native-config-auth-requiredp
                                    fn-native-config-auth-protected-onlyp
                                    fn-native-config-auth-path
                                    fn-native-config-posting-enabledp
                                    fn-native-config-posting-agent
                                    fn-native-config-anchor-server fn-native-config-log-path
                                    fn-native-config-control-path fn-native-config-acl2-path
                                    fn-native-config-acl2-slots fn-native-config-alerts-command
                                    fn-native-config-alerts-headroom-min-percent
                                    fn-native-config-alerts-refusal-rate-per-minute
                                    fn-native-config-alerts-cooldown-seconds
                                    fn-native-config-ops-mission fn-native-config-ops-unit
                                    fn-native-config-ops-scope fn-native-config-ops-keep-releases
                                    fn-native-config-ops-log-max-bytes
                                    fn-native-config-ops-log-keep
                                    fn-native-config-ops-memory-max
                                    fn-native-config-listener-tls-port fn-ncfg-tls-port-okp
                                    (:e fn-ncfg-show-header)))))))

(local
 (defthm fn-ncfg-normalize-of-show-pairs
   (implies (fn-native-config-show-wfp c)
            (equal (fn-ncfg-normalize (fn-ncfg-show-pairs c)) c))
   :hints (("Goal" :use fn-ncfg-show-shapep-make :in-theory (e/d (fn-native-config-show-wfp)
                                   (fn-ncfg-opt-string fn-ncfg-opt-nat fn-ncfg-opt-pair
                                    fn-ncfg-string-value fn-ncfg-bool-value
                                    fn-ncfg-nat-value fn-ncfg-show-textp
                                    fn-ncfg-show-opt-textp fn-ncfg-show-natp
                                    fn-ncfg-show-opt-natp fn-ncfg-show-shapep
                                    fn-native-config-listener-hostp
                                    fn-ncfg-optional-absolutep fn-ncfg-optional-memberp
                                    fn-ncfg-memberp fn-ncfg-under-store fn-ncfg-pairedp
                                    fn-native-config-make fn-native-config-store fn-native-config-listener-host
                                    fn-native-config-listener-port fn-native-config-tls-cert
                                    fn-native-config-tls-key fn-native-config-auth-requiredp
                                    fn-native-config-auth-protected-onlyp
                                    fn-native-config-auth-path
                                    fn-native-config-posting-enabledp
                                    fn-native-config-posting-agent
                                    fn-native-config-anchor-server fn-native-config-log-path
                                    fn-native-config-control-path fn-native-config-acl2-path
                                    fn-native-config-acl2-slots fn-native-config-alerts-command
                                    fn-native-config-alerts-headroom-min-percent
                                    fn-native-config-alerts-refusal-rate-per-minute
                                    fn-native-config-alerts-cooldown-seconds
                                    fn-native-config-ops-mission fn-native-config-ops-unit
                                    fn-native-config-ops-scope fn-native-config-ops-keep-releases
                                    fn-native-config-ops-log-max-bytes
                                    fn-native-config-ops-log-keep
                                    fn-native-config-ops-memory-max
                                    fn-native-config-listener-tls-port fn-ncfg-tls-port-okp))))))

(local
 (defthm fn-ncfg-show-bounds
   (implies (fn-native-config-show-wfp c)
            (and (fn-ncfg-show-lines-okp (fn-native-config-show-lines c))
                 (true-listp (fn-native-config-show-lines c))
                 (<= (len (fn-native-config-show-lines c)) 127)
                 (<= (len (fn-native-config-show-octets c)) *fn-ncfg-max-octets*)))
   :hints (("Goal" :in-theory (e/d (fn-native-config-show-wfp)
                                   (fn-ncfg-show-entry fn-ncfg-show-header
                                    fn-ncfg-opt-string fn-ncfg-opt-nat
                                    fn-ncfg-show-textp fn-ncfg-show-opt-textp
                                    fn-ncfg-show-natp fn-ncfg-show-opt-natp
                                    fn-ncfg-show-shapep fn-ncfg-show-pvp
                                    fn-ncfg-show-join
                                    fn-native-config-listener-hostp
                                    fn-ncfg-optional-absolutep fn-ncfg-optional-memberp
                                    fn-ncfg-memberp fn-record-string-octets fn-native-config-store fn-native-config-listener-host
                                    fn-native-config-listener-port fn-native-config-tls-cert
                                    fn-native-config-tls-key fn-native-config-auth-requiredp
                                    fn-native-config-auth-protected-onlyp
                                    fn-native-config-auth-path
                                    fn-native-config-posting-enabledp
                                    fn-native-config-posting-agent
                                    fn-native-config-anchor-server fn-native-config-log-path
                                    fn-native-config-control-path fn-native-config-acl2-path
                                    fn-native-config-acl2-slots fn-native-config-alerts-command
                                    fn-native-config-alerts-headroom-min-percent
                                    fn-native-config-alerts-refusal-rate-per-minute
                                    fn-native-config-alerts-cooldown-seconds
                                    fn-native-config-ops-mission fn-native-config-ops-unit
                                    fn-native-config-ops-scope fn-native-config-ops-keep-releases
                                    fn-native-config-ops-log-max-bytes
                                    fn-native-config-ops-log-keep
                                    fn-native-config-ops-memory-max
                                    fn-native-config-listener-tls-port fn-ncfg-tls-port-okp
                                    (:e fn-ncfg-show-header)))))))

(local
 (progn
   (defthm fn-ncfg-show-bounds-lines
     (implies (fn-native-config-show-wfp c)
              (< (len (fn-native-config-show-lines c)) 128))
     :hints (("Goal" :use fn-ncfg-show-bounds :in-theory (disable fn-native-config-show-wfp
                                                                  fn-native-config-show-lines)))
     :rule-classes :linear)
   (defthm fn-ncfg-show-bounds-octets
     (implies (fn-native-config-show-wfp c)
              (<= (len (fn-ncfg-show-join (fn-native-config-show-lines c))) 16384))
     :hints (("Goal" :use fn-ncfg-show-bounds :in-theory (disable fn-native-config-show-wfp
                                                                  fn-native-config-show-lines)))
     :rule-classes :linear)
   (defthm fn-ncfg-show-bounds-okp
     (implies (fn-native-config-show-wfp c)
              (and (fn-ncfg-show-lines-okp (fn-native-config-show-lines c))
                   (true-listp (fn-native-config-show-lines c))))
     :hints (("Goal" :use fn-ncfg-show-bounds :in-theory (disable fn-native-config-show-wfp
                                                                  fn-native-config-show-lines))))))

; KEYSTONE (PKT-096).  The subject is `fn-native-config-load', which every
; operator verb reads fn.toml through (`fn-native-operator-run', called at
; host/native-operator-host.lisp:19, and host/native-config-host.lisp).  What
; `operator CONFIG show' prints, and what a mission writes, loads back as
; exactly the configuration it was rendered from.
(defthm fn-native-config-show-round-trip
  (implies (fn-native-config-show-wfp c)
           (equal (fn-native-config-load (fn-native-config-show-octets c))
                  (list :accepted c)))
  :hints (("Goal" :in-theory (e/d (fn-native-config-load)
                                  (fn-native-config-show-wfp fn-native-config-show-lines
                                   fn-ncfg-show-pairs fn-ncfg-normalize
                                   fn-ncfg-parse-lines fn-ncfg-lines fn-ncfg-show-join))
           :use (fn-ncfg-show-lines-parse fn-ncfg-normalize-of-show-pairs))))

;; -----------------------------------------------------------------------------
;; Every configuration the loader accepts is renderable.  The parser's values
;; are parsed-shaped (a boolean, a printable string, a natural); each field's
;; normalization keeps its bound; so the loaded configuration satisfies
;; `fn-native-config-show-wfp' and `show' needs no run-time check.

(encapsulate ()
  (local
   (defun fn-ncfg-parsed-valuep (v)
     (declare (xargs :guard t))
     (and (true-listp v) (equal (len v) 2)
          (cond ((equal (car v) :bool) (booleanp (cadr v)))
                ((equal (car v) :string)
                 (and (stringp (cadr v))
                      (fn-ncfg-printablep (fn-record-string-octets (cadr v)))))
                ((equal (car v) :nat) (natp (cadr v)))
                (t nil)))))

  (local
   (defun fn-ncfg-parsed-pairsp (pairs)
     (declare (xargs :guard t))
     (if (consp pairs)
         (and (fn-ncfg-parsed-valuep (fn-ncfg-third (car pairs)))
              (fn-ncfg-parsed-pairsp (cdr pairs)))
       t)))

  (local
   (defthm fn-ncfg-printable-octet-listp
     (implies (fn-ncfg-printablep xs)
              (fn-cbor-octet-listp (list-fix xs)))
     :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp)))))

  (local
   (defthm fn-ncfg-decimal-aux-natp-unless-bad
     (implies (not (equal (fn-ncfg-decimal-aux xs v) :bad))
              (natp (fn-ncfg-decimal-aux xs v)))
     :hints (("Goal" :in-theory (enable fn-ncfg-decimal-aux)))))

  (local
   (defthm fn-ncfg-decimal-natp
     (implies (not (equal (fn-ncfg-decimal xs) :bad))
              (natp (fn-ncfg-decimal xs)))
     :hints (("Goal" :in-theory (enable fn-ncfg-decimal)))))

  (local
   (defthm fn-ncfg-octets-chars-character-listp
     (character-listp (fn-record-octets-chars xs))
     :hints (("Goal" :in-theory (enable fn-record-octets-chars)))))

  (local
   (defthm fn-ncfg-string-octets-aux-of-octets-chars
     (implies (fn-cbor-octet-listp xs)
              (equal (fn-record-string-octets-aux (fn-record-octets-chars xs))
                     (list-fix xs)))
     :hints (("Goal" :in-theory (enable fn-record-octets-chars fn-record-string-octets-aux
                                        fn-cbor-octet-listp fn-cbor-octetp)))))

  (local
   (defthm fn-ncfg-string-octets-of-printable
     (implies (fn-ncfg-printablep xs)
              (equal (fn-record-string-octets (fn-record-octets-string (list-fix xs)))
                     (list-fix xs)))
     :hints (("Goal" :in-theory (enable fn-record-string-octets fn-record-octets-string)))))

  (local
   (defthm fn-ncfg-printablep-of-list-fix
     (equal (fn-ncfg-printablep (list-fix xs)) (fn-ncfg-printablep xs))))

  (local
   (defthm fn-ncfg-parse-value-parsed
     (implies (not (equal (fn-ncfg-parse-value xs) :bad))
              (fn-ncfg-parsed-valuep (fn-ncfg-parse-value xs)))
     :hints (("Goal" :in-theory (e/d (fn-ncfg-parse-value fn-ncfg-quoted-value)
                                     (fn-ncfg-decimal fn-ncfg-printable-octet-listp
                                      fn-record-octets-string fn-record-string-octets))
              :use ((:instance fn-ncfg-string-octets-of-printable
                     (xs (fn-ncfg-reverse (fn-ncfg-rest (fn-ncfg-reverse (cdr xs)))))))))))

  (local
   (defthm fn-ncfg-parse-lines-parsed
     (implies (and (fn-ncfg-parsed-pairsp pairs)
                   (not (equal (fn-ncfg-parse-lines lines current tables pairs) :bad)))
              (fn-ncfg-parsed-pairsp (fn-ncfg-parse-lines lines current tables pairs)))
     :hints (("Goal" :in-theory (e/d (fn-ncfg-parse-lines)
                                     (fn-ncfg-parse-value fn-ncfg-trim fn-ncfg-split-equals
                                      fn-ncfg-identp fn-ncfg-key-allowedp fn-ncfg-pair-seenp
                                      fn-ncfg-tablep fn-ncfg-table-seenp fn-record-octets-string
                                      fn-ncfg-reverse))))))

  (local
   (defthm fn-ncfg-value-parsed
     (implies (and (fn-ncfg-parsed-pairsp pairs) (fn-ncfg-value pairs table key))
              (fn-ncfg-parsed-valuep (fn-ncfg-value pairs table key)))
     :hints (("Goal" :in-theory (e/d (fn-ncfg-value) (fn-ncfg-parsed-valuep))))))

  (local
   (defthm fn-ncfg-string-value-textp
     (implies (and (or (null v) (fn-ncfg-parsed-valuep v))
                   (or (null d) (fn-ncfg-printablep (fn-record-string-octets d)))
                   (not (equal (fn-ncfg-string-value v d b r) :bad)))
              (fn-ncfg-show-opt-textp (fn-ncfg-string-value v d b r) b))
     :hints (("Goal" :in-theory (enable fn-ncfg-string-value fn-ncfg-show-opt-textp
                                        fn-ncfg-show-textp)))))

  (local
   (defthm fn-ncfg-string-value-present
     (implies (and (or (null v) (fn-ncfg-parsed-valuep v))
                   (not (equal (fn-ncfg-string-value v d b r) :bad))
                   (or r d v))
              (fn-ncfg-string-value v d b r))
     :hints (("Goal" :in-theory (enable fn-ncfg-string-value fn-ncfg-string-okp)))))

  (local
   (defthm fn-ncfg-bool-value-booleanp
     (implies (and (or (null v) (fn-ncfg-parsed-valuep v))
                   (booleanp d)
                   (not (equal (fn-ncfg-bool-value v d) :bad)))
              (booleanp (fn-ncfg-bool-value v d)))
     :hints (("Goal" :in-theory (enable fn-ncfg-bool-value)))))

  (local
   (defthm fn-ncfg-nat-value-natp
     (implies (and (or (null d) (and (natp d) (<= d c)))
                   (not (equal (fn-ncfg-nat-value v d c) :bad)))
              (fn-ncfg-show-opt-natp (fn-ncfg-nat-value v d c) c))
     :hints (("Goal" :in-theory (enable fn-ncfg-nat-value fn-ncfg-show-opt-natp)))))

  (local
   (defthm fn-ncfg-string-octets-aux-of-append
     (equal (fn-record-string-octets-aux (append a b))
            (append (fn-record-string-octets-aux a) (fn-record-string-octets-aux b)))
     :hints (("Goal" :in-theory (enable fn-record-string-octets-aux)))))

  (local
   (defthm fn-ncfg-printablep-of-append
     (equal (fn-ncfg-printablep (append a b))
            (and (fn-ncfg-printablep a) (fn-ncfg-printablep b)))))

  (local
   (defthm fn-ncfg-under-store-printable
     (implies (and (stringp store) (fn-ncfg-printablep (fn-record-string-octets store))
                   (stringp suffix) (fn-ncfg-printablep (fn-record-string-octets suffix)))
              (fn-ncfg-printablep (fn-record-string-octets (fn-ncfg-under-store store suffix))))
     :hints (("Goal" :in-theory (enable fn-ncfg-under-store fn-record-string-octets)))))

  (local
   (defthm fn-ncfg-string-value-textp-present
     (implies (and (or (null v) (fn-ncfg-parsed-valuep v))
                   (or (null d) (fn-ncfg-printablep (fn-record-string-octets d)))
                   (not (equal (fn-ncfg-string-value v d b r) :bad))
                   (or r d v))
              (fn-ncfg-show-textp (fn-ncfg-string-value v d b r) b))
     :hints (("Goal" :use (fn-ncfg-string-value-textp fn-ncfg-string-value-present)
              :in-theory (e/d (fn-ncfg-show-opt-textp)
                              (fn-ncfg-string-value-textp fn-ncfg-string-value-present
                               fn-ncfg-show-textp fn-ncfg-string-value))))))

  (local
   (defthm fn-ncfg-show-textp-printable
     (implies (fn-ncfg-show-textp x b)
              (and (stringp x) (fn-ncfg-printablep (fn-record-string-octets x))))
     :rule-classes :forward-chaining))

  (local
   (defthm fn-ncfg-nat-value-natp-present
     (implies (and (natp d) (<= d c)
                   (not (equal (fn-ncfg-nat-value v d c) :bad)))
              (fn-ncfg-show-natp (fn-ncfg-nat-value v d c) c))
     :hints (("Goal" :in-theory (enable fn-ncfg-nat-value fn-ncfg-show-natp)))))

  (local
   (defthm fn-ncfg-under-store-of-required-printable
     (implies (and (or (null v) (fn-ncfg-parsed-valuep v))
                   (not (equal (fn-ncfg-string-value v nil b t) :bad))
                   (stringp suffix)
                   (fn-ncfg-printablep (fn-record-string-octets suffix)))
              (fn-ncfg-printablep
               (fn-record-string-octets
                (fn-ncfg-under-store (fn-ncfg-string-value v nil b t) suffix))))
     :hints (("Goal" :use ((:instance fn-ncfg-string-value-textp-present (d nil) (r t))
                           (:instance fn-ncfg-under-store-printable
                                      (store (fn-ncfg-string-value v nil b t))))
              :in-theory (e/d (fn-ncfg-show-textp)
                              (fn-ncfg-string-value-textp-present fn-ncfg-string-value
                               fn-ncfg-under-store-printable
                               fn-ncfg-under-store fn-ncfg-parsed-valuep))))))

  (defthm fn-ncfg-show-wfp-of-make
    (implies (and (fn-ncfg-show-textp store *fn-ncfg-max-path*)
                  (fn-ncfg-show-textp host *fn-ncfg-max-text*)
                  (fn-native-config-listener-hostp host)
                  (fn-ncfg-show-natp port 65535)
                  (not (equal port 0))
                  (fn-ncfg-show-opt-textp tls-cert *fn-ncfg-max-path*)
                  (fn-ncfg-show-opt-textp tls-key *fn-ncfg-max-path*)
                  (fn-ncfg-pairedp tls-cert tls-key)
                  (booleanp auth-required)
                  (booleanp auth-protected)
                  (fn-ncfg-show-textp auth-path *fn-ncfg-max-path*)
                  (booleanp posting-enabled)
                  (fn-ncfg-show-opt-textp agent *fn-ncfg-max-text*)
                  (fn-ncfg-show-opt-textp anchor *fn-ncfg-max-server*)
                  (fn-ncfg-show-opt-textp log *fn-ncfg-max-path*)
                  (fn-ncfg-show-textp control *fn-ncfg-max-path*)
                  (fn-ncfg-show-opt-textp acl2-path *fn-ncfg-max-path*)
                  (fn-ncfg-show-opt-natp acl2-slots 65535)
                  (fn-ncfg-show-opt-textp alert-command *fn-ncfg-max-path*)
                  (fn-ncfg-optional-absolutep alert-command)
                  (fn-ncfg-show-natp headroom 100)
                  (fn-ncfg-show-natp refusal-rate *fn-ncfg-max-u64*)
                  (fn-ncfg-show-natp cooldown *fn-ncfg-max-u64*)
                  (fn-ncfg-show-opt-textp mission *fn-ncfg-max-text*)
                  (fn-ncfg-optional-memberp mission *fn-ncfg-mission-names*)
                  (fn-ncfg-show-opt-textp unit *fn-ncfg-max-text*)
                  (fn-ncfg-show-textp scope *fn-ncfg-max-text*)
                  (fn-ncfg-memberp scope *fn-ncfg-ops-scopes*)
                  (fn-ncfg-show-natp keep-releases *fn-ncfg-max-u64*)
                  (not (equal keep-releases 0))
                  (fn-ncfg-show-natp log-max-bytes *fn-ncfg-max-u64*)
                  (not (equal log-max-bytes 0))
                  (fn-ncfg-show-natp log-keep *fn-ncfg-max-u64*)
                  (fn-ncfg-show-opt-textp memory-max *fn-ncfg-max-text*)
                  (fn-ncfg-show-opt-natp tls-port 65535)
                  (fn-ncfg-tls-port-okp tls-port port tls-cert))
             (fn-native-config-show-wfp
              (fn-native-config-make store host port tls-cert tls-key auth-required
                                     auth-protected auth-path posting-enabled
                                     agent anchor log control acl2-path acl2-slots
                                     alert-command headroom refusal-rate cooldown
                                     mission unit scope keep-releases log-max-bytes
                                     log-keep memory-max tls-port)))
    :hints (("Goal" :in-theory (e/d (fn-native-config-show-wfp fn-ncfg-show-shapep)
                                    (fn-ncfg-show-textp fn-ncfg-show-natp fn-ncfg-show-opt-textp
                                     fn-ncfg-show-opt-natp fn-native-config-listener-hostp
                                     fn-ncfg-pairedp fn-ncfg-tls-port-okp fn-ncfg-optional-absolutep
                                     fn-ncfg-optional-memberp fn-ncfg-memberp)))))

  (local
   (defthm fn-ncfg-normalize-renderable
     (implies (and (fn-ncfg-parsed-pairsp pairs)
                   (not (equal (fn-ncfg-normalize pairs) :bad)))
              (fn-native-config-show-wfp (fn-ncfg-normalize pairs)))
     :hints (("Goal" :in-theory (e/d (fn-ncfg-normalize)
                                     (fn-native-config-show-wfp fn-native-config-make
                                      fn-ncfg-string-value fn-ncfg-bool-value fn-ncfg-nat-value
                                      fn-ncfg-show-textp fn-ncfg-show-natp fn-ncfg-show-opt-textp
                                      fn-ncfg-show-opt-natp fn-ncfg-parsed-valuep
                                      fn-ncfg-parsed-pairsp fn-ncfg-under-store
                                      fn-native-config-listener-hostp fn-ncfg-pairedp fn-ncfg-tls-port-okp
                                      fn-ncfg-optional-absolutep fn-ncfg-optional-memberp
                                      fn-ncfg-memberp fn-record-string-octets fn-ncfg-printablep))))))

  ; KEYSTONE (PRF-094).  The subject is `fn-native-config-load', which
  ; `fn-native-operator-run' (host/native-operator-host.lisp:19) reads fn.toml
  ; through before `show' renders it: what the loader accepts, show renders.
  (defthm fn-native-config-load-renderable
    (implies (equal (car (fn-native-config-load octets)) :accepted)
             (fn-native-config-show-wfp (cadr (fn-native-config-load octets))))
    :hints (("Goal" :in-theory (e/d (fn-native-config-load)
                                    (fn-native-config-show-wfp fn-ncfg-normalize
                                     fn-ncfg-parse-lines fn-ncfg-lines fn-ncfg-ascii-octetsp
                                     fn-ncfg-parsed-pairsp))))))

; With the round trip: every loaded configuration's rendering loads back as
; itself.
(defthm fn-native-config-loaded-show-round-trip
  (implies (equal (car (fn-native-config-load octets)) :accepted)
           (equal (fn-native-config-load
                   (fn-native-config-show-octets (cadr (fn-native-config-load octets))))
                  (list :accepted (cadr (fn-native-config-load octets)))))
  :hints (("Goal" :use (fn-native-config-load-renderable
                        (:instance fn-native-config-show-round-trip
                                   (c (cadr (fn-native-config-load octets)))))
           :in-theory (disable fn-native-config-load-renderable
                               fn-native-config-show-round-trip
                               fn-native-config-show-wfp fn-native-config-show-octets))))

; -----------------------------------------------------------------------------
; `operator CONFIG show [TABLE KEY]': the whole rendering, or one key's value
; as a word (a string unquoted, a natural in decimal, true or false).

(defun fn-ncfg-show-word (pv)
  (declare (xargs :guard t))
  (if (equal (fn-ncfg-first pv) :string)
      (fn-record-string-octets (fn-ncfg-second pv))
    (fn-ncfg-show-value pv)))

;   (:shown OCTETS)          what `show' prints
;   (:refused :unset | :unknown-key)
; C is a loaded configuration: fn-native-config-load-renderable.
(defun fn-native-config-show (c table key)
  (declare (xargs :guard t))
  (cond ((and (null table) (null key)) (list :shown (fn-native-config-show-octets c)))
        ((not (and (stringp table) (stringp key) (fn-ncfg-key-allowedp table key)))
         (list :refused :unknown-key))
        (t (let ((pv (fn-ncfg-value (fn-ncfg-show-pairs c) table key)))
             (if pv
                 (list :shown (fn-ncfg-show-word pv))
               (list :refused :unset))))))

; -----------------------------------------------------------------------------
; Missions (PKT-097, spike deferral 3).  A mission is a named fn.toml: the
; configuration below, written as its rendering, plus the store profile
; books/native-mission.lisp gives it.  The figures are the spike's:
;   (posting auth-required protected-only headroom-min-percent
;    refusal-rate-per-minute)
(defun fn-native-mission-row (name)
  (declare (xargs :guard t))
  (cond ((equal name "small-community") '(t t t 10 30))
        ((equal name "relay") '(nil t t 20 120))
        ((equal name "archive") '(nil nil nil 25 30))
        (t nil)))

(defun fn-ncfg-join-path (node suffix)
  (declare (xargs :guard t))
  (if (and (stringp node) (stringp suffix)) (concatenate 'string node suffix) ""))

; The node directory: absolute, printable, no trailing slash, and short
; enough that every path under it is within the path bound.
(defconst *fn-ncfg-max-node-path* 480)

(defun fn-native-mission-nodep (node)
  (declare (xargs :guard t))
  (and (fn-ncfg-show-textp node *fn-ncfg-max-node-path*)
       (fn-ncfg-absolutep node)
       (not (equal (fn-ncfg-first (fn-ncfg-reverse (fn-record-string-octets node))) 47))))

(defun fn-native-mission-config (name node host port)
  (declare (xargs :guard t))
  (let ((row (fn-native-mission-row name)))
    (fn-native-config-make
     (fn-ncfg-join-path node "/store") host port
     (fn-ncfg-join-path node "/tls/cert.pem") (fn-ncfg-join-path node "/tls/key.pem")
     (fn-ncfg-second row) (fn-ncfg-third row)
     (fn-ncfg-join-path node "/store/auth.toml")
     (fn-ncfg-first row) nil nil
     (fn-ncfg-join-path node "/log/fn.log")
     (fn-ncfg-join-path node "/store/control.sock") nil nil
     nil (fn-ncfg-nth 3 row) (fn-ncfg-nth 4 row) *fn-ncfg-default-cooldown-seconds*
     name nil *fn-ncfg-default-ops-scope* *fn-ncfg-default-keep-releases*
     *fn-ncfg-default-log-max-bytes* *fn-ncfg-default-log-keep* nil nil)))

; The directories the operator's host creates beside fn.toml (the store is
; created by `init').
(defun fn-native-mission-directories (node)
  (declare (xargs :guard t))
  (list (fn-ncfg-join-path node "/log") (fn-ncfg-join-path node "/tls")))

;   (:accepted CONFIG OCTETS)   write OCTETS as NODE/fn.toml
;   (:refused REASON)
(defun fn-native-mission-plan (name node host port)
  (declare (xargs :guard t))
  (cond ((null (fn-native-mission-row name)) (list :refused :unknown-mission))
        ((not (fn-native-mission-nodep node)) (list :refused :node-path))
        (t (let ((config (fn-native-mission-config name node host port)))
             (if (fn-native-config-show-wfp config)
                 (list :accepted config (fn-native-config-show-octets config))
               (list :refused :listener))))))

; What a mission writes is read back, by the loader every verb uses, as the
; mission's configuration, naming the mission.
(defthm fn-native-mission-plan-loads-back
  (let ((plan (fn-native-mission-plan name node host port)))
    (implies (equal (car plan) :accepted)
             (and (equal (fn-native-config-load (caddr plan))
                         (list :accepted (cadr plan)))
                  (equal (fn-native-config-ops-mission (cadr plan)) name))))
  :hints (("Goal" :in-theory (disable fn-native-config-show-wfp
                                      fn-native-config-show-octets
                                      fn-native-config-load))))

; Every consumer reasons about these through the theorems above, never by
; unfolding the rendering (books/native-operator.lisp's command grammar
; mentions `fn-native-config-show' in one branch).
(in-theory (disable fn-native-config-show fn-native-config-show-octets
                    fn-native-config-show-wfp fn-native-config-show-lines
                    fn-ncfg-show-pairs fn-native-mission-plan
                    fn-native-mission-config))
